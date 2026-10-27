
#include <algorithm>
#include <climits>
#include <cstring>
#include <map>
#include <vector>

#include "deps.h"
#include "issue.h"
#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

Word make_nop() { return Word{0x0000000000007918ull, 0x000fc00000000000ull}; }
Word make_bra() { return Word{0x0000000000007947ull, 0x000fc00003800000ull}; }

namespace {

const int MAX_WAIT_VALUE = 15;
const int CROSS_BLOCK_MIN_WAIT = 1;
const int JT_WAIT1_INST_MIN = 256;

enum Pattern { P_SELF_LOOP, P_SINGLE_ENTRY_LOOP, P_SIMPLE_IF, P_GENERIC };

struct XDep {
    int to;
    uint8_t type;
    uint16_t mask;
};

int val_of(const Inst &i, const char *name, int dflt) {
    int v = val_index(i.cls, name);
    return v < 0 ? dflt : (int)get(i, v);
}

bool jt_unanimous_all(const SInst &s) {
    const int BRA_COND_U = 1;
    static const int CALL = op_id("CALL");
    return s.in.op == CALL || val_of(s.in, "cond", -1) == BRA_COND_U;
}

void set_word(SInst &s, const Word &w, int stype) {
    SInst t;
    build_sinst(w, stype, false, &t);
    s.w = t.w;
    s.in = t.in;
    s.ok = t.ok;
    s.nregs = t.nregs;
    memcpy(s.regs, t.regs, sizeof s.regs);
    s.pred = t.pred;
    s.pred_cls = t.pred_cls;
    s.pred_cond = t.pred_cond;
}

bool keep_at_block_end(const SInst &s) { return ori_kind(s).flow || s.sc.sop == SOP_SM70_BREAK; }

struct Owo {
    SbProg &p;
    int stype;
    SbStats *stats;

    std::vector<int> liveWait, beyond;

    std::map<int, std::vector<XDep>> deps;
    std::vector<int> regTab;
    std::vector<int> touched;

    Owo(SbProg &p_, int t, SbStats *s) : p(p_), stype(t), stats(s) {
        liveWait.assign(p.blocks.size(), INT_MIN);
        beyond.assign(p.blocks.size(), INT_MIN);
        regTab.assign(16 * 1024, -1);
    }
    SInst &S(int k) { return p.nodes[k].s; }
    int last_inst(int b) {
        int k = p.last_node(b);
        return p.nodes[k].kind == SBN_INST ? k : -1;
    }
    int block_wait(int b) {
        int w = 0;
        for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next) w += S(k).waitLatency;
        return w;
    }

    bool self_loop(int b) const {
        const SbBlock &x = p.blocks[b];
        return x.loopHdrIdx == x.loopRegion && x.loopHdrIdx == x.index;
    }
    bool tail_of_single_entry_loop(int b) const {
        if (!p.hasBackEdge) return false;
        const SbBlock &x = p.blocks[b];
        for (int sv : x.succ) {
            const SbBlock &s = p.blocks[sv];
            if (s.index > x.index) continue;
            if (x.index == x.loopRegion && s.index == x.loopHdrIdx && s.predCount == 2 && x.succ.size() == 2 &&
                loop_single_entry(p, x.loopHdrIdx, x.loopRegion))
                return true;
        }
        return false;
    }

    bool if_single_succ(int b, bool backward) const {
        const SbBlock &x = p.blocks[b];
        const std::vector<int> &one = backward ? x.succ : x.pred;
        if (one.size() != 1) return false;
        const SbBlock &m = p.blocks[one[0]];
        const std::vector<int> &two = backward ? m.pred : m.succ;
        if (two.size() != 2) return false;
        int b1 = two[0], b2 = two[1];
        const std::vector<int> &l1 = backward ? p.blocks[b1].pred : p.blocks[b1].succ;
        const std::vector<int> &l2 = backward ? p.blocks[b2].pred : p.blocks[b2].succ;
        if ((l1.size() == 1 && l1[0] == b2) || (l2.size() == 1 && l2[0] == b1)) return true;
        return l1.size() == 1 && l2.size() == 1 && l1[0] == l2[0];
    }
    bool func_exit(int b, const SInst &last) const {
        if (last.sc.sop == SOP_SM70_RET || last.sc.sop == SOP_SM70_EXIT) return true;
        bool funcEnd = b == p.funcs[p.blocks[b].func].last;
        bool jmp = sb_is_jmp(last) && !sb_is_cond_flow(last);
        return funcEnd && !jmp && !sb_is_jmx(last);
    }

    int &slot(int cls, int no) {
        int k = cls * 1024 + (no & 1023);
        if (regTab[k] < 0) touched.push_back(k);
        return regTab[k];
    }
    void reset_regs() {
        for (int k : touched) regTab[k] = -1;
        touched.clear();
    }

    void add_dep(int bp, int from, int to, int type, int cls) {
        if (p.nodes[from].block != bp) return;
        std::vector<XDep> &l = deps[from];
        uint16_t m = (uint16_t)(1u << cls);
        for (XDep &e : l)
            if (e.to == to && e.type == type) {
                e.mask |= m;
                return;
            }
        l.push_back(XDep{to, (uint8_t)type, m});
    }

    void forward(int bp, int b) {
        for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            const SInst &s = S(k);
            uint8_t ord[SINST_MAX_REGS];
            int nr = rev_regs(s, ord);
            for (int q = 0; q < nr; q++) {
                const SReg &r = s.regs[ord[q]];
                if (r.cls > RC_ACTIVEM) continue;
                int &d = slot(r.cls, r.no);
                if (r.def) {
                    if (d >= 0 && d != k) add_dep(bp, d, k, DEP_OUTPUT, r.cls);
                    d = k;
                } else if (d >= 0 && d != k) {
                    add_dep(bp, d, k, DEP_FLOW, r.cls);
                }
            }
        }
    }

    void backward(int bp, int b) {
        for (int k = p.last_node(b); k != p.blocks[b].lab; k = p.nodes[k].prev) {
            const SInst &s = S(k);
            uint8_t ord[SINST_MAX_REGS];
            int nr = rev_regs(s, ord);
            for (int q = 0; q < nr; q++) {
                const SReg &r = s.regs[ord[q]];
                if (r.cls > RC_R) continue;
                int &d = slot(r.cls, r.no);
                if (r.def) d = k;
                else if (d >= 0 && d != k) add_dep(bp, k, d, DEP_ANTI, r.cls);
            }
        }
    }

    void add_across(int bp, int succ) {
        reset_regs();
        forward(bp, bp);
        forward(bp, succ);
        reset_regs();
        backward(bp, succ);
        backward(bp, bp);
        reset_regs();
    }

    int outstanding(int bp, int succ, int blockWait, Pattern pat) {
        int out = 0;
        for (int k = p.first_inst(bp); k != p.blocks[bp].eb; k = p.nodes[k].next) {
            const SInst &s = S(k);
            if (s.flags & GF_DECOUPLED) continue;
            auto it = deps.find(k);
            if (it == deps.end()) continue;
            for (const XDep &e : it->second) {
                int db = p.nodes[e.to].block;
                if (db != succ) continue;
                const SInst &d = S(e.to);
                if (pat == P_SELF_LOOP && bp == db && d.instOrder >= s.instOrder) continue;
                if (pat != P_SELF_LOOP && bp == db) continue;
                int deep = blockWait + d.waitTa - s.waitTa;
                int hz = dep_latency(e.type, s, d, e.mask, 0, true);
                if (deep <= hz) out = std::max(out, hz - deep);
            }
        }
        return out;
    }

    int new_wait(int last) {
        const SInst &ls = S(last);
        int nw = I2I_ISSUE_RATE;
        if (!(ls.flags & GF_COUPLED) && (ls.wrSB >= 0 || ls.rdSB >= 0)) nw = std::max(nw, SCOREBOARD_RAW_DELAY);
        const int maxPipeWait = max_res_busy();
        for (int k = last; p.nodes[k].kind != SBN_LAB; k = p.nodes[k].prev) {
            const SInst &ps = S(k);
            int waitToLast = ls.waitTa - ps.waitTa;
            OriKind ok = ori_kind(ps);
            bool defer = ps.sc.sop == SOP_SM70_BAR && bar_defer_blocking(ps);
            nw = std::max(nw, (defer ? ok.minNextStrict : ok.minNext) - waitToLast);
            if (waitToLast + nw >= maxPipeWait) break;
            nw = std::max(nw, res_busy(ps) - waitToLast);
        }
        return nw;
    }
    int add_nop(int at, int wait) {
        SbNode n;
        n.kind = SBN_INST;
        build_sinst(make_nop(), stype, false, &n.s);
        n.s.number = -1;
        n.s.rdSB = n.s.wrSB = -1;
        n.s.reqSB = 0;
        n.s.waitLatency = wait;
        n.s.endGroup = 1;
        return p.insert_after(at, n);
    }

    void insert_wait_before(int k, int cycles) {
        int at = p.nodes[k].prev;
        for (int i = cycles / MAX_WAIT_VALUE; i > 0; i--) at = add_nop(at, MAX_WAIT_VALUE);
        if (cycles % MAX_WAIT_VALUE) add_nop(at, cycles % MAX_WAIT_VALUE);
    }

    void renumber(int b) {
        int t = 0, order = 0;
        for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            S(k).instOrder = order++;
            S(k).waitTa = t;
            t += S(k).waitLatency;
        }
    }

    void cross_block(int bp, Pattern pat) {
        int last = last_inst(bp);
        SInst &ls = S(last);
        const int oldW = ls.waitLatency;
        bool loop = pat == P_SELF_LOOP || pat == P_SINGLE_ENTRY_LOOP;
        int newW = new_wait(last);
        if (liveWait[bp] != INT_MIN) newW = std::max(newW, oldW + liveWait[bp]);
        if (oldW < CROSS_BLOCK_MIN_WAIT || oldW <= newW) return;
        const int delta = oldW - newW;
        int oldBlock = ls.waitTa + oldW;
        int newBlock = oldBlock - delta;
        if (pat == P_SELF_LOOP && oldW >= newBlock - oldW) return;
        deps.clear();
        if (block_wait(bp) != oldBlock) stats->assertHits++;
        int maxOut = 0, backOut = 0;
        const std::vector<int> succ = p.blocks[bp].succ;
        for (int sv : succ) {
            add_across(bp, sv);
            int outIn = outstanding(bp, sv, newBlock, pat);
            int b2 = delta - block_wait(sv);
            beyond[sv] = b2;
            int total = std::max(outIn, b2);
            if (loop && p.blocks[bp].loopHdrIdx == p.blocks[sv].index) backOut = total;
            maxOut = std::max(maxOut, total);
        }
        int out = loop ? backOut : maxOut;
        newW += out;
        if (newW >= oldW) return;
        ls.waitLatency = newW;
        if (stats->regroupLowered) ls.endGroup = use_group_for(ls, newW);
        p.blocks[bp].maxHazard = false;
        if (stats->beyondFromLowered)
            for (int sv : succ) beyond[sv] = oldW - newW - block_wait(sv);
        for (int sv : succ) {
            liveWait[sv] = std::max(liveWait[sv], beyond[sv]);
            if (loop && p.blocks[bp].loopHdrIdx != p.blocks[sv].index) {
                int sink = maxOut - out;
                if (sink > 0) {
                    insert_wait_before(p.first_inst(sv), sink);
                    renumber(sv);
                }
            }
        }
    }

    void cross_blocks() {
        bool any = false;
        for (const SbBlock &b : p.blocks) any |= b.maxHazard;
        if (!any) return;
        for (int bp = 0; bp < (int)p.blocks.size(); bp++) {
            if (!p.blocks[bp].maxHazard) continue;
            int last = last_inst(bp);
            if (last < 0) continue;
            const SInst &ls = S(last);
            if (sb_is_call(ls) || func_exit(bp, ls)) continue;
            bool condJt = sb_is_cond_flow(ls);
            if (self_loop(bp) && condJt) cross_block(bp, P_SELF_LOOP);
            else if (tail_of_single_entry_loop(bp) && condJt) cross_block(bp, P_SINGLE_ENTRY_LOOP);
            else if (if_single_succ(bp, true) && if_single_succ(bp, false)) cross_block(bp, P_SIMPLE_IF);
            else cross_block(bp, P_GENERIC);
        }
    }

    int insert_block(int b) {
        int nb = p.insert_block_after(b);
        liveWait.insert(liveWait.begin() + nb, INT_MIN);
        beyond.insert(beyond.begin() + nb, INT_MIN);
        return nb;
    }

    void jt_speculation(int b) {
        int jt = last_inst(b);
        int loopB = p.blocks[b].target;
        if (loopB < 0 || p.blocks[b].loopHdrIdx != p.blocks[loopB].index) return;
        int count = 0;
        for (int k = p.blocks[loopB].lab; k != jt && k >= 0 && count < JT_WAIT1_INST_MIN; k = p.nodes[k].next) count++;
        if (count < JT_WAIT1_INST_MIN) return;
        if (b + 1 >= (int)p.blocks.size()) return;
        SInst &js = S(jt);
        const int oldW = js.waitLatency, newW = 1;
        const int delta = oldW - newW;
        if (delta <= 0) stats->assertHits++;
        int oldBlock = js.waitTa + oldW;
        int newBlock = oldBlock - delta;
        int ft = b + 1;
        Pattern pat = self_loop(b) ? P_SELF_LOOP : P_GENERIC;
        deps.clear();
        add_across(b, ft);
        int out = outstanding(b, ft, newBlock, pat);

        int oldLive = liveWait[b], newLive = INT_MIN;
        if (oldLive != INT_MIN && oldLive + newW > 0) newLive = oldLive + (oldBlock - newBlock);
        int live = std::max(oldLive, newLive);
        liveWait[b] = live;
        out = std::max(out, live);
        if (out > 0) insert_wait_before(p.first_inst(ft), out);
        int nb = insert_block(b);
        SbNode n;
        n.kind = SBN_INST;
        build_sinst(make_bra(), stype, false, &n.s);
        n.s.number = -1;
        n.s.rdSB = n.s.wrSB = -1;
        n.s.reqSB = 0;
        n.s.waitLatency = std::max(delta, ori_kind(S(jt)).minNext);
        n.s.endGroup = S(jt).endGroup;
        p.insert_after(p.blocks[nb].lab, n);
        p.blocks[nb].target = loopB;
        SInst &j2 = S(jt);
        invert_branch(j2, stype);
        p.blocks[b].target = nb + 1;
        j2.waitLatency = newW;
        j2.endGroup = 0;
        analyze_cfg(p);
    }

    void run() {
        cross_blocks();
        for (int b = 0; b < (int)p.blocks.size(); b++) {
            int last = last_inst(b);
            if (last < 0) continue;
            const SInst &ls = S(last);
            if (sb_is_cond_flow(ls) && jt_unanimous_all(ls)) jt_speculation(b);
        }
    }
};

}

void invert_branch(SInst &s, int shader_type) {
    Inst in = s.in;
    auto flip = [&](const char *name) {
        int v = val_index(in.cls, name);
        if (v >= 0) set(in, v, get(in, v) ^ 1);
    };
    if (val_of(in, "Pg", 7) != 7) flip("Pg@not");
    else if (val_of(in, "UPq", 7) != 7) flip("UPq@not");
    else flip("Pp@not");
    set_word(s, in.w, shader_type);
}

void optimize_wait_opex(SbProg &p, int shader_type, SbStats *stats) {
    SbStats local;
    Owo o(p, shader_type, stats ? stats : &local);
    o.run();
}

void legalize_wait_opex(SbProg &p, int shader_type, SbStats *stats) {
    SbStats local;
    if (!stats) stats = &local;
    Owo o(p, shader_type, stats);
    auto S = [&](int k) -> SInst & { return p.nodes[k].s; };
    bool deferBlocking = false;
    for (const SbNode &n : p.nodes)
        if (n.kind == SBN_INST && n.s.sc.sop == SOP_SM70_BAR && bar_defer_blocking(n.s)) deferBlocking = true;
    if (deferBlocking) {
        for (int b = 0; b < (int)p.blocks.size(); b++) {
            int bar = -1;
            for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next) {
                const SInst &s = S(k);
                if (s.sc.sop == SOP_SM70_BAR && bar_defer_blocking(s)) bar = k;
                else if (bar >= 0 && barrier_sync_event(s)) bar = -1;
            }
            if (bar < 0) continue;
            SInst &last = S(p.last_node(b));
            int pad = S(bar).waitTa + ori_kind(S(bar)).minNextStrict - (last.waitTa + last.waitLatency);
            if (pad > 0) {
                last.waitLatency += pad;
            }
        }
    }

    for (int b = 0; b < (int)p.blocks.size(); b++) {
        for (int k = p.first_inst(b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            SInst &s = S(k);
            if (s.waitLatency <= MAX_WAIT_VALUE) continue;
            int delta = s.waitLatency - MAX_WAIT_VALUE;
            s.waitLatency = MAX_WAIT_VALUE;
            o.insert_wait_before(keep_at_block_end(s) ? k : p.nodes[k].next, delta);
        }
    }
}

}
}
}
