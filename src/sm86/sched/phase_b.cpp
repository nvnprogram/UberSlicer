
#include <climits>
#include <cstring>
#include <set>

#include "issue.h"
#include "phase_a.h"
#include "phase_b.h"

namespace ub {
namespace sm86 {
namespace sched {

namespace {

void forced_block(SInst *in, int n, const BlockDeps &deps, PaMachine &m) {
    std::vector<int> ref = deps.ref;
    m.set_deps(&deps);
    m.init_block(in, n);
    std::vector<int> avail;
    for (int i = 0; i < n; i++)
        if (ref[i] == 0) {
            avail.insert(avail.begin(), i);
            m.avail_added(i, ref);
        }
    int next = 0;
    while (!avail.empty() && next < n) {
        int k = -1;
        for (size_t j = 0; j < avail.size(); j++) {
            m.ready_time(avail[j]);
            if (avail[j] == next) k = (int)j;
        }
        if (k < 0) break;
        int best = next++;
        m.process_pick(best);
        if (in[best].ta > m.time()) m.set_time(in[best].ta);
        avail.erase(avail.begin() + k);
        for (const DepEdge &e : deps.out[best]) {
            int t = m.time() + m.dep_latency(best, e);
            if (t > in[e.to].ta) in[e.to].ta = t;
            m.dep_released(best, e);
            if (--ref[e.to] == 0) {
                avail.insert(avail.begin(), e.to);
                m.avail_added(e.to, ref);
            }
        }
        m.avail_removed(best, ref);
        m.schedule(best);
    }
    for (int i = next; i < n; i++) m.finish_inst(i);
    m.finish_block();
}

long long rel_bytes(const SInst &s) {
    if (!s.ok && s.in.cls < 0) return 1;
    Operand o[MAX_OPNDS];
    int no = operands(s.in, o, MAX_OPNDS);
    for (int j = 0; j < no; j++)
        if (o[j].kind == O_REL) return o[j].imm;
    return 1;
}

bool is_named(const SInst &s, const char *name) { return s.in.cls >= 0 && !strcmp(op_name(s.in.op), name); }

long long value(const SInst &s, const char *name) {
    if (s.in.cls < 0) return -1;
    int v = val_index(s.in.cls, name);
    return v >= 0 ? get(s.in, v) : -1;
}

}

std::vector<int> jump_table(const SInst *code, int at, const std::string &consts, const std::function<bool(int)> &ok) {
    const SInst &s = code[at];
    long long imm = (long long)(int32_t)(uint32_t)(s.in.w.lo >> 32);
    long long next = (at + 1) * 16ll;
    auto entry = [&](size_t off) {
        uint32_t v;
        memcpy(&v, consts.data() + off, 4);
        long long a = (long long)(int32_t)v + imm + next;
        return v != 0 && a >= 0 && a % 16 == 0 && a / 16 <= INT32_MAX && ok((int)(a / 16)) ? (int)(a / 16) : -1;
    };
    long long tableOff = -1, count = -1;
    bool uniform = is_named(s, "BRXU");
    long long ra = value(s, uniform ? "URa" : "Ra");
    for (int j = at - 1; j >= 0 && tableOff < 0; j--) {
        const SInst &l = code[j];
        if (value(l, uniform ? "URd" : "Rd") != ra) continue;
        if (!(uniform ? is_named(l, "ULDC") : l.sc.sop == SOP_SM70_LDC)) break;
        tableOff = value(l, uniform ? "Sa_offset" : "Ra_offset");

        long long index = value(l, uniform ? "URa" : "Ra");
        for (int k = j - 1; k >= 0 && count < 0; k--) {
            const SInst &c = code[k];
            if (value(c, uniform ? "URd" : "Rd") != index) continue;
            const char *op = c.in.cls >= 0 ? op_name(c.in.op) : "";
            bool scale = !strcmp(op, "SHF") || !strcmp(op, "USHF") ||
                         ((!strcmp(op, "IMAD") || !strcmp(op, "UIMAD")) && value(c, "Sb") >= 0 &&
                          value(c, uniform ? "URc" : "Rc") == (uniform ? 63 : 255));
            if (scale) {
                index = value(c, uniform ? "URa" : "Ra");
                continue;
            }
            bool clamp = !strcmp(op, "IMNMX") || !strcmp(op, "UIMNMX") || !strcmp(op, "SEL") || !strcmp(op, "USEL");
            if (clamp && value(c, "Sb") >= 0) count = value(c, "Sb") + 1;
            break;
        }
    }
    std::vector<int> best, cur;
    if (tableOff >= 0 && tableOff % 4 == 0)
        for (size_t off = (size_t)tableOff; off + 4 <= consts.size(); off += 4) {
            if (count >= 0 && (long long)best.size() >= count) break;
            int t = entry(off);
            if (t < 0) break;
            best.push_back(t);
        }
    if (best.empty())
        for (size_t off = 0; off + 4 <= consts.size(); off += 4) {
            int t = entry(off);
            if (t >= 0) {
                cur.push_back(t);
                if (cur.size() > best.size()) best = cur;
            } else {
                cur.clear();
            }
        }
    return best;
}

void pa_times(SbProg &p, DepsCtx ctx) {
    std::vector<SInst> flat;
    std::vector<int> node, start;
    for (size_t b = 0; b < p.blocks.size(); b++) {
        start.push_back((int)flat.size());
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            flat.push_back(p.nodes[k].s);
            node.push_back(k);
        }
    }
    start.push_back((int)flat.size());
    for (SInst &s : flat) s.ta = s.depbarCommit = 0;
    IssueMachine m;
    const int total = (int)flat.size();
    for (size_t b = 0; b + 1 < start.size(); b++) {
        int s0 = start[b], n = start[b + 1] - s0;
        if (n == 0) continue;
        SInst *in = flat.data() + s0;
        ctx.after = in + n;
        ctx.nafter = total - s0 - n;
        BlockDeps bd;
        calc_deps(in, n, ctx, &bd);
        ur_nc_step(in, n, ctx);
        forced_block(in, n, bd, m);
    }
    for (int j = 0; j < total; j++) {
        p.nodes[node[j]].s.ta = flat[j].ta;
        p.nodes[node[j]].s.depbarCommit = flat[j].depbarCommit;
    }
}

void phase_b_prog(SbProg &p, const DepsCtx &ctx, int shader_type, SbStats *stats) {
    assign_scoreboards(p, shader_type, stats);
    opex_replay(p, ctx, stats);
    optimize_wait_opex(p, shader_type, stats);
    legalize_wait_opex(p, shader_type, stats);
    warpsync_after_break_regions(p, shader_type);
    add_padding(p, shader_type);
    set_opex(p, shader_type);
    assign_reuse(p);
    relocate(p);
    write_control(p);
}

bool sb_from_words(const Word *in, int n, const Cfg &cfg, int shader_type, SbProg *out) {
    SbProg &p = *out;
    p = SbProg();
    int nb = (int)cfg.starts.size();
    if (n <= 0 || nb == 0 || cfg.starts[0] != 0 || cfg.funcs.empty() || cfg.funcs[0] != 0) return false;
    for (size_t f = 0; f < cfg.funcs.size(); f++) {
        SbFunc fn;
        fn.first = cfg.funcs[f];
        fn.last = f + 1 < cfg.funcs.size() ? cfg.funcs[f + 1] - 1 : nb - 1;
        fn.main = f == 0;
        p.funcs.push_back(fn);
    }
    std::vector<int> funcOf(nb, 0), nodeOf(n, -1);
    for (size_t f = 0; f < p.funcs.size(); f++)
        for (int b = p.funcs[f].first; b <= p.funcs[f].last && b < nb; b++) funcOf[b] = (int)f;
    for (int b = 0; b < nb; b++) {
        int bi = p.add_block(funcOf[b]);
        int end = b + 1 < nb ? cfg.starts[b + 1] : n;
        for (int k = cfg.starts[b]; k < end; k++) {
            SInst s;
            build_sinst(in[k], shader_type, false, &s);
            s.number = k;
            nodeOf[k] = p.append_inst(bi, s);
            if (k < (int)cfg.rel.size()) p.nodes[nodeOf[k]].relBlock = cfg.rel[k];
        }
    }
    for (int b = 0; b < nb; b++) {
        int last = p.last_node(b);
        if (last == p.blocks[b].lab) continue;
        const SInst &s = p.nodes[last].s;
        int t = p.nodes[last].relBlock;
        if (b < (int)cfg.jmx.size() && sb_is_jmx(s)) p.blocks[b].jmxTargets = cfg.jmx[b];
        else if (t >= 0 && t < nb && sb_is_jmp(s)) p.blocks[b].target = t;
        else if (t >= 0 && t < nb && sb_is_call(s)) p.blocks[b].callee = funcOf[t];
    }
    for (size_t k = 0; k < p.nodes.size(); k++) {
        SbNode &x = p.nodes[k];
        if (x.kind == SBN_INST && x.s.sc.sop == SOP_SM70_NOP)
            nop_stand_in(&x.s, p.last_node(x.block) == (int)k, shader_type);
    }
    analyze_cfg(p);
    sb_ldc_latency(p);
    return true;
}

int phase_b(const Word *in, int n, const Cfg &cfg, int shader_type, std::vector<Word> &out, std::vector<int> &map,
            SbStats *stats) {
    SbProg p;
    if (!sb_from_words(in, n, cfg, shader_type, &p)) return -1;
    DepsCtx ctx;
    ctx.compute = cfg.compute;
    ctx.shared_isb = cfg.shared_isb;
    for (const SbNode &x : p.nodes)
        if (x.kind == SBN_INST && x.s.sc.sop == SOP_SM70_KILL) ctx.has_kil = true;
    pa_times(p, ctx);
    SbStats local;
    phase_b_prog(p, ctx, shader_type, stats ? stats : &local);
    out.clear();
    map.assign(n, -1);
    for (size_t b = 0; b < p.blocks.size(); b++)
        for (int k = p.first_inst((int)b); k != p.blocks[b].eb; k = p.nodes[k].next) {
            int num = p.nodes[k].s.number;
            if (num >= 0 && num < n) map[num] = (int)out.size();
            out.push_back(p.nodes[k].s.w);
        }
    return 0;
}

bool strip_phase_b(const Word *code, int n, const std::string &consts, std::vector<Word> *inOut, Cfg *cfg,
                   std::vector<int> *keepOut) {
    std::vector<SInst> all(n);
    for (int k = 0; k < n; k++) build_sinst(code[k], ST_UNKNOWN, false, &all[k]);
    std::vector<Word> word(code, code + n);
    std::vector<long long> target(n, 0);
    for (int k = 0; k < n; k++) {
        long long imm = rel_bytes(all[k]);
        target[k] = imm == 1 ? -1 : k + 1 + imm / 16;
    }

    std::vector<uint8_t> drop(n, 0);
    for (int k = 0; k < n; k++) {
        const SInst &s = all[k];
        int sop = s.sc.sop;
        bool nop = is_named(s, "NOP") || sop == SOP_SM70_NOP;
        bool zero = code[k].lo == 0 && code[k].hi == 0;
        bool selfBra = sop == SOP_SM70_BRA && target[k] == k;
        bool warpsync = sop == SOP_SM70_WARPSYNC && k > 0 && all[k - 1].sc.sop == SOP_SM70_BSYNC;
        bool padNop = nop && k > 0 && (all[k - 1].sc.sop == SOP_SM70_BRA || (drop[k - 1] && is_named(all[k - 1], "NOP")));
        drop[k] = zero || sop == SOP_SM70_DEPBAR || selfBra || warpsync || padNop;
    }

    for (int k = 0; k + 1 < n; k++) {
        const SInst &s = all[k];
        if (drop[k] || !sb_is_jmp(s) || !sb_is_cond_flow(s) || target[k] != k + 2) continue;
        const SInst &b = all[k + 1];
        if (drop[k + 1] || !sb_is_jmp(b) || sb_is_cond_flow(b) || target[k + 1] < 0) continue;
        bool aimed = false;
        for (int j = 0; j < n && !aimed; j++) aimed = target[j] == k + 1;
        if (aimed) continue;
        SInst inv = s;
        invert_branch(inv, ST_UNKNOWN);
        word[k] = inv.w;
        target[k] = target[k + 1];
        drop[k + 1] = 1;
    }

    std::vector<uint8_t> lead(n + 1, 0);
    lead[0] = 1;
    auto next_kept = [&](int k) {
        for (int j = k + 1; j < n; j++)
            if (!drop[j]) return j;
        return -1;
    };
    int prevKept = -1;
    for (int k = 0; k < n; k++) {
        if (drop[k]) continue;
        const SInst &s = all[k];
        if (target[k] >= 0 && target[k] <= n) lead[target[k]] = 1;
        int sop = s.sc.sop;
        bool nop = is_named(s, "NOP") || sop == SOP_SM70_NOP;
        int nk = next_kept(k);
        bool nopRun = nop && nk >= 0 && (is_named(all[nk], "NOP") || all[nk].sc.sop == SOP_SM70_NOP);
        int cls = s.in.cls;
        if (sop == SOP_SM70_BRA || sop == SOP_SM70_BRX || sop == SOP_SM73_BRXU || sop == SOP_SM70_EXIT ||
            sop == SOP_SM70_RET || sop == SOP_SM70_JMX || sop == SOP_SM70_JMP || sop == SOP_SM70_CALL ||
            sop == SOP_SM70_BSYNC || sop == SOP_SM70_MEMBAR || is_named(s, "LEPC") || is_named(s, "ERRBAR") ||
            (nop && !nopRun) ||
            cls == 84 || cls == 91)
            lead[k + 1] = 1;
        bool afterClear = prevKept >= 0 && all[prevKept].in.cls == 80;
        if (sop == SOP_SM70_CALL || is_named(s, "ERRBAR") || sop == SOP_SM70_WARPSYNC ||
            cls == 80 || (cls == 91 && !afterClear))
            lead[k] = 1;
        prevKept = k;
    }

    std::vector<uint8_t> emptyAt(n + 1, 0);
    for (int k = 0; k < n; k++) {
        if (drop[k] || all[k].sc.sop != SOP_SM70_BSSY) continue;
        long long x = target[k];
        if (x <= k || x > n) continue;
        int before = (int)x - 1;
        while (before > k && drop[before]) before--;
        if (all[before].sc.sop != SOP_SM70_BSYNC) continue;
        for (int j = 0; j < n && !emptyAt[x]; j++)
            if (!drop[j] && sb_is_jmp(all[j]) && target[j] == x) emptyAt[x] = 1;
    }
    std::vector<Word> &in = *inOut;
    std::vector<int> &keep = *keepOut;
    in.clear();
    keep.clear();
    *cfg = Cfg();
    std::vector<int> blockAt(n + 1, -1);
    std::vector<int> emptyBlock(n + 1, -1);
    bool pend = false;
    for (int k = 0; k < n; k++) {
        pend |= lead[k] != 0;
        if (emptyAt[k]) {
            emptyBlock[k] = (int)cfg->starts.size();
            cfg->starts.push_back((int)in.size());
            pend = true;
        }
        if (drop[k]) continue;
        if (pend) cfg->starts.push_back((int)in.size());
        pend = false;
        in.push_back(word[k]);
        keep.push_back(k);
    }
    int m = (int)in.size(), nb = (int)cfg->starts.size();
    if (m == 0) return false;

    std::vector<int> blockOfIn(m, 0);
    for (int b = 0; b < nb; b++)
        for (int i = cfg->starts[b]; i < (b + 1 < nb ? cfg->starts[b + 1] : m); i++) blockOfIn[i] = b;
    std::vector<int> firstKept(n + 1, -1);
    for (int w = n, i = m - 1; w >= 0; w--) {
        while (i >= 0 && keep[i] >= w) i--;
        firstKept[w] = i + 1 < m ? i + 1 : -1;
        blockAt[w] = i + 1 < m ? blockOfIn[i + 1] : -1;
    }
    cfg->rel.assign(m, -1);
    std::set<int> fstart = {0};
    for (int i = 0; i < m; i++) {
        long long t = target[keep[i]];
        if (t < 0 || t > n) continue;

        cfg->rel[i] = all[keep[i]].sc.sop == SOP_SM70_BSSY && emptyBlock[t] >= 0 ? emptyBlock[t] : blockAt[t];
        if (sb_is_call(all[keep[i]]) && blockAt[t] >= 0) fstart.insert(blockAt[t]);
    }
    cfg->funcs.assign(fstart.begin(), fstart.end());
    cfg->jmx.assign(nb, std::vector<int>());
    for (int b = 0; b < nb; b++) {
        int i = (b + 1 < nb ? cfg->starts[b + 1] : m) - 1;
        const SInst &s = all[keep[i]];
        if (!sb_is_jmx(s)) continue;
        std::vector<int> words = jump_table(all.data(), keep[i], consts, [&](int w) {
            return w <= n && blockAt[w] >= 0 && cfg->starts[blockAt[w]] == firstKept[w];
        });
        std::vector<int> best;
        for (int w : words) best.push_back(blockAt[w]);
        cfg->jmx[b] = best;
    }
    return true;
}

}
}
}
