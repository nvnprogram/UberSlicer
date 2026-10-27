
#include "validate.h"

#include <algorithm>
#include <cstring>

#include "issue.h"
#include "machine.h"
#include "phase_b.h"
#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

namespace {

const int NUM_SB = 6;
const int NO_SB = 7;

const int AGE_CAP = 64;

const int ORDER_CAP = 64;

const int NKEYS = 336;
int reg_key(const SReg &r) {
    switch (r.cls) {
    case RC_R: return r.no >= 0 && r.no < 255 ? r.no : -1;
    case RC_UR: return r.no >= 0 && r.no < 63 ? 256 + r.no : -1;
    case RC_P: return r.no >= 0 && r.no < 7 ? 320 + r.no : -1;
    case RC_UP: return r.no >= 0 && r.no < 7 ? 328 + r.no : -1;
    default: return -1;
    }
}

long long value(const SInst &s, const char *name) {
    if (s.in.cls < 0) return -1;
    int v = val_index(s.in.cls, name);
    return v >= 0 ? get(s.in, v) : -1;
}

int rel_target(const SInst &s, int at) {
    if (s.in.cls < 0) return -1;
    Operand o[MAX_OPNDS];
    int no = operands(s.in, o, MAX_OPNDS);
    for (int j = 0; j < no; j++)
        if (o[j].kind == O_REL) return at + 1 + (int)(o[j].imm / 16);
    return -1;
}

bool call_word(const SInst &s) { return sb_is_call(s) || (s.in.cls >= 0 && !strcmp(op_name(s.in.op), "CALL")); }

bool jump_call(const SInst &s) {
    bool uniform = false, neg = false;
    return call_word(s) && (guard(s.in, &uniform, &neg) != 7 || neg);
}

bool ordered_vq(int vq) { return vq >= VQ_ORDERED_FIRST && vq <= VQ_ORDERED_LAST; }

bool bar_reads_done(const SInst &s) {
    if (s.sc.sop != SOP_SM70_BAR || s.pred >= 0 || !ordered_vq(s.sc.vq) || s.sc.vq == VQ_ORDERED_FIRST) return false;
    return bar_blocks(s.in.cls);
}

bool complementary(const SInst &a, const SInst &b) {
    return a.pred >= 0 && b.pred >= 0 && a.pred == b.pred && a.pred_cls == b.pred_cls && a.pred_cond != b.pred_cond;
}

struct Item {
    int16_t key;
    uint8_t kind;
    uint8_t rd;
    int prod;
    int a, b;
    bool operator<(const Item &o) const {
        if (kind != o.kind) return kind < o.kind;
        if (key != o.key) return key < o.key;
        if (prod != o.prod) return prod < o.prod;
        return rd < o.rd;
    }
    bool same(const Item &o) const { return kind == o.kind && key == o.key && prod == o.prod && rd == o.rd; }
};
typedef std::vector<Item> State;

bool merge(State &x, const State &y) {
    State m;
    m.reserve(x.size() + y.size());
    size_t i = 0, j = 0;
    bool changed = false;
    while (i < x.size() || j < y.size()) {
        if (j == y.size() || (i < x.size() && x[i] < y[j])) {
            m.push_back(x[i++]);
        } else if (i == x.size() || y[j] < x[i]) {
            m.push_back(y[j++]);
            changed = true;
        } else {
            Item t = x[i];
            if (y[j].a < t.a || y[j].b < t.b) changed = true;
            t.a = std::min(t.a, y[j].a);
            t.b = std::min(t.b, y[j].b);
            m.push_back(t);
            i++;
            j++;
        }
    }
    x.swap(m);
    return changed;
}

struct Fx { int prod, age; };

struct Rel { int prod; bool rd; int sb; int newer; int qnewer; };

struct Checker {
    const std::vector<SInst> &s;
    const std::vector<Ctl> &ctl;
    std::vector<Hazard> *out = nullptr;
    int found = 0;

    std::vector<std::vector<Fx>> fw, fr;
    std::vector<std::vector<int>> dw, dr;
    std::vector<Rel> rel;
    int sbAge[NUM_SB];

    Checker(const std::vector<SInst> &s_, const std::vector<Ctl> &c_)
        : s(s_), ctl(c_), fw(NKEYS), fr(NKEYS), dw(NKEYS), dr(NKEYS) {}

    void report(int at, int from, int kind, int need, int have) {
        found++;
        if (out) out->push_back({at, from, kind, need, have});
    }

    void load(const State &st) {
        for (int k = 0; k < NKEYS; k++) {
            fw[k].clear();
            fr[k].clear();
            dw[k].clear();
            dr[k].clear();
        }
        rel.clear();
        for (int q = 0; q < NUM_SB; q++) sbAge[q] = AGE_CAP;
        for (const Item &x : st) {
            switch (x.kind) {
            case 0: fw[x.key].push_back({x.prod, x.a}); break;
            case 1: fr[x.key].push_back({x.prod, x.a}); break;
            case 2: dw[x.key].push_back(x.prod); break;
            case 3: dr[x.key].push_back(x.prod); break;
            case 4: rel.push_back({x.prod, x.rd != 0, x.key, x.a, x.b}); break;
            default: sbAge[x.key] = x.a; break;
            }
        }
    }

    bool shadowed(const std::vector<Fx> &v, size_t i, const SInst &x) const {
        if (x.pred < 0) return false;
        for (size_t j = i + 1; j < v.size(); j++) {
            const SInst &w = s[v[j].prod];
            if (w.pred == x.pred && w.pred_cls == x.pred_cls && w.pred_cond == x.pred_cond) return true;
        }
        return false;
    }

    bool pending(int prod, bool rd) const {
        for (const Rel &r : rel)
            if (r.prod == prod && r.rd == rd) return true;
        return false;
    }
    bool write_pending(int p) const { return pending(p, false); }
    bool read_pending(int p) const { return pending(p, true); }

    State save() const {
        State st;
        for (int k = 0; k < NKEYS; k++) {
            for (const Fx &f : fw[k])
                if (f.age < AGE_CAP) st.push_back({(int16_t)k, 0, 0, f.prod, f.age, 0});
            for (const Fx &f : fr[k])
                if (f.age < AGE_CAP) st.push_back({(int16_t)k, 1, 0, f.prod, f.age, 0});
            for (int p : dw[k])
                if (write_pending(p)) st.push_back({(int16_t)k, 2, 0, p, 0, 0});
            for (int p : dr[k])
                if (read_pending(p)) st.push_back({(int16_t)k, 3, 0, p, 0, 0});
        }
        for (const Rel &r : rel) st.push_back({(int16_t)r.sb, 4, (uint8_t)r.rd, r.prod, r.newer, r.qnewer});
        for (int q = 0; q < NUM_SB; q++)
            if (sbAge[q] < AGE_CAP) st.push_back({(int16_t)q, 5, 0, -1, sbAge[q], 0});
        std::sort(st.begin(), st.end());

        State u;
        for (const Item &x : st) {
            if (!u.empty() && u.back().same(x)) {
                u.back().a = std::min(u.back().a, x.a);
                u.back().b = std::min(u.back().b, x.b);
                continue;
            }
            u.push_back(x);
        }
        return u;
    }

    void complete(std::vector<uint8_t> &done) {
        for (size_t i = 0; i < rel.size(); i++) {
            if (!done[i]) continue;
            int vq = s[rel[i].prod].sc.vq;
            if (!ordered_vq(vq)) continue;
            for (size_t j = 0; j < rel.size(); j++)
                if (!done[j] && (rel[j].rd || !rel[i].rd) && s[rel[j].prod].sc.vq == vq && rel[j].qnewer > rel[i].qnewer)
                    done[j] = 1;
        }

        for (size_t i = 0; i < rel.size(); i++)
            if (done[i] && !rel[i].rd)
                for (size_t j = 0; j < rel.size(); j++)
                    if (rel[j].prod == rel[i].prod && rel[j].rd) done[j] = 1;
        size_t w = 0;
        for (size_t i = 0; i < rel.size(); i++)
            if (!done[i]) rel[w++] = rel[i];
        rel.resize(w);
    }

    void wait_sb(int at, unsigned mask, int depbarSb, int depbarCnt) {
        std::vector<uint8_t> done(rel.size(), 0);
        for (int q = 0; q < NUM_SB; q++) {
            bool all = (mask >> q) & 1, part = q == depbarSb;
            if (!all && !part) continue;
            if (all && depbarSb < 0 && sbAge[q] < SCOREBOARD_RAW_DELAY)
                report(at, -1, HZ_SB_DELAY, SCOREBOARD_RAW_DELAY, sbAge[q]);
            for (size_t i = 0; i < rel.size(); i++)
                if (rel[i].sb == q && (all || rel[i].newer >= depbarCnt)) done[i] = 1;
        }
        complete(done);
    }
    void add_release(int prod, bool rd, int sb) {
        int vq = s[prod].sc.vq;
        for (Rel &r : rel) {
            if (sb < NUM_SB && r.sb == sb) r.newer = std::min(r.newer + 1, ORDER_CAP);
            if (ordered_vq(vq) && s[r.prod].sc.vq == vq) r.qnewer = std::min(r.qnewer + 1, ORDER_CAP);
        }
        rel.push_back({prod, rd, sb, 0, 0});
        if (sb < NUM_SB) sbAge[sb] = 0;
    }

    void step(int k, bool record) {
        const SInst &x = s[k];
        const Ctl &c = ctl[k];
        std::vector<Hazard> *keep = out;
        int keepFound = found;
        if (!record) out = nullptr;
        if (x.in.cls >= 0) {
            wait_sb(k, c.wait, -1, 0);
            if (x.sc.sop == SOP_SM70_DEPBAR) {
                long long q = value(x, "sbidx"), cnt = value(x, "cnt"), list = value(x, "scoreboard_list");
                wait_sb(k, list > 0 ? (unsigned)list : 0u, q >= 0 && q < NUM_SB ? (int)q : NUM_SB, (int)cnt);
            }

            if (bar_reads_done(x)) {
                std::vector<uint8_t> done(rel.size(), 0);
                for (size_t i = 0; i < rel.size(); i++)
                    if (rel[i].rd && s[rel[i].prod].sc.vq == x.sc.vq) done[i] = 1;
                complete(done);
            }
            bool varWrite = (x.flags & GF_NEEDS_WRITE_SB) != 0 || c.wr < NUM_SB;
            bool varRead = (x.flags & GF_NEEDS_READ_SB) != 0 || c.rd < NUM_SB;
            bool decoupled = (x.flags & GF_DECOUPLED) != 0;
            for (int r = 0; r < x.nregs; r++) {
                const SReg &g = x.regs[r];
                int key = reg_key(g);
                if (g.def || key < 0) continue;
                for (size_t i = 0; i < fw[key].size(); i++) {
                    const Fx &f = fw[key][i];
                    int need = dep_latency(DEP_FLOW, s[f.prod], x, 1 << g.cls, 0, false);
                    if (f.age < need && !complementary(s[f.prod], x) && !shadowed(fw[key], i, x))
                        report(k, f.prod, HZ_RAW_FIXED, need, f.age);
                }
                for (int p : dw[key])
                    if (write_pending(p) && !complementary(s[p], x)) report(k, p, HZ_RAW_SB, 0, 0);
            }
            for (int r = 0; r < x.nregs; r++) {
                const SReg &g = x.regs[r];
                int key = reg_key(g);
                if (!g.def || key < 0) continue;
                for (const Fx &f : fw[key]) {
                    int need = dep_latency(DEP_OUTPUT, s[f.prod], x, 1 << g.cls, 0, false);
                    if (f.age < need && !complementary(s[f.prod], x)) report(k, f.prod, HZ_WAW_FIXED, need, f.age);
                }

                for (int p : dw[key])
                    if (write_pending(p) && !complementary(s[p], x) && !(varWrite && same_ordered_vq(s[p], x)))
                        report(k, p, HZ_WAW_SB, 0, 0);
                for (const Fx &f : fr[key]) {
                    int need = dep_latency(DEP_ANTI, s[f.prod], x, 1 << g.cls, 0, false);
                    if (f.age < need && !complementary(s[f.prod], x)) report(k, f.prod, HZ_WAR_FIXED, need, f.age);
                }

                for (int p : dr[key])
                    if (read_pending(p) && !complementary(s[p], x) && !(varWrite && same_ordered_vq(s[p], x)))
                        report(k, p, HZ_WAR_SB, 0, 0);
            }

            for (int r = 0; r < x.nregs; r++) {
                const SReg &g = x.regs[r];
                int key = reg_key(g);
                if (key < 0) continue;
                if (g.def) {
                    if (x.pred < 0) {
                        fw[key].clear();
                        dw[key].clear();
                        fr[key].clear();
                        dr[key].clear();
                    }
                    if (varWrite) dw[key].push_back(k);
                    else fw[key].push_back({k, 0});
                } else if (varRead && g.cls == RC_R) {

                    dr[key].push_back(k);
                } else if (!decoupled) {
                    fr[key].push_back({k, 0});
                }
            }

            if (varRead) add_release(k, true, c.rd < NUM_SB ? c.rd : NO_SB);
            if (varWrite) add_release(k, false, c.wr < NUM_SB ? c.wr : NO_SB);
        }
        int d = std::max<int>(c.stall, 1);
        for (int key = 0; key < NKEYS; key++) {
            for (Fx &f : fw[key]) f.age = std::min(f.age + d, AGE_CAP);
            for (Fx &f : fr[key]) f.age = std::min(f.age + d, AGE_CAP);
        }
        for (int q = 0; q < NUM_SB; q++) sbAge[q] = std::min(sbAge[q] + d, AGE_CAP);
        out = keep;
        if (!record) found = keepFound;
    }
};

void check_word(const SInst &x, const Ctl &c, int k, std::vector<Hazard> *out, int *found) {
    auto report = [&](int kind, int need, int have) {
        (*found)++;
        if (out) out->push_back({k, -1, kind, need, have});
    };
    if (x.in.cls < 0) {
        report(HZ_DECODE, 0, 0);
        return;
    }
    if (!ctl_valid(x.in)) report(HZ_CTL_ROW, 0, 0);
    if (c.stall > 11 && c.yld) report(HZ_EG_STALL, 0, c.stall);
    if (c.wr == 6 || c.rd == 6) report(HZ_SB_INDEX, 0, 0);
    bool drain = c.stall == 0 && !c.yld;
    if ((ctl_reuse(x.in) || value(x, "reuse_src_e") > 0) && !c.yld) report(HZ_REUSE_EG, 0, 0);

    bool uniform, neg;
    bool guarded = guard(x.in, &uniform, &neg) != 7 || neg;
    if (x.sc.sop != SOP_SM70_NOP && !drain && !(call_word(x) && guarded)) {
        int need = ori_kind(x).minNext;
        if (c.stall < need) report(HZ_MIN_NEXT, need, c.stall);
    }
}

}

int validate(const Word *code, int n, const std::string &consts, int shader_type, std::vector<Hazard> *out) {
    if (n <= 0) return 0;
    std::vector<SInst> s(n);
    std::vector<Ctl> ctl(n);
    for (int k = 0; k < n; k++) {
        build_sinst(code[k], shader_type, false, &s[k]);
        ctl[k] = ctl_get(code[k]);
    }
    int found = 0;
    for (int k = 0; k < n; k++) check_word(s[k], ctl[k], k, out, &found);

    std::vector<uint8_t> lead(n + 1, 0);
    lead[0] = 1;
    std::vector<std::vector<int>> table(n);
    std::vector<int> target(n, -1);
    for (int k = 0; k < n; k++) {
        const SInst &x = s[k];
        if (x.in.cls < 0) continue;
        int o = x.sc.sop;
        if (sb_is_jmp(x) || sb_is_call(x) || o == SOP_SM70_BSSY) {
            target[k] = rel_target(x, k);
            if (target[k] >= 0 && target[k] < n) lead[target[k]] = 1;
            else target[k] = -1;
        }
        if (sb_is_jmx(x)) {
            table[k] = jump_table(s.data(), k, consts, [&](int w) { return w < n; });
            for (int t : table[k]) lead[t] = 1;
        }
        if (sb_is_jmp(x) || sb_is_jmx(x) || sb_is_call(x) || o == SOP_SM70_EXIT || o == SOP_SM70_RET ||
            o == SOP_SM70_JMP)
            lead[k + 1] = 1;
    }
    std::vector<int> start, blockOf(n + 1, -1);
    for (int k = 0; k < n; k++) {
        if (lead[k]) start.push_back(k);
        blockOf[k] = (int)start.size() - 1;
    }
    const int nb = (int)start.size();
    start.push_back(n);
    std::vector<int> afterCall;
    for (int b = 0; b + 1 < nb; b++)
        if (call_word(s[start[b + 1] - 1]) && !jump_call(s[start[b + 1] - 1])) afterCall.push_back(b + 1);
    std::vector<std::vector<int>> succ(nb);
    for (int b = 0; b < nb; b++) {
        int last = start[b + 1] - 1;
        const SInst &x = s[last];
        bool fall = b + 1 < nb, guarded = x.pred >= 0;
        std::vector<int> &v = succ[b];
        auto all = [&]() {
            for (int t = 0; t < nb; t++) v.push_back(t);
        };
        if (x.in.cls < 0) {
            if (fall) v.push_back(b + 1);
        } else if (sb_is_jmp(x)) {
            if (target[last] >= 0) v.push_back(blockOf[target[last]]);
            if (fall && (sb_is_cond_flow(x) || jump_call(x))) v.push_back(b + 1);
        } else if (sb_is_jmx(x)) {
            for (int t : table[last]) v.push_back(blockOf[t]);
            if (table[last].empty()) all();
            if (fall && guarded) v.push_back(b + 1);
        } else if (sb_is_call(x)) {
            if (target[last] >= 0) v.push_back(blockOf[target[last]]);
            if (fall && guarded) v.push_back(b + 1);
        } else if (x.sc.sop == SOP_SM70_RET) {
            for (int t : afterCall) v.push_back(t);
            if (fall && guarded) v.push_back(b + 1);
        } else if (x.sc.sop == SOP_SM70_EXIT) {
            if (fall && sb_is_retc(x)) v.push_back(b + 1);
        } else if (x.sc.sop == SOP_SM70_JMP) {
            all();
        } else if (fall) {
            v.push_back(b + 1);
        }
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
    }

    std::vector<std::vector<int>> retTo(nb);
    for (int c : afterCall) {
        int at = start[c] - 1;
        if (target[at] < 0) continue;
        std::vector<uint8_t> seen(nb, 0);
        std::vector<int> todo = {blockOf[target[at]]};
        while (!todo.empty()) {
            int b = todo.back();
            todo.pop_back();
            if (seen[b]) continue;
            seen[b] = 1;
            const SInst &x = s[start[b + 1] - 1];
            if (x.in.cls >= 0 && x.sc.sop == SOP_SM70_RET) {
                retTo[b].push_back(c);
                if (x.pred >= 0 && b + 1 < nb) todo.push_back(b + 1);
                continue;
            }
            if (call_word(x) && !jump_call(x)) {
                if (b + 1 < nb) todo.push_back(b + 1);
                continue;
            }
            for (int t : succ[b]) todo.push_back(t);
        }
    }
    for (int b = 0; b < nb; b++) {
        const SInst &x = s[start[b + 1] - 1];
        if (x.in.cls < 0 || x.sc.sop != SOP_SM70_RET || retTo[b].empty()) continue;
        std::vector<int> v = retTo[b];
        if (x.pred >= 0 && b + 1 < nb) v.push_back(b + 1);
        std::sort(v.begin(), v.end());
        v.erase(std::unique(v.begin(), v.end()), v.end());
        succ[b] = v;
    }

    Checker ck(s, ctl);
    std::vector<State> in(nb);
    std::vector<uint8_t> reached(nb, 0), queued(nb, 0);
    std::vector<int> work = {0};
    reached[0] = queued[0] = 1;
    while (!work.empty()) {
        int b = work.back();
        work.pop_back();
        queued[b] = 0;
        ck.load(in[b]);
        for (int k = start[b]; k < start[b + 1]; k++) ck.step(k, false);
        State o = ck.save();
        for (int t : succ[b]) {
            bool changed = merge(in[t], o) || !reached[t];
            reached[t] = 1;
            if (changed && !queued[t]) {
                queued[t] = 1;
                work.push_back(t);
            }
        }
    }
    ck.out = out;
    ck.found = 0;
    for (int b = 0; b < nb; b++) {
        if (!reached[b]) continue;
        ck.load(in[b]);
        for (int k = start[b]; k < start[b + 1]; k++) ck.step(k, true);
    }
    return found + ck.found;
}

}
}
}
