
#include "deps.h"

#include <cstring>

namespace ub {
namespace sm86 {
namespace sched {

namespace {

const int REGCLASS_NONE = -1;
const int MEMDOM_NONE = -1;

int val_of(const Inst &i, const char *name, int dflt) {
    int v = val_index(i.cls, name);
    return v < 0 ? dflt : (int)get(i, v);
}

struct Graph {
    std::vector<std::vector<DepEdge>> made;
    std::vector<int> ref;

    void add(int from, int to, int type, int cls, int dom) {
        uint16_t rm = cls >= 0 && cls < 16 ? (uint16_t)(1u << cls) : 0;
        uint32_t mm = dom >= 0 && dom < MD_COUNT ? 1u << dom : 0;
        for (DepEdge &e : made[from]) {
            if (e.to == to && e.type == type) {
                e.reg_mask |= rm;
                e.mem_mask |= mm;
                return;
            }
        }
        ref[to]++;
        made[from].push_back(DepEdge{to, (uint8_t)type, rm, mm});
    }
};

struct RegState {
    int ip = -1, lastDefP = -1, lastDefNotP = -1;
};

struct RegMap {
    const SInst *in;
    std::vector<int> idx;
    std::vector<RegState> tab;
    std::vector<int> touched;
    std::vector<uint8_t> *prohibit;
    Graph *g;

    static int key(int cls, int no) { return cls * 1024 + (no & 1023); }
    void init(int n) {
        for (int k : touched) tab[k] = RegState();
        touched.clear();
        idx.assign(n, 0);
        if (tab.empty()) tab.resize(8 * 1024);
    }
    bool predicated(int i) const { return in[i].pred >= 0; }

    std::vector<uint16_t> predDefs[16];
    void count_pred_defs(int n) {
        for (int p = 0; p < 16; p++) predDefs[p].assign(n + 1, 0);
        for (int i = 0; i < n; i++) {
            for (int p = 0; p < 16; p++) predDefs[p][i + 1] = predDefs[p][i];
            for (int k = 0; k < in[i].nregs; k++) {
                const SReg &r = in[i].regs[k];
                if (!r.def || r.no < 0 || r.no > 7) continue;
                if (r.cls == RC_P) predDefs[r.no][i + 1]++;
                else if (r.cls == RC_UP) predDefs[8 + r.no][i + 1]++;
            }
        }
    }

    bool compare_preds(int a, int b) const {
        if (a < 0 || b < 0) return false;
        if (!predicated(a) || !predicated(b)) return false;
        if (in[a].pred_cls != in[b].pred_cls || in[a].pred != in[b].pred) return false;
        int p = (in[a].pred_cls == RC_UP ? 8 : 0) + (in[a].pred & 7);
        int lo = a < b ? a : b, hi = a < b ? b : a;
        return predDefs[p][hi] == predDefs[p][lo];
    }
    bool complementary_preds(int a, int b) const {
        return compare_preds(a, b) && in[a].pred_cond != in[b].pred_cond;
    }
    bool identical_preds(int a, int b) const {
        return compare_preds(a, b) && in[a].pred_cond == in[b].pred_cond;
    }

    bool defines_reg(int i, int no) const {
        const SInst &s = in[i];
        for (int k = 0; k < s.nregs; k++)
            if (s.regs[k].first_def) return s.regs[k].no == no;
        return false;
    }
    bool insts_complementary(int a, int b, int cls, int no) const {
        if (a < 0 || b < 0) return false;
        if (!complementary_preds(a, b)) return false;
        if ((cls == RC_P || cls == RC_UP) && in[a].pred == no)
            if (defines_reg(a, no) || defines_reg(b, no)) return false;
        return true;
    }
    int most_recent(int a, int b) const {
        int ia = a >= 0 ? idx[a] : 0, ib = b >= 0 ? idx[b] : 0;
        return ia > ib ? a : b;
    }
    void add_deps(int from, int to, int type, int cls) {
        if (from < 0) return;
        if (type == DEP_ANTI) g->add(to, from, type, cls, MEMDOM_NONE);
        else g->add(from, to, type, cls, MEMDOM_NONE);
    }

    void create(int ip, int cls, int no, int type) {
        const RegState st = tab[key(cls, no)];
        if (type == DEP_FLOW &&
            (insts_complementary(ip, st.lastDefNotP, cls, no) || insts_complementary(st.lastDefP, ip, cls, no)))
            (*prohibit)[ip] = 1;
        if (cls == RC_CC) {
            add_deps(st.ip, ip, type, cls);
            return;
        }
        int latest = most_recent(st.lastDefP, st.lastDefNotP);
        int earliest = latest == st.lastDefP ? st.lastDefNotP : st.lastDefP;
        add_deps(latest, ip, type, cls);
        if (insts_complementary(latest, earliest, cls, no)) add_deps(earliest, ip, type, cls);
    }
    void update(int ip, int cls, int no) {
        int k = key(cls, no);
        RegState &st = tab[k];
        if (st.ip < 0 && st.lastDefP < 0 && st.lastDefNotP < 0) touched.push_back(k);
        bool trueCond = !predicated(ip) || in[ip].pred_cond == PRED_COND_TRUE;
        if (trueCond) st.lastDefP = ip;
        else st.lastDefNotP = ip;
        st.ip = ip;
    }
    void flow(int ip, int cls, int no) {
        int p = tab[key(cls, no)].ip;
        if (p >= 0 && p != ip) create(ip, cls, no, DEP_FLOW);
    }
    void anti(int ip, int cls, int no) {
        int p = tab[key(cls, no)].ip;
        if (p >= 0 && p != ip) create(ip, cls, no, DEP_ANTI);
    }
    void output(int ip, int cls, int no) {
        int p = tab[key(cls, no)].ip;
        if (p >= 0 && p != ip) create(ip, cls, no, DEP_OUTPUT);
        update(ip, cls, no);
    }
};

enum MemOp { MO_READ, MO_WRITE };

struct MemDepInfo {
    int ip;
    int op;
    int dom;
    int vr = -1, vr2 = -1, start = -1, size = 0;
    void range(int a, int b, int s, int z) { vr = a; vr2 = b; start = s; size = z; }
};

bool overlapping(const MemDepInfo &a, const MemDepInfo &b, bool &covered) {
    covered = false;
    bool ov = false;
    if (a.start == -1 || b.start == -1) ov = true;
    else if (a.vr != b.vr || a.vr2 != b.vr2) ov = true;
    else if ((b.start >= a.start && b.start < a.start + a.size) || (a.start >= b.start && a.start < b.start + b.size))
        ov = true;
    if (ov) {

        if (b.start == -1) covered = true;
        else covered = b.vr == a.vr && b.vr2 == a.vr2 && b.start <= a.start && b.start + b.size >= a.start + a.size;
    }
    return ov;
}

struct MemDep {
    Graph *g;
    std::vector<MemDepInfo> rd[MD_COUNT], wr[MD_COUNT];
    int alias[MD_COUNT];
    int distinct = 0;
    int psync = -1;
    std::vector<int> addrRefs;
    std::vector<uint8_t> urDep;
    static const int LIST_LIMIT = 200;

    void init() {
        for (int k = 0; k < MD_COUNT; k++) {
            rd[k].clear();
            wr[k].clear();
            alias[k] = 0;
        }
        implicit(MD_GENMEM, MD_LMEM);
        implicit(MD_GENMEM, MD_SMEM);
        implicit(MD_GENMEM, MD_GMEM);
        implicit(MD_GENMEM, MD_IPARAM);
        implicit(MD_LMEM, MD_IPARAM);
        distinct = 0;
        psync = -1;
    }
    void implicit(int a, int b) {
        alias[a] |= 1 << b;
        alias[b] |= 1 << a;
    }
    int list_count(int op, int dom) const {
        int c = (int)wr[dom].size();
        if (op == MO_WRITE && (int)rd[dom].size() > c) c = (int)rd[dom].size();
        return c;
    }
    int list_count(const MemDepInfo &d) const {
        if (alias[d.dom] == 0) return list_count(d.op, d.dom);
        int mask = (1 << d.dom) | alias[d.dom], c = 0;
        for (int k = 0; mask != 0; k++) {
            int t = list_count(d.op, k);
            if (t > c) c = t;
            mask >>= 1;
        }
        return c;
    }
    void add(int from, int to, int dom) { g->add(from, to, DEP_ORDER, REGCLASS_NONE, dom); }
    void do_read(const MemDepInfo &d) {
        if (!rd[d.dom].empty() && rd[d.dom][0].ip == d.ip) return;
        bool dummy;
        for (const MemDepInfo &w : wr[d.dom])
            if (overlapping(w, d, dummy) && w.ip != d.ip) add(w.ip, d.ip, w.dom);
        rd[d.dom].insert(rd[d.dom].begin(), d);
    }
    void do_write(const MemDepInfo &d) {
        if (!wr[d.dom].empty() && wr[d.dom][0].ip == d.ip) return;
        bool cov;
        for (size_t k = 0; k < rd[d.dom].size();) {
            const MemDepInfo &r = rd[d.dom][k];
            if (overlapping(r, d, cov)) {
                if (r.ip != d.ip) add(r.ip, d.ip, r.dom);
                if (cov) {
                    rd[d.dom].erase(rd[d.dom].begin() + k);
                    continue;
                }
            }
            k++;
        }
        for (size_t k = 0; k < wr[d.dom].size();) {
            const MemDepInfo &w = wr[d.dom][k];
            if (overlapping(w, d, cov)) {
                add(w.ip, d.ip, w.dom);
                if (cov) {
                    wr[d.dom].erase(wr[d.dom].begin() + k);
                    continue;
                }
            }
            k++;
        }
        wr[d.dom].insert(wr[d.dom].begin(), d);
    }
    void add_for_all(int ip, std::vector<MemDepInfo> &l, bool covered) {
        for (const MemDepInfo &m : l) add(m.ip, ip, m.dom);
        if (covered) l.clear();
    }
    void alias_deps(const MemDepInfo &d) {
        int mask = alias[d.dom];
        bool covered = d.op == MO_WRITE && d.start == -1 && d.dom == MD_GENMEM;
        for (int k = 0; mask != 0; k++) {
            if (mask & 1) {
                if (d.op == MO_WRITE) add_for_all(d.ip, rd[k], covered);
                add_for_all(d.ip, wr[k], covered);
            }
            mask >>= 1;
        }
    }
};

int g_nop = -2;

void init_ops() {
    if (g_nop == -2) g_nop = op_id("NOP");
}

bool is_nop(const SInst &s) { return s.in.op == g_nop || s.sc.sop == SOP_SM70_NOP; }

bool is_flow_control(const SInst &s) {
    switch (s.sc.sop) {
    case SOP_SM70_BRA: case SOP_SM70_BRX: case SOP_SM73_BRXU: case SOP_SM70_EXIT: case SOP_SM70_RET:
    case SOP_SM70_CALL: case SOP_SM70_BSYNC: case SOP_SM70_MEMBAR: case SOP_SM70_JMP: case SOP_SM70_JMX:
        return true;
    default:
        return false;
    }
}

bool is_jmp(const SInst &s) {
    if (s.sc.sop == SOP_SM70_JMP) return true;
    if (s.sc.sop != SOP_SM70_BRA || val_index(s.in.cls, "UPp") >= 0) return false;
    return val_of(s.in, "Pg", 7) == 7 && val_of(s.in, "Pg@not", 0) == 0 && val_of(s.in, "Pp", 7) == 7 &&
           val_of(s.in, "Pp@not", 0) == 0 && val_index(s.in.cls, "Pp") >= 0;
}

bool has_uniform_reg(const SInst &s) {
    for (int k = 0; k < s.nregs; k++)
        if (s.regs[k].cls == RC_UR || s.regs[k].cls == RC_UP) return true;
    return false;
}

bool cannot_change_threads(const SInst &s) {
    switch (s.sc.sop) {
    case SOP_SM70_SHFL: case SOP_SM70_VOTE: case SOP_SM73_VOTEU: case SOP_SM70_MATCH: case SOP_SM70_FSWZADD:
    case SOP_SM82_REDUX: case SOP_SM70_BSSY: case SOP_SM70_BMOV: case SOP_SM70_BMOV_B: case SOP_SM70_BMOV_R:
    case SOP_SM70_BREAK: case SOP_SM70_ATOMG: case SOP_SM70_ATOMS: case SOP_SM70_ATOM: case SOP_SM70_RED:
    case SOP_SM70_SUATOM: case SOP_SM70_SURED:
        return true;
    default:
        return false;
    }
}

bool can_alter_mask(const SInst &s, bool compute) {
    if (is_flow_control(s) && !is_jmp(s) && s.sc.sop != SOP_SM70_MEMBAR) return true;
    switch (s.sc.sop) {
    case SOP_SM70_KILL: case SOP_SM70_WARPSYNC: case SOP_SM70_BREAK: case SOP_SM70_YIELD:
        return true;
    case SOP_SM70_BMOV: case SOP_SM70_BMOV_B: case SOP_SM70_BMOV_R:
        for (int k = 0; k < s.nregs; k++)
            if (s.regs[k].def && s.regs[k].cls == RC_STATE) return true;
        return false;
    case SOP_SM70_BAR:
        return !compute && val_of(s.in, "barmode", 0) == 0;
    default:
        return false;
    }
}

int mem_size_bytes(int sz) {
    static const int b[8] = {1, 1, 2, 2, 4, 8, 16, 16};
    return sz >= 0 && sz < 8 ? b[sz] : 4;
}

void refine(const SInst &s, MemDepInfo &d, const MemDep &md, bool attr) {
    if (md.list_count(d) >= MemDep::LIST_LIMIT) {
        if (md.alias[d.dom] & (1 << MD_GENMEM)) d.dom = MD_GENMEM;
        return;
    }
    int ra = val_of(s.in, "Ra", 255);

    if (ra != 255 && md.addrRefs[d.ip] <= 1) return;
    int vr = ra == 255 ? -1 : ra;
    int ur = val_of(s.in, "Ra_URb", -1);
    if (ur < 0) ur = val_of(s.in, "Ra_URc", -1);
    if (ur == 63) ur = -1;
    int off = val_of(s.in, "Ra_offset", 0);
    int size = attr ? (val_of(s.in, "sz", 0) + 1) * 4 : mem_size_bytes(val_of(s.in, "sz", 4));
    d.range(vr, ur, off, size);
}

int get_mem_dep(const SInst &s, int ip, bool lastInBlock, const DepsCtx &ctx, MemDep &md, MemDepInfo *out) {
    int n = 0;
    auto put = [&](int op, int dom) -> MemDepInfo & {
        MemDepInfo &d = out[n++];
        d = MemDepInfo();
        d.ip = ip;
        d.op = op;
        d.dom = dom;
        return d;
    };
    int sop = s.sc.sop;
    bool isNop = is_nop(s);
    bool asMembar = sop == SOP_SM70_MEMBAR || (isNop && lastInBlock);
    bool asBar = sop == SOP_SM70_BAR || (isNop && !lastInBlock);
    bool tex = false;
    switch (sop) {
    case SOP_SM70_LDG: refine(s, put(MO_READ, MD_GMEM), md, false); break;
    case SOP_SM70_STG: refine(s, put(MO_WRITE, MD_GMEM), md, false); break;
    case SOP_SM70_LDS: refine(s, put(MO_READ, MD_SMEM), md, false); break;
    case SOP_SM70_STS: refine(s, put(MO_WRITE, MD_SMEM), md, false); break;
    case SOP_SM70_LDL: refine(s, put(MO_READ, MD_LMEM), md, false); break;
    case SOP_SM70_STL: refine(s, put(MO_WRITE, MD_LMEM), md, false); break;
    case SOP_SM70_LD: refine(s, put(MO_READ, MD_GENMEM), md, false); break;
    case SOP_SM70_ST: refine(s, put(MO_WRITE, MD_GENMEM), md, false); break;
    case SOP_SM70_ALD:

        if (ctx.shared_isb) put(MO_READ, MD_OBUF);
        else refine(s, put(MO_READ, MD_IBUF), md, true);
        break;
    case SOP_SM70_AST: refine(s, put(MO_WRITE, MD_OBUF), md, true); break;
    case SOP_SM70_ATOMG: case SOP_SM70_RED: put(MO_WRITE, MD_GMEM); break;
    case SOP_SM70_ATOMS: put(MO_WRITE, MD_SMEM); break;
    case SOP_SM70_ATOM: put(MO_WRITE, MD_GENMEM); break;
    case SOP_SM70_SULD: put(MO_READ, MD_SURF); break;
    case SOP_SM70_SUST: case SOP_SM70_SUATOM: case SOP_SM70_SURED: put(MO_WRITE, MD_SURF); break;
    case SOP_SM70_ISBERD:
        put(MO_READ, MD_SMEM);
        put(MO_READ, MD_OBUF);
        put(MO_READ, MD_OBUF);
        break;
    case SOP_SM73_ISBEWR:
        put(MO_WRITE, MD_SMEM);
        put(MO_WRITE, MD_IBUF);
        put(MO_WRITE, MD_OBUF);
        break;
    case SOP_SM70_ERRBAR: put(MO_WRITE, MD_GENMEM); break;
    case SOP_SM70_OUT: case SOP_SM70_OUT_FINAL: put(MO_READ, MD_OBUF); break;
    case SOP_SM70_TEX: case SOP_SM70_TLD: case SOP_SM70_TLD4: case SOP_SM70_TXD: case SOP_SM70_TMML:
    case SOP_SM70_TXQ: case SOP_SM73_FOOTPRINT:
        put(MO_READ, MD_TEX);
        tex = true;
        break;
    default:
        if (asMembar) {
            put(MO_WRITE, MD_GENMEM);
            put(MO_WRITE, MD_SURF);
            if (val_of(s.in, "sco", 0) >= 3) put(MO_WRITE, MD_TEX);
            put(MO_WRITE, MD_TTU);
        } else if (asBar) {
            put(MO_WRITE, MD_SURF);
            put(MO_WRITE, MD_GMEM);
            put(MO_WRITE, MD_SMEM);
        }
        break;
    }

    if (ctx.has_kil) {
        bool killDep = false;
        switch (sop) {
        case SOP_SM70_STG: case SOP_SM70_ST: case SOP_SM70_ATOMG: case SOP_SM70_ATOM: case SOP_SM70_RED:
        case SOP_SM70_SUST: case SOP_SM70_SUATOM: case SOP_SM70_SURED:
            killDep = true;
            break;
        default:
            killDep = asMembar || (cannot_change_threads(s) && sop != SOP_SM70_BSSY && sop != SOP_SM70_BREAK &&
                                   sop != SOP_SM70_BMOV && sop != SOP_SM70_BMOV_B && sop != SOP_SM70_BMOV_R);
            break;
        }
        if (killDep) {
            put(MO_READ, MD_KILL);
        } else if (sop == SOP_SM70_KILL) {
            put(MO_WRITE, MD_KILL).range(-1, -1, md.distinct++, 1);
        }
    }
    if (sop == SOP_SM70_WARPSYNC) put(MO_WRITE, MD_IMPLICIT_DERIVATIVES);
    if (tex) put(MO_READ, MD_IMPLICIT_DERIVATIVES);
    if (sop == SOP_SM70_OUT || sop == SOP_SM70_OUT_FINAL) put(MO_WRITE, MD_ARCH_STATE);

    if (sop == SOP_SM70_EXIT || sop == SOP_SM70_RET) {
        put(MO_READ, MD_SURF);
        put(MO_READ, MD_GMEM);
        put(MO_READ, MD_SMEM);
        put(MO_READ, MD_LMEM);
        put(MO_READ, MD_OBUF);
        put(MO_READ, MD_PATCH);
        put(MO_READ, MD_MAP);
        put(MO_READ, MD_ARCH_STATE);
        if (ctx.has_kil) put(MO_READ, MD_KILL);
    }

    if (can_alter_mask(s, ctx.compute)) {
        bool cannot = cannot_change_threads(s) || has_uniform_reg(s);
        MemDepInfo &a = put(MO_WRITE, MD_ACTIVE_MASK);
        if (!cannot && md.list_count(a) < MemDep::LIST_LIMIT) a.range(-1, -1, md.distinct++, 1);
        if (sop != SOP_SM70_KILL) {
            MemDepInfo &u = put(MO_WRITE, MD_UR);
            if (!cannot && md.list_count(u) < MemDep::LIST_LIMIT) u.range(-1, -1, md.distinct++, 1);
        }
    } else {
        if (cannot_change_threads(s)) put(MO_READ, MD_ACTIVE_MASK);
        if (md.urDep[ip]) put(MO_READ, MD_UR);
    }
    return n;
}

int addr_refs(const SInst *in, int n, int i, const DepsCtx &ctx) {
    int ra = val_of(in[i].in, "Ra", 255);
    if (ra == 255) return 0;
    auto reads = [&](const SInst &s) {
        for (int r = 0; r < s.nregs; r++)
            if (s.regs[r].cls == RC_R && !s.regs[r].def && s.regs[r].no == ra) return true;
        return false;
    };
    auto writes = [&](const SInst &s) {
        for (int r = 0; r < s.nregs; r++)
            if (s.regs[r].cls == RC_R && s.regs[r].def && s.regs[r].no == ra) return true;
        return false;
    };
    int start = i;
    while (start > 0 && !writes(in[start - 1])) start--;
    int c = 0;
    for (int k = start; k < n; k++) {
        if (reads(in[k])) c++;
        if (k >= i && writes(in[k])) return c;
    }

    for (int k = 0; k < ctx.nafter && c < 2; k++) {
        if (reads(ctx.after[k])) c++;
        if (writes(ctx.after[k])) break;
    }
    return c;
}

bool is_vector_op(const SInst &s) {
    switch (s.sc.sop) {
    case SOP_SM70_LDG: case SOP_SM70_STG: case SOP_SM70_LDS: case SOP_SM70_STS: case SOP_SM70_LDL:
    case SOP_SM70_STL: case SOP_SM70_LD: case SOP_SM70_ST: case SOP_SM70_ATOM: case SOP_SM70_ATOMG:
    case SOP_SM70_RED: case SOP_SM70_ATOMS: case SOP_SM70_ALD: case SOP_SM70_AST: case SOP_SM70_LDC:
    case SOP_SM70_TEX: case SOP_SM70_TLD: case SOP_SM70_TLD4: case SOP_SM70_TMML: case SOP_SM70_TXD:
    case SOP_SM70_TXQ: case SOP_SM70_SULD: case SOP_SM70_SUST: case SOP_SM70_SUATOM: case SOP_SM70_SURED:
    case SOP_SM73_FOOTPRINT: case SOP_SM70_IPA: case SOP_SM70_OUT: case SOP_SM70_OUT_FINAL:
    case SOP_SM70_ISBERD: case SOP_SM73_ISBEWR: case SOP_SM73_ULDC: case SOP_SM70_SHFL:
        return true;
    default:
        return false;
    }
}

}

int rev_regs(const SInst &s, uint8_t *ord) {
    bool vec = is_vector_op(s);
    int ra = -1, ur = -1;
    if (vec && val_of(s.in, "e", 0) == 1) {
        ra = val_of(s.in, "Ra", 255);
        ur = val_of(s.in, "Ra_URb", -1);
    }
    int n = 0;
    for (int e = s.nregs; e > 0;) {
        int b = e - 1;
        while (b > 0 && s.regs[b - 1].opd == s.regs[e - 1].opd && s.regs[b - 1].def == s.regs[e - 1].def) b--;
        const SReg &r = s.regs[b];
        bool wide = e - b == 2 && (r.cls == RC_R || r.cls == RC_UR);
        if (wide && vec)
            wide = !r.def && ((r.cls == RC_R && ra >= 0 && ra != 255 && r.no == ra) ||
                              (r.cls == RC_UR && ur >= 0 && ur != 63 && r.no == ur));
        if (wide) {
            ord[n++] = (uint8_t)b;
            ord[n++] = (uint8_t)(b + 1);
        } else {
            for (int k = e - 1; k >= b; k--) ord[n++] = (uint8_t)k;
        }
        e = b;
    }
    return n;
}

namespace {

bool is_r2ur(const SInst &s) { return s.sc.sop == SOP_SM73_R2UR; }

}

void ur_nc_step(const SInst *in, int n, DepsCtx &ctx) {
    for (int i = 0; i < n; i++) {
        const SInst &s = in[i];
        for (int k = 0; k < s.nregs; k++) {
            const SReg &r = s.regs[k];
            if (!r.def || r.no < 0) continue;
            bool nc = is_r2ur(s);
            if (r.cls == RC_UR && r.no < 128) {
                uint64_t b = 1ull << (r.no & 63);
                ctx.ur_nc[r.no >> 6] = nc ? ctx.ur_nc[r.no >> 6] | b : ctx.ur_nc[r.no >> 6] & ~b;
            } else if (r.cls == RC_UP && r.no < 8) {
                uint8_t b = (uint8_t)(1u << r.no);
                ctx.up_nc = nc ? ctx.up_nc | b : ctx.up_nc & ~b;
            }
        }
    }
}

bool dont_schedule(const SInst &s) {
    init_ops();
    return is_flow_control(s);
}

void calc_deps(const SInst *in, int n, const DepsCtx &ctx, BlockDeps *out) {
    init_ops();
    Graph g;
    g.made.assign(n, std::vector<DepEdge>());
    g.ref.assign(n, 0);
    out->prohibit_reuse.assign(n, 0);
    RegMap rm;
    rm.in = in;
    rm.g = &g;
    rm.prohibit = &out->prohibit_reuse;
    rm.init(n);
    rm.count_pred_defs(n);
    MemDep md;
    md.g = &g;
    md.init();
    md.addrRefs.assign(n, 0);
    for (int i = 0; i < n; i++) md.addrRefs[i] = addr_refs(in, n, i, ctx);

    md.urDep.assign(n, 0);
    {
        uint64_t urDef[2] = {ctx.ur_nc[0], ctx.ur_nc[1]};
        uint8_t upDef = ctx.up_nc;
        for (int i = 0; i < n; i++) {
            const SInst &s = in[i];
            for (int k = 0; k < s.nregs; k++) {
                const SReg &r = s.regs[k];
                if (r.cls != RC_UR && r.cls != RC_UP) continue;
                if (r.def) md.urDep[i] = 1;
                else if (r.cls == RC_UR && r.no >= 0 && r.no < 128 && (urDef[r.no >> 6] >> (r.no & 63) & 1)) md.urDep[i] = 1;
                else if (r.cls == RC_UP && r.no >= 0 && r.no < 8 && (upDef >> r.no & 1)) md.urDep[i] = 1;
            }
            for (int k = 0; k < s.nregs; k++) {
                const SReg &r = s.regs[k];
                if (!r.def || r.no < 0) continue;
                if (r.cls == RC_UR && r.no < 128) urDef[r.no >> 6] |= 1ull << (r.no & 63);
                if (r.cls == RC_UP && r.no < 8) upDef |= (uint8_t)(1u << r.no);
            }
        }
    }
    std::vector<int> stateDef(1024 + 2, -1);
    std::vector<int> stateTouched;
    auto stateKey = [](int no) { return (no + 1) & 1023; };

    bool seenDso = false;
    for (int i = 0; i < n; i++) {
        const SInst &s = in[i];
        rm.idx[i] = i + 1;
        bool lastInBlock = i == n - 1;
        if (dont_schedule(s) || (is_nop(s) && lastInBlock)) seenDso = true;
        if (seenDso) g.ref[i]++;
        bool seenState = false;
        uint8_t ord[SINST_MAX_REGS];
        rev_regs(s, ord);
        for (int q = 0; q < s.nregs; q++) {
            const SReg &r = s.regs[ord[q]];
            if (r.cls <= RC_ACTIVEM) {
                if (r.def) rm.output(i, r.cls, r.no);
                else rm.flow(i, r.cls, r.no);
            }
            seenState |= r.cls == RC_STATE;
        }
        if (seenState) {
            for (int q = 0; q < s.nregs; q++) {
                const SReg &r = s.regs[ord[q]];
                if (r.cls != RC_STATE) continue;
                int &d = stateDef[stateKey(r.no)];
                if (!r.def) {
                    if (d >= 0) g.add(d, i, DEP_FLOW, RC_STATE, MEMDOM_NONE);
                } else {
                    if (d < 0) stateTouched.push_back(stateKey(r.no));
                    d = i;
                }
            }
        }
        MemDepInfo deps[32];
        int nd = get_mem_dep(s, i, lastInBlock, ctx, md, deps);
        for (int k = 0; k < nd; k++) {
            if (deps[k].op == MO_READ) md.do_read(deps[k]);
            else md.do_write(deps[k]);
            md.alias_deps(deps[k]);
        }
        if (s.sc.sop == SOP_SM70_BSSY) {
            if (md.psync >= 0) g.add(md.psync, i, DEP_ORDER, REGCLASS_NONE, MEMDOM_NONE);
            md.psync = i;
        }
    }
    for (int k : stateTouched) stateDef[k] = -1;
    stateTouched.clear();

    rm.init(n);
    int lastTex = -1;
    for (int i = n - 1; i >= 0; i--) {
        const SInst &s = in[i];
        rm.idx[i] = n - i;
        bool seenState = false;
        uint8_t ord[SINST_MAX_REGS];
        rev_regs(s, ord);
        for (int q = 0; q < s.nregs; q++) {
            const SReg &r = s.regs[ord[q]];
            if (r.cls <= RC_R) {
                if (r.def) rm.update(i, r.cls, r.no);
                else rm.anti(i, r.cls, r.no);
            }
            seenState |= r.cls == RC_STATE;
        }
        if (s.sc.flags & GF_IS_TEX_BATCH) lastTex = i;
        else if (lastTex >= 0 && s.sc.sop == SOP_SM70_KILL) g.add(i, lastTex, DEP_ANTI, REGCLASS_NONE, MEMDOM_NONE);
        if (seenState) {
            for (int q = 0; q < s.nregs; q++) {
                const SReg &r = s.regs[ord[q]];
                if (r.cls != RC_STATE) continue;
                int &d = stateDef[stateKey(r.no)];
                if (d >= 0 && i < d) g.add(i, d, DEP_ANTI, RC_STATE, MEMDOM_NONE);
                if (r.def) {
                    if (d < 0) stateTouched.push_back(stateKey(r.no));
                    d = i;
                }
            }
        }
    }

    out->out.assign(n, std::vector<DepEdge>());
    for (int i = 0; i < n; i++) out->out[i].assign(g.made[i].rbegin(), g.made[i].rend());
    out->ref = g.ref;
}

}
}
}
