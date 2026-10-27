
#include "../uber.h"
#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <string>

#include "sched/classify.h"
#include "sched/issue.h"
#include "sched/phase_a.h"
#include "sched/phase_b.h"
#include "sched/validate.h"

namespace ub {

namespace ss = sm86::sched;

static const int SB_WRITE = 0;
static const int SB_READ = 1;
static const u8 WAIT_ALL = 0x3f;
static const int STALL_MAX = 15;

static void set_ctl86(sm86::Inst &in) {
    sm86::ClassInfo ci = sm86::info(in.cls);
    bool varlat = (ci.flags & sm86::CI_VARLAT) != 0;
    bool varsrc = (ci.flags & sm86::CI_VARLAT_SRC) != 0;

    for (const char *nm : {"reuse_src_a", "reuse_src_b", "reuse_src_c"}) {
        int vi = sm86::val_index(in.cls, nm);
        if (vi >= 0) sm86::set(in, vi, 0);
    }

    int bt = sm86::val_index(in.cls, "batch_t");
    if (bt >= 0) sm86::set(in, bt, 0);

    int ui = sm86::val_index(in.cls, "usched_info");
    if (ui >= 0) sm86::set(in, ui, STALL_MAX);

    sm86::Ctl c = sm86::ctl_get(in.w);
    c.pm = 0;
    c.wr = varlat ? SB_WRITE : 7;
    c.rd = varsrc ? SB_READ : 7;
    c.wait = WAIT_ALL;
    in.w = sm86::ctl_set(in.w, c);
}

void phase_b86(std::vector<u8> &bc, u32 co) {
    for (u32 off = Sm86::kCode; off + 16 <= co; off += 16) {
        Sm86::Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        if (!w.lo && !w.hi) continue;
        sm86::Inst in;
        if (!sm86::decode(w, &in)) continue;
        set_ctl86(in);
        std::memcpy(bc.data() + off, &in.w.lo, 8);
        std::memcpy(bc.data() + off + 8, &in.w.hi, 8);
    }
}

int shader_type86(const std::vector<u8> &bc) {
    if (bc.size() < 4) return sm86::ST_UNKNOWN;
    u32 w0 = sm86x::rd32(bc, 0);
    static const int types[] = {sm86::ST_UNKNOWN, sm86::ST_VSB, sm86::ST_TI, sm86::ST_TS,
                                sm86::ST_GS, sm86::ST_PS};
    unsigned t = (w0 >> 10) & 15;
    return t >= 1 && t <= 5 ? types[t] : sm86::ST_UNKNOWN;
}

void code_words86(const std::vector<u8> &bc, u32 co, std::vector<Sm86::Word> &code,
                  std::string &consts) {
    code.clear();
    for (u32 off = Sm86::kCode; off + 16 <= co && off + 16 <= bc.size(); off += 16) {
        Sm86::Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        code.push_back(w);
    }
    while (!code.empty() && Sm86::empty(code.back())) code.pop_back();
    consts.assign(bc.begin() + (long)std::min((size_t)co, bc.size()), bc.end());
}

namespace {

enum { OK_NONE = 0, OK_READ = 1, OK_FIXED = 2 };

enum { WK_MASK_READ = 1, WK_MASK_WRITE = 2, WK_UR_READ = 4, WK_UR_WRITE = 8 };

struct OrderKinds {
    std::vector<u8> mem, warp;
    std::vector<char> xlane;
};

const OrderKinds &order_kinds() {
    static OrderKinds K;
    if (!K.mem.empty()) return K;
    const OpSets &T = Sm86::sets();
    int n = sm86::nops();
    std::vector<u8> &k = K.mem;
    k.assign((size_t)n, OK_NONE);
    K.warp.assign((size_t)n, 0);
    K.xlane.assign((size_t)n, 0);
    for (int op = 0; op < n; op++) if (T.side_effect[(size_t)op]) k[(size_t)op] = OK_FIXED;
    for (const char *nm : {"BMOV", "B2R", "R2B", "R2UR", "S2UR", "S2R", "BAR", "MEMBAR", "LEPC"}) {
        int op = sm86::op_id(nm);
        if (op >= 0) k[(size_t)op] = OK_FIXED;
    }

    for (const char *nm : {"BSSY", "YIELD", "DEPBAR", "NOP", "SHFL", "FSWZADD", "VOTE", "VOTEU",
                           "MATCH", "REDUX"}) {
        int op = sm86::op_id(nm);
        if (op >= 0) k[(size_t)op] = OK_NONE;
    }

    for (const char *nm : {"TEX", "TLD", "TLD4", "TMML", "TXQ", "TXD", "FOOTPRINT", "GATHER",
                           "LD", "LDG", "LDL", "LDS", "LDSM", "ALD", "SULD", "ISBERD"}) {
        int op = sm86::op_id(nm);
        if (op >= 0 && k[(size_t)op] == OK_NONE) k[(size_t)op] = OK_READ;
    }
    for (const char *nm : {"SHFL", "FSWZADD", "VOTE", "VOTEU", "MATCH", "REDUX", "BSSY", "BMOV",
                           "BREAK"}) {
        int op = sm86::op_id(nm);
        if (op >= 0) K.warp[(size_t)op] |= WK_MASK_READ;
    }
    for (const char *nm : {"KILL", "WARPSYNC", "BAR", "YIELD", "BREAK", "BMOV"}) {
        int op = sm86::op_id(nm);
        if (op < 0) continue;
        K.warp[(size_t)op] |= WK_MASK_WRITE;
        if (strcmp(nm, "KILL")) K.warp[(size_t)op] |= WK_UR_WRITE;
    }
    for (const char *nm : {"SHFL", "VOTE", "VOTEU", "MATCH", "REDUX"}) {
        int op = sm86::op_id(nm);
        if (op >= 0) K.xlane[(size_t)op] = 1;
    }
    return K;
}

struct OrderFacts {
    sm86::RSet86 w, r;
    u8 kind = OK_NONE;
    u8 warp = 0;
    bool xlane = false;
    bool pinned = false;
    int gkey = -1;
    int ginv = 0;

    int alo = -1, ahi = -1;
    u8 attr = 0;

    int lbase = -1;
    long long llo = 0, lhi = 0;
};
enum { ATTR_NONE = 0, ATTR_STORE = 1, ATTR_LOAD_OUT = 2, ATTR_LOAD_IN = 3 };

long long value_of(const sm86::Inst &in, const char *nm, long long dflt) {
    int v = sm86::val_index(in.cls, nm);
    return v >= 0 ? (long long)sm86::get(in, v) : dflt;
}

int local_bytes(const sm86::Inst &in, const char *data) {
    sm86::Inst t = in;
    int v = sm86::val_index(t.cls, data);
    if (v < 0 || !sm86::set(t, v, 0)) return -1;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(t, o, sm86::MAX_OPNDS);
    for (int k = 0; k < n; k++)
        if (o[k].val == v) return o[k].nregs ? 4 * o[k].nregs : -1;
    return -1;
}

OrderFacts order_facts(const Sm86::Word &q) {
    OrderFacts f;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) { f.kind = OK_FIXED; f.pinned = true; return f; }
    sm86::RSet86 d, md;
    sm86::def_use_split(in, &d, &md, &f.r);
    f.w = d;
    f.w.unite(md);
    const OrderKinds &K = order_kinds();
    f.kind = K.mem[(size_t)in.op];
    f.warp = K.warp[(size_t)in.op];
    f.xlane = K.xlane[(size_t)in.op] != 0;
    for (int k = sm86::KEY_UP; k < sm86::KEY_COUNT; k++)
        if (k < sm86::KEY_B || k >= sm86::KEY_UR)
            if (f.w.has(k)) f.warp |= WK_UR_READ;
    static const int bsync = sm86::op_id("BSYNC"), ast = sm86::op_id("AST"),
                     ald = sm86::op_id("ALD");
    f.pinned = Sm86::cf_kind(in.op) != C_OTHER || in.op == bsync;
    bool uni, neg;
    int g = sm86::guard(in, &uni, &neg);
    if (g != 7) {
        f.gkey = uni ? sm86::KEY_UP + g : sm86::KEY_P + g;
        f.ginv = neg ? 1 : 0;
    }
    if ((in.op == ast || in.op == ald) && value_of(in, "Ra", -1) == RZ &&
        value_of(in, "Rc", RZ) == RZ) {
        long long off = value_of(in, "Ra_offset", -1), sz = value_of(in, "sz", -1);
        if (off >= 0 && sz >= 0) {
            f.alo = (int)off;
            f.ahi = (int)(off + 4 * (sz + 1));
            f.attr = in.op == ast ? ATTR_STORE
                                  : value_of(in, "io", 1) == 0 ? ATTR_LOAD_IN : ATTR_LOAD_OUT;
        }
    }
    static const int ldl = sm86::op_id("LDL"), stl = sm86::op_id("STL");
    if (in.op == ldl || in.op == stl) {
        long long base = value_of(in, "Ra", -1), off = value_of(in, "Ra_offset", 0);
        int nb = local_bytes(in, in.op == ldl ? "Rd" : "Rb");
        if (base >= 0 && nb > 0) {
            f.lbase = (int)base;
            f.llo = off;
            f.lhi = off + nb;
        }
    }
    return f;
}

bool warp_conflict(const OrderFacts &a, const OrderFacts &c) {
    auto meet = [](u8 x, u8 y) {
        return ((x & WK_MASK_READ) && (y & WK_MASK_WRITE)) || ((x & WK_UR_READ) && (y & WK_UR_WRITE));
    };
    return meet(a.warp, c.warp) || meet(c.warp, a.warp);
}

bool mem_conflict(const OrderFacts &a, const OrderFacts &c, bool shared_isb) {
    if (a.kind == OK_NONE || c.kind == OK_NONE) return false;
    if (a.kind == OK_READ && c.kind == OK_READ) return false;

    if (a.attr && c.attr && (a.attr == ATTR_STORE || c.attr == ATTR_STORE)) {
        if (a.attr == ATTR_LOAD_IN || c.attr == ATTR_LOAD_IN) return shared_isb;
        return !(a.ahi <= c.alo || c.ahi <= a.alo);
    }

    if (a.lbase >= 0 && a.lbase == c.lbase) return !(a.lhi <= c.llo || c.lhi <= a.llo);
    return true;
}

void check_order(const std::vector<Sm86::Word> &in, const std::vector<int> &starts,
                 const std::vector<int> &perm, bool shared_isb) {
    int n = (int)in.size();
    std::vector<int> pos((size_t)n, -1);
    for (int k = 0; k < n; k++) pos[(size_t)perm[(size_t)k]] = k;
    std::vector<OrderFacts> f((size_t)n);
    for (int k = 0; k < n; k++) f[(size_t)k] = order_facts(in[(size_t)k]);
    for (size_t b = 0; b < starts.size(); b++) {
        int s0 = starts[b], s1 = b + 1 < starts.size() ? starts[b + 1] : n;
        for (int i = s0; i < s1; i++) {
            int pi = pos[(size_t)i];
            if (pi < s0 || pi >= s1) fail("sm86 schedule: slot %d left its block", i);
            if (f[(size_t)i].pinned && pi != i)
                fail("sm86 schedule: flow control at %d moved to %d", i, pi);
            for (int j = i + 1; j < s1; j++) {
                if (pos[(size_t)j] > pi) continue;
                const OrderFacts &a = f[(size_t)i], &c = f[(size_t)j];
                if (a.pinned || c.pinned)
                    fail("sm86 schedule: Phase A moved slot %d across the flow control at %d",
                         a.pinned ? j : i, a.pinned ? i : j);

                bool warp = warp_conflict(a, c);
                if (!warp && a.gkey >= 0 && a.gkey == c.gkey && a.ginv != c.ginv &&
                    !a.w.has(a.gkey) && !c.w.has(a.gkey) && !a.xlane && !c.xlane)
                    continue;
                bool regs = a.w.intersects(c.r) || a.w.intersects(c.w) || a.r.intersects(c.w);
                bool mem = mem_conflict(a, c, shared_isb);
                if (regs || mem || warp)
                    fail("sm86 schedule: Phase A put slot %d (%s) ahead of slot %d (%s), which "
                         "it depends on through %s (guards %d/%d, %d/%d; attributes %d..%d, "
                         "%d..%d)", j, Sm86::op_name(Sm86::decode_op(in[(size_t)j])), i,
                         Sm86::op_name(Sm86::decode_op(in[(size_t)i])),
                         regs ? "a register" : mem ? "memory" : "the active mask", c.gkey,
                         c.ginv, a.gkey, a.ginv, c.alo, c.ahi, a.alo, a.ahi);
            }
        }
    }
}

void phase_a86(std::vector<Sm86::Word> &in, ss::Cfg &cfg, int st) {
    int n = (int)in.size();
    ss::SbProg p;
    if (!ss::sb_from_words(in.data(), n, cfg, st, &p))
        fail("sm86 schedule: the blocks do not cover the code");

    std::vector<ss::SInst> prog((size_t)n);
    std::vector<char> seen((size_t)n, 0);
    for (const ss::SbNode &x : p.nodes) {
        if (x.kind != ss::SBN_INST || x.s.number < 0 || x.s.number >= n) continue;
        prog[(size_t)x.s.number] = x.s;
        seen[(size_t)x.s.number] = 1;
    }
    for (int k = 0; k < n; k++)
        if (!seen[(size_t)k]) fail("sm86 schedule: word %d is in no block", k);
    ss::DepsCtx ctx;
    ctx.compute = cfg.compute;
    ctx.shared_isb = cfg.shared_isb;
    for (const ss::SInst &s : prog)
        if (s.ok && s.sc.sop == ss::SOP_SM70_KILL) ctx.has_kil = true;
    ss::IssueMachine m;
    std::vector<int> perm;
    ss::phase_a_program(prog, cfg.starts, ctx, m, perm);
    if ((int)perm.size() != n) fail("sm86 schedule: Phase A lost instructions");
    check_order(in, cfg.starts, perm, cfg.shared_isb);
    std::vector<Sm86::Word> w2((size_t)n);
    std::vector<int> rel2((size_t)n, -1);
    for (int k = 0; k < n; k++) {
        size_t o = (size_t)perm[(size_t)k];
        w2[(size_t)k] = in[o];
        if (o < cfg.rel.size()) rel2[(size_t)k] = cfg.rel[o];
    }
    in.swap(w2);
    cfg.rel.swap(rel2);
}

int copy_pipes86(std::vector<Sm86::Word> &in, const ss::Cfg &cfg, int st) {
    enum { P_ALU, P_FMA, P_2X, P_NONE };
    struct Info {
        int pipe = P_NONE, unit = -1, lat = 0, nd = 0, nu = 0;
        bool var = false;
        int d[8], u[16];
    };
    const int n = (int)in.size();
    std::vector<Info> inf((size_t)n);
    auto describe = [&](int k) {
        Info &I = inf[(size_t)k];
        I = Info();
        sm86::Inst x;
        ss::SchedClass c;
        if (!sm86::decode(in[(size_t)k], &x) || !ss::classify(x, st, &c)) {
            I.var = true;
            return;
        }
        uint32_t r = c.res;
        I.pipe = (r >> ss::RES_2XFMA) & 1 ? P_2X : (r >> ss::RES_FMA) & 1 ? P_FMA
                 : (r >> ss::RES_ALU) & 1 ? P_ALU : P_NONE;
        I.unit = c.unit == ss::UV_COUPLED_ALU || c.unit == ss::UV_COUPLED_FMA ? c.unit : -1;
        I.lat = c.latency;
        I.var = (c.flags & ss::GF_IS_LONG_LATENCY) || I.unit < 0;
        sm86::Operand o[sm86::MAX_OPNDS];
        int m = sm86::operands(x, o, sm86::MAX_OPNDS);
        for (int j = 0; j < m; j++) {
            if (o[j].kind != sm86::O_GPR) continue;
            for (int g = 0; g < o[j].nregs; g++) {
                int reg = o[j].reg + g;
                if (reg >= RZ) continue;
                if ((o[j].role == sm86::R_DEF || o[j].role == sm86::R_DEFUSE) && I.nd < 8)
                    I.d[I.nd++] = reg;
                if ((o[j].role == sm86::R_USE || o[j].role == sm86::R_DEFUSE) && I.nu < 16)
                    I.u[I.nu++] = reg;
            }
        }
    };
    for (int k = 0; k < n; k++) describe(k);

    int flips = 0;
    for (size_t b = 0; b < cfg.starts.size(); b++) {
        int s = cfg.starts[b], e = b + 1 < cfg.starts.size() ? cfg.starts[b + 1] : n;
        int ready[RZ], from[RZ];
        for (int r = 0; r < RZ; r++) ready[r] = 0, from[r] = -1;
        int now = 0, busy[3] = {0, 0, 0}, disp[2] = {0, 0};
        auto issue_at = [&](const Info &I, int pipe, int unit) {
            int t = now;
            for (int j = 0; j < I.nu; j++) {
                int r = I.u[j];
                t = std::max(t, ready[r] + (from[r] >= 0 && unit >= 0 && from[r] != unit));
            }
            if (pipe != P_NONE) t = std::max({t, busy[pipe], disp[pipe == P_ALU ? 0 : 1]});
            return t;
        };
        for (int k = s; k < e && k < n; k++) {
            Info &I = inf[(size_t)k];
            bool imad;
            int kind = I.nd == 1 ? Sm86::copy_form(in[(size_t)k], &imad) : -1;
            if (kind >= 0) {
                int unit = -1;
                for (int j = k + 1; j < e && j < n && unit < 0; j++) {
                    const Info &J = inf[(size_t)j];
                    bool rd = false, wr = false;
                    for (int q = 0; q < J.nu; q++) rd |= J.u[q] == I.d[0];
                    for (int q = 0; q < J.nd; q++) wr |= J.d[q] == I.d[0];
                    if (rd) unit = J.unit >= 0 ? J.unit : -2;
                    else if (wr) break;
                }
                auto score = [&](int pipe, int u) {
                    return issue_at(I, pipe, u) + (unit >= 0 && unit != u);
                };
                int sa = score(P_ALU, ss::UV_COUPLED_ALU), sf = score(P_FMA, ss::UV_COUPLED_FMA);
                bool want = imad ? sf <= sa : sf < sa;
                if (want != imad) {
                    Sm86::Word f = Sm86::copy_flip(in[(size_t)k]);
                    if (!(f == in[(size_t)k])) {
                        in[(size_t)k] = f;
                        describe(k);
                        flips++;
                    }
                }
            }
            int t = issue_at(I, I.pipe, I.unit);
            if (I.pipe != P_NONE) {
                busy[I.pipe] = t + (I.pipe == P_2X ? 1 : 2);
                disp[I.pipe == P_ALU ? 0 : 1] = t + 1;
            }
            for (int j = 0; j < I.nd; j++) {
                ready[I.d[j]] = I.var ? t : t + I.lat;
                from[I.d[j]] = I.var ? -1 : I.unit;
            }
            now = t + 1;
        }
    }
    return flips;
}

int stall_sum86(const std::vector<Sm86::Word> &w) {
    int sum = 0;
    for (const Sm86::Word &x : w)
        if (!Sm86::empty(x)) sum += sm86::ctl_get(x).stall;
    return sum;
}

}

void schedule86(std::vector<u8> &bc, std::vector<u8> &ct) {
    u32 co = Sm86::const_off(ct);
    std::vector<Sm86::Word> code;
    std::string consts;
    code_words86(bc, co, code, consts);
    if (code.empty()) fail("sm86 schedule: no code");

    std::vector<Sm86::Word> in;
    ss::Cfg cfg;
    std::vector<int> keep;
    if (!ss::strip_phase_b(code.data(), (int)code.size(), consts, &in, &cfg, &keep))
        fail("sm86 schedule: the code does not read back into blocks");

    for (const std::vector<int> &j : cfg.jmx)
        if (!j.empty()) fail("sm86 schedule: a computed jump survived");
    int st = shader_type86(bc);
    cfg.compute = false;
    cfg.shared_isb = bc.size() >= 4 && ((bc[3] >> 1) & 1);

    phase_a86(in, cfg, st);

    std::vector<Sm86::Word> alt = in;
    ss::Cfg cfg2 = cfg;
    int flips = copy_pipes86(alt, cfg2, st);
    if (flips) phase_a86(alt, cfg2, st);
    std::vector<Sm86::Word> out;
    for (int pass = 0; pass < (flips ? 2 : 1); pass++) {
        ss::SbStats stats;
        stats.regroupLowered = true;
        stats.beyondFromLowered = true;
        std::vector<Sm86::Word> o;
        std::vector<int> map;
        const std::vector<Sm86::Word> &src = pass ? alt : in;
        if (ss::phase_b(src.data(), (int)src.size(), pass ? cfg2 : cfg, st, o, map, &stats) != 0)
            fail("sm86 schedule: Phase B refused the program");
        if (stats.assertHits) fail("sm86 schedule: Phase B met input the compiler would reject");
        if (!pass || stall_sum86(o) < stall_sum86(out)) out.swap(o);
    }

    Sm86::fix_calls(out);
    std::vector<u8> obc;
    Sm86::assemble(bc, co, out, obc, ct);
    bc.swap(obc);
}

int validate86(const std::vector<u8> &bc, u32 co, int *first) {
    std::vector<Sm86::Word> code;
    std::string consts;
    code_words86(bc, co, code, consts);
    std::vector<ss::Hazard> hz;
    int n = ss::validate(code.data(), (int)code.size(), consts, shader_type86(bc), &hz);
    if (first) *first = hz.empty() ? -1 : hz[0].at;
    return n;
}

int issue_cycles86(const std::vector<u8> &bc, u32 co) {
    int sum = 0;
    for (u32 off = Sm86::kCode; off + 16 <= co; off += 16) {
        Sm86::Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        if (!w.lo && !w.hi) continue;
        sm86::Ctl c = sm86::ctl_get(w);
        sum += c.stall;
    }
    return sum;
}

int inst_class86(const std::vector<u8> &bc, u32 co, int n, u8 *cls) {
    int k = 0;
    for (u32 off = Sm86::kCode; off + 16 <= co && k < n; off += 16, k++) {
        Sm86::Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        u8 v = 0;
        sm86::Inst in;
        if (sm86::decode(w, &in)) {
            sm86::ClassInfo ci = sm86::info(in.cls);
            if (ci.flags & sm86::CI_VARLAT) v |= 1;
            sm86::Ctl c = sm86::ctl_get(w);
            if (c.rd != 7) v |= 2;
            if (c.wr != 7) v |= 4;
        }
        cls[k] = v;
    }
    return k;
}

}
