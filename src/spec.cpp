
#include "spec.h"
#include <cmath>

namespace ub {

bool g_cse_mov32i = false;

bool g_fmac = false;

bool g_fmac_all = false;

static inline int32_t s32(u32 v) { return (int32_t)v; }

static inline float f32_of(u32 u) { float f; std::memcpy(&f, &u, 4); return f; }
static inline u32 bits_of(float f) { u32 u; std::memcpy(&u, &f, 4); return u; }

static bool icmp_op(int op, u32 a, u32 b, bool sgn, bool *out) {
    if (sgn) {
        int32_t x = s32(a), y = s32(b);
        switch (op) {
        case 1: *out = x < y; return true;
        case 2: *out = x == y; return true;
        case 3: *out = x <= y; return true;
        case 4: *out = x > y; return true;
        case 5: *out = x != y; return true;
        case 6: *out = x >= y; return true;
        }
    } else {
        switch (op) {
        case 1: *out = a < b; return true;
        case 2: *out = a == b; return true;
        case 3: *out = a <= b; return true;
        case 4: *out = a > b; return true;
        case 5: *out = a != b; return true;
        case 6: *out = a >= b; return true;
        }
    }
    return false;
}

static Tri bop(int op, Tri c, Tri pv) {
    if (op == 0) {
        if (c == TRI_F || pv == TRI_F) return TRI_F;
        if (c == TRI_T && pv == TRI_T) return TRI_T;
        return TRI_U;
    }
    if (op == 1) {
        if (c == TRI_T || pv == TRI_T) return TRI_T;
        if (c == TRI_F && pv == TRI_F) return TRI_F;
        return TRI_U;
    }
    if (op == 2) {
        if (c == TRI_U || pv == TRI_U) return TRI_U;
        return (c != pv) ? TRI_T : TRI_F;
    }
    return TRI_U;
}

static inline Tri notTri(Tri c) { return c == TRI_U ? TRI_U : (c ? TRI_F : TRI_T); }

static float ftz(float x) {
    if (x != 0.0f && std::fabs(x) < 1.1754943508222875e-38f)
        return std::copysign(0.0f, x);
    return x;
}

static bool fcmp_op(int op, float a, float b, bool *out) {
    bool nan = std::isnan(a) || std::isnan(b);
    if (op == 0) { *out = false; return true; }
    if (op == 15) { *out = true; return true; }
    if (op == 7) { *out = !nan; return true; }
    if (op == 8) { *out = nan; return true; }
    bool unordered = op >= 9;
    int base = unordered ? op - 8 : op;
    if (nan) { *out = unordered; return true; }
    switch (base) {
    case 1: *out = a < b; return true;
    case 2: *out = a == b; return true;
    case 3: *out = a <= b; return true;
    case 4: *out = a > b; return true;
    case 5: *out = a != b; return true;
    case 6: *out = a >= b; return true;
    }
    return false;
}

struct FsetpF {
    int d0, d1, ra, absa, nega, absb, negb, pc, pcinv, bop_, ftz_, cmp, rd, bf, cc;
};
static FsetpF fsetp_fields(u64 q) {
    FsetpF f{};
    f.d0 = (int)((q >> 3) & 7); f.d1 = (int)(q & 7);
    f.ra = (int)((q >> 8) & 0xFF);
    f.absa = (int)((q >> 7) & 1); f.nega = (int)((q >> 43) & 1);
    f.absb = (int)((q >> 44) & 1); f.negb = (int)((q >> 6) & 1);
    f.pc = (int)((q >> 39) & 7); f.pcinv = (int)((q >> 42) & 1);
    f.bop_ = (int)((q >> 45) & 3); f.ftz_ = (int)((q >> 47) & 1);
    f.cmp = (int)((q >> 48) & 0xF);
    return f;
}
static FsetpF fset_fields(u64 q) {
    FsetpF f{};
    f.rd = (int)(q & 0xFF); f.ra = (int)((q >> 8) & 0xFF);
    f.absa = (int)((q >> 54) & 1); f.nega = (int)((q >> 43) & 1);
    f.absb = (int)((q >> 44) & 1); f.negb = (int)((q >> 53) & 1);
    f.pc = (int)((q >> 39) & 7); f.pcinv = (int)((q >> 42) & 1);
    f.bop_ = (int)((q >> 45) & 3); f.bf = (int)((q >> 52) & 1);
    f.ftz_ = (int)((q >> 55) & 1); f.cmp = (int)((q >> 48) & 0xF);
    f.cc = (int)((q >> 47) & 1);
    return f;
}
struct FmnmxF { int rd, ra, absa, nega, absb, negb, pc, pcinv, ftz_, cc; };
static FmnmxF fmnmx_fields(u64 q) {
    FmnmxF f{};
    f.rd = (int)(q & 0xFF); f.ra = (int)((q >> 8) & 0xFF);
    f.absa = (int)((q >> 46) & 1); f.nega = (int)((q >> 45) & 1);
    f.absb = (int)((q >> 49) & 1); f.negb = (int)((q >> 48) & 1);
    f.pc = (int)((q >> 39) & 7); f.pcinv = (int)((q >> 42) & 1);
    f.ftz_ = (int)((q >> 44) & 1); f.cc = (int)((q >> 47) & 1);
    return f;
}
struct PsetF { int rd, pa, pain, pb, pbin, pc, pcin, inner, outer, bf; };
static PsetF pset_fields(u64 q) {
    PsetF f{};
    f.rd = (int)(q & 0xFF);
    f.pa = (int)((q >> 12) & 7); f.pain = (int)((q >> 15) & 1);
    f.pb = (int)((q >> 29) & 7); f.pbin = (int)((q >> 32) & 1);
    f.pc = (int)((q >> 39) & 7); f.pcin = (int)((q >> 42) & 1);
    f.inner = (int)((q >> 24) & 3); f.outer = (int)((q >> 45) & 3);
    f.bf = (int)((q >> 44) & 1);
    return f;
}

struct XShape { u64 key; int sela, selb, psl, mrg, cbcc; };
static const XShape XMAD_SHAPES[] = {
    {0x3600000000000000ull, 0, 0, 0, 0, 0},
    {0x3620001000000000ull, 1, 0, 1, 0, 0},
    {0x4e00000000000000ull, 0, 0, 0, 0, 0},
    {0x4f10000000000000ull, 0, 1, 0, 1, 0},
    {0x5b30001800000000ull, 1, 1, 1, 0, 1},
};

bool xmad_shape(u64 q, int *sela, int *selb, int *psl, int *mrg, int *cbcc) {
    int f = srcb_form(q);
    u64 srcb;
    if (f == FORM_IMM) srcb = (u64)0xFFFFull << 20;
    else if (f == FORM_CBUF) srcb = (u64)0x7FFFFull << 20;
    else srcb = (u64)0xFFull << 20;
    u64 m = 0xFFull | (0xFFull << 8) | (0xFull << 16) | srcb | (0xFFull << 39);
    u64 k = q & ~m;
    for (const XShape &s : XMAD_SHAPES)
        if (s.key == k) {
            *sela = s.sela; *selb = s.selb; *psl = s.psl; *mrg = s.mrg;
            *cbcc = s.cbcc;
            return true;
        }
    return false;
}

u32 xmad_value(u32 sa, int hia, u32 sb, int hib, u32 sc, int psl, int mrg,
               int cbcc) {
    u32 a = hia ? ((sa >> 16) & 0xFFFF) : (sa & 0xFFFF);
    u32 b = hib ? ((sb >> 16) & 0xFFFF) : (sb & 0xFFFF);
    u32 r = (a * b) & M32;
    if (psl) r = (r << 16) & M32;
    u32 c = sc & M32;
    if (cbcc) c = (c + ((sb & 0xFFFF) << 16)) & M32;
    r = (r + c) & M32;
    if (mrg) r = (r & 0xFFFF) | (((sb & 0xFFFF) << 16) & M32);
    return r & M32;
}

void Spec::init(const Program &prog, int opt_bank,
                const std::vector<int> &exit_live, bool lm_dse_, bool cbfold_,
                int folds_, bool texrw_) {
    const OpSets &T = S();
    p = &prog;
    bank = opt_bank;
    fold_blob = true;
    folds = folds_;
    texrw = texrw_;
    lm_dse = lm_dse_;
    copyprop = true;
    lmfwd = true && copyprop;
    cbfold = cbfold_ && copyprop;
    cse = true && copyprop;
    fix_maydef = true;

    int n = prog.n;
    exit_mask.clear();
    for (int r : exit_live) exit_mask.set(r);

    cat.assign((size_t)n, C_OTHER);
    tgt.assign((size_t)n, -1);
    dd.assign((size_t)n, {});
    pnum.assign((size_t)n, 0);
    pinv.assign((size_t)n, 0);
    nopred.assign((size_t)n, 0);
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];
        int c = C_OTHER;
        if (nm == T.O_Ssy) c = C_SSY;
        else if (nm == T.O_Pbk) c = C_PBK;
        else if (nm == T.O_Pcnt) c = C_PCNT;
        else if (nm == T.O_Sync) c = C_SYNC;
        else if (nm == T.O_Brk) c = C_BRK;
        else if (nm == T.O_Cont) c = C_CONT;
        else if (nm == T.O_Bra || nm == T.O_Jmp) c = C_BRA;
        else if (nm == T.O_Brx || nm == T.O_Jmx) c = C_BRX;
        else if (nm == T.O_Exit || nm == T.O_Ret) c = C_EXIT;
        cat[(size_t)i] = (int8_t)c;
        tgt[(size_t)i] = prog.target(i);
        RSet u = prog.defs[i];
        u.unite(prog.maydefs[i]);
        std::vector<int> lst;
        u.list(lst);
        dd[(size_t)i].assign(lst.begin(), lst.end());
        pnum[(size_t)i] = (int8_t)((prog.q[i] >> 16) & 7);
        pinv[(size_t)i] = (int8_t)((prog.q[i] >> 19) & 1);
        nopred[(size_t)i] = (char)T.no_pred[(size_t)nm];
    }

    def_mask.assign((size_t)n, Mask());
    dall_mask.assign((size_t)n, Mask());
    use_list.assign((size_t)n, {});
    maydef_set.assign((size_t)n, {});
    for (int i = 0; i < n; i++) {
        prog.defs[i].to_mask(def_mask[(size_t)i]);
        dall_mask[(size_t)i] = def_mask[(size_t)i];
        prog.maydefs[i].to_mask(dall_mask[(size_t)i]);
        prog.uses[i].list(use_list[(size_t)i]);
        prog.maydefs[i].list(maydef_set[(size_t)i]);
    }

    copy_src.assign((size_t)n, -1);
    for (int i = 0; i < n; i++) {
        if (prog.op[i] != T.O_Mov) continue;
        u64 q = prog.q[i];
        if (srcb_form(q) != FORM_REG) continue;
        int d = (int)(q & 0xFF), s = (int)((q >> 20) & 0xFF);
        if (d == RZ || s == RZ || d == s) continue;
        copy_src[(size_t)i] = (d << 8) | s;
    }

    cb_src_d.assign((size_t)n, -1);
    cb_src_key.assign((size_t)n, 0);
    for (int i = 0; i < n; i++) {
        if (prog.op[i] != T.O_Mov) continue;
        u64 q = prog.q[i];
        if (srcb_form(q) != FORM_CBUF) continue;
        int d = (int)(q & 0xFF);
        int b = cbuf_bank(q), o = cbuf_off(q);
        if (d == RZ || b == opt_bank || b == 1) continue;
        cb_src_d[(size_t)i] = d;
        cb_src_key[(size_t)i] = (int32_t)(CBBASE - ((b << 20) | o));
    }

    cb_slots.assign((size_t)n, {});
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];
        if (!T.alu_cbuf[(size_t)nm] || srcb_form(prog.q[i]) != FORM_REG) continue;

        if (srcc_form(prog.q[i])) continue;
        int offs[8];
        int m = gpr_src_offsets(prog.q[i], nm, prog.props[i], offs);
        for (int k = 0; k < m; k++) {
            if (offs[k] == 20 || offs[k] == 39) {
                int r = (int)((prog.q[i] >> offs[k]) & 0xFF);
                if (r != RZ) cb_slots[(size_t)i].push_back(r);
            }
        }
    }

    norw.assign((size_t)n, 0);
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];
        norw[(size_t)i] = (char)(T.tex_bases[(size_t)nm] || nm == T.O_Shfl ||
                                 mem_data_regs(prog.q[i], nm) > 1);
    }

    cse_ok.assign((size_t)n, 0);
    cse_dst.assign((size_t)n, 0);
    cse_base_q.assign((size_t)n, 0);
    cse_srcoff.assign((size_t)n, {});
    cse_pmask.assign((size_t)n, Mask());
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];

        if (!T.pure_cse[(size_t)nm] &&
            !(g_cse_mov32i && nm == T.O_Mov32i)) continue;
        RSet u = prog.defs[i];
        u.unite(prog.maydefs[i]);
        std::vector<int> lst; u.list(lst);
        if (lst.size() != 1) continue;
        int d = lst[0];
        if (d >= PREG || d == RZ) continue;
        u64 q = prog.q[i];
        int offs[8];
        int m = gpr_src_offsets(q, nm, prog.props[i], offs);
        u64 mask = 0xFFull | (0xFull << 16);
        for (int k = 0; k < m; k++) mask |= 0xFFull << offs[k];
        Mask pm;
        int gp = (int)((q >> 16) & 7);
        std::vector<int> uu; prog.uses[i].list(uu);
        for (int r : uu)
            if (r >= PREG && !(r == PREG + gp && gp != PT)) pm.set(r);
        cse_ok[(size_t)i] = 1;
        cse_dst[(size_t)i] = d;
        cse_base_q[(size_t)i] = q & ~mask;
        cse_srcoff[(size_t)i].assign(offs, offs + m);
        cse_pmask[(size_t)i] = pm;
    }

    lm.assign((size_t)n, LmSlot());
    lm_ok = true;
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];
        if (nm != T.O_Stl && nm != T.O_Ldl) continue;
        u64 q = prog.q[i];
        if (((q >> 8) & 0xFF) != (u64)RZ) { lm_ok = false; continue; }
        int32_t off = lmem_off(q);
        int w = mem_data_regs(q, nm);
        if (off < 0 || (off & 3) || off > 0x40000) { lm_ok = false; continue; }
        if ((off >> 2) + w > LMMAX) { lm_ok = false; continue; }
        LmSlot s;
        s.off = off >> 2; s.w = w; s.store = (nm == T.O_Stl); s.valid = true;
        lm[(size_t)i] = s;
    }

    lm_live = lm_dse && lm_ok;
    if (lm_live) {
        for (int i = 0; i < n; i++) {
            if (!lm[(size_t)i].valid) continue;
            int o = lm[(size_t)i].off, w = lm[(size_t)i].w;
            bool st = lm[(size_t)i].store;
            bool pred = prog.guarded(i) || prog.never(i);
            if (st) {
                for (int k = 0; k < w; k++) dall_mask[(size_t)i].set(LMBIT + o + k);
                if (pred) {
                    for (int k = 0; k < w; k++) {
                        maydef_set[(size_t)i].push_back(LMBIT + o + k);
                        use_list[(size_t)i].push_back(LMBIT + o + k);
                    }
                    std::sort(maydef_set[(size_t)i].begin(),
                              maydef_set[(size_t)i].end());
                } else {
                    for (int k = 0; k < w; k++) def_mask[(size_t)i].set(LMBIT + o + k);
                }
            } else {
                for (int k = 0; k < w; k++) use_list[(size_t)i].push_back(LMBIT + o + k);
            }
        }
    }
    stl_is_se = !lm_live;

    is_se.assign((size_t)n, 0);
    is_branchy.assign((size_t)n, 0);
    is_pushy.assign((size_t)n, 0);
    is_free.assign((size_t)n, 0);
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];
        is_se[(size_t)i] = T.side_effect[(size_t)nm];
        is_branchy[(size_t)i] = T.branchy[(size_t)nm];
        is_pushy[(size_t)i] = T.pushy[(size_t)nm];
        is_free[(size_t)i] = T.freebie[(size_t)nm];
    }

    truesrc.assign((size_t)n, RSet());
    for (int i = 0; i < n; i++) {
        if (prog.guarded(i) || prog.never(i)) {
            u64 orig = prog.q[i];
            u64 forced = (orig & ~((u64)0xF << 16)) | ((u64)PT << 16);
            RSet d, md, u;
            Program::du_word(forced, prog.op[i], prog.props[i], d, md, u);
            truesrc[(size_t)i] = u;
        } else {
            truesrc[(size_t)i] = prog.uses[i];
        }
    }
    n_fixed = 0;
    if (fix_maydef) {
        for (int i = 0; i < n; i++) {
            auto &m = maydef_set[(size_t)i];
            if (m.empty()) continue;
            bool hit = false;
            for (int r : m) if (truesrc[(size_t)i].has(r)) { hit = true; break; }
            if (!hit) continue;
            std::vector<int> keep;
            for (int r : m) if (!truesrc[(size_t)i].has(r)) keep.push_back(r);
            m.swap(keep);
            n_fixed++;
        }
    }

    lmval = (folds & FOLD_LMVAL) && lm_ok;
    if (lmval) {
        for (int i = 0; i < n; i++) {
            if (!lm[(size_t)i].valid || !lm[(size_t)i].store) continue;
            int off = lm[(size_t)i].off, w = lm[(size_t)i].w;
            auto &v = dd[(size_t)i];
            for (int k = 0; k < w; k++) {
                int key = LMVAL + off + k;
                if (std::find(v.begin(), v.end(), key) == v.end())
                    v.push_back(key);
            }
            std::sort(v.begin(), v.end());
        }
    }
    tex_rw.assign((size_t)n, 0);
    tex_dstgroup.assign((size_t)n, 0);
    for (int i = 0; i < n; i++) {
        int nm = prog.op[i];
        if (!T.tex_bases[(size_t)nm]) continue;
        tex_dstgroup[(size_t)i] = 1;
        if (!texrw || nm != T.O_Texs) continue;
        int tgtf = (int)((prog.q[i] >> 53) & 0xF);
        static const int TS[14][2] = {
            {1,0},{1,1},{1,1},{2,1},{2,1},{2,2},{2,1},{2,1},{2,1},{2,2},{2,1},
            {2,1},{2,1},{2,2}};
        int k = tgtf < 13 ? tgtf : 13;
        if (!(TS[k][0] == 1 && TS[k][1] == 1)) continue;
        tex_rw[(size_t)i] = 1;
        norw[(size_t)i] = 0;
    }
}

int Spec::cbfold_slot(int i, const EMap &e) const {
    if (!cbfold) return -1;
    if (norw[(size_t)i]) return -1;
    const std::vector<int> &slots = cb_slots[(size_t)i];
    if (slots.empty()) return -1;
    const OpSets &T = S();
    int nm = p->op[i];
    u64 q = p->q[i];
    int offs[10];
    int m = gpr_src_offsets(q, nm, p->props[i], offs);
    for (int off : {20, 39}) {

        if (off == 20 && !T.alu_cbuf[(size_t)nm]) continue;
        if (off == 39 && !T.alu_cbuf_srcc[(size_t)nm]) continue;
        int r = (int)((q >> off) & 0xFF);
        if (r == RZ) continue;
        if (std::find(slots.begin(), slots.end(), r) == slots.end()) continue;

        int occ = 0;
        for (int k = 0; k < m; k++)
            if ((int)((q >> offs[k]) & 0xFF) == r) occ++;
        if (occ != 1) continue;
        auto it = e.find(r);
        if (it == e.end() || it->second >= 0) continue;
        return off;
    }
    return -1;
}

bool Spec::cb(int b, int off, u32 *out) const {
    if (b == bank) {
        int k = off >> 2;
        if (k >= 0 && k < (int)opt->size()) { *out = (*opt)[(size_t)k] & M32; return true; }
        return false;
    }
    if (fold_blob && b == 1) return p->blob_u32(off, out);
    return false;
}

bool Spec::regval(const VMap &v, int r, u32 *out) const {
    if (r == RZ) { *out = 0; return true; }
    const u32 *x = vmap_get(v, r);
    if (!x) return false;
    *out = *x;
    return true;
}

bool Spec::srcbval(u64 q, const VMap &v, u32 *out) const {
    int f = srcb_form(q);
    if (f == FORM_IMM) { *out = (u32)imm20i_signed(q); return true; }
    if (f == FORM_CBUF) return cb(cbuf_bank(q), cbuf_off(q), out);
    int r = (int)((q >> 20) & 0xFF);
    if (r == RZ) { *out = 0; return true; }
    const u32 *x = vmap_get(v, r);
    if (!x) return false;
    *out = *x;
    return true;
}

Tri Spec::predval(const VMap &v, int pn, int inv) const {
    bool b;
    if (pn == PT) b = true;
    else {
        const u32 *x = vmap_get(v, PREG + pn);
        if (!x) return TRI_U;
        b = (*x != 0);
    }
    if (inv) b = !b;
    return b ? TRI_T : TRI_F;
}

void Spec::lop_out(u64 q, int lop, bool ha, u32 a, bool hb, u32 b, int d,
                   int pd, int pop, EvalOut &out) const {
    (void)q;
    bool hr = false;
    u32 r = 0;
    Tri pr = TRI_U;
    if (ha && hb) {
        r = (lop == 0 ? (a & b) : lop == 1 ? (a | b) : lop == 2 ? (a ^ b) : b) & M32;
        hr = true;
        pr = (r != 0) ? TRI_T : TRI_F;
    } else if (lop == 1) {
        bool hk = ha || hb;
        u32 k = ha ? a : b;
        if (hk) {
            if (k == M32) { r = M32; hr = true; pr = TRI_T; }
            else if (k != 0) pr = TRI_T;
        }
    } else if (lop == 0) {
        bool hk = ha || hb;
        u32 k = ha ? a : b;
        if (hk && k == 0) { r = 0; hr = true; pr = TRI_F; }
    } else if (lop == 3 && hb) {
        r = b & M32;
        hr = true;
        pr = (r != 0) ? TRI_T : TRI_F;
    }
    if (d != RZ && hr) out.put(d, r);
    if (pd != PT) {
        if (pop == 0) out.put(PREG + pd, 0);
        else if (pop == 1) out.put(PREG + pd, 1);
        else if (pr != TRI_U)
            out.put(PREG + pd, (u32)((pop == 2) ? (pr ? 0 : 1) : (pr ? 1 : 0)));
    }
}

void Spec::eval5(int i, const VMap &v, EvalOut &out) const {
    const OpSets &T = S();
    u64 q = p->q[i];
    int nm = p->op[i];

    if (nm == T.O_Mov) {
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        u32 x;
        bool ok;
        if (!((q >> 60) & 1)) ok = cb(cbuf_bank(q), cbuf_off(q), &x);
        else ok = regval(v, (int)((q >> 20) & 0xFF), &x);
        if (!ok) return;
        out.put(d, x);
        return;
    }
    if (nm == T.O_Mov32i) {
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        out.put(d, imm32(q));
        return;
    }
    if (nm == T.O_Isetp) {
        if ((q >> 43) & 1) return;
        u32 a, b;
        bool ha = regval(v, (int)((q >> 8) & 0xFF), &a);
        bool hb = srcbval(q, v, &b);
        bool sgn = (q >> 48) & 1;
        Tri c = TRI_U;
        if (ha && hb) {
            bool r;
            if (icmp_op((int)((q >> 49) & 7), a, b, sgn, &r)) c = r ? TRI_T : TRI_F;
        }
        Tri pv = predval(v, (int)((q >> 39) & 7), (int)((q >> 42) & 1));
        int op = (int)((q >> 45) & 3);
        Tri r0 = bop(op, c, pv);
        Tri r1 = bop(op, notTri(c), pv);
        int d0 = (int)((q >> 3) & 7), d1 = (int)(q & 7);
        if (d0 != PT && r0 != TRI_U) out.put(PREG + d0, (u32)r0);
        if (d1 != PT && r1 != TRI_U) out.put(PREG + d1, (u32)r1);
        return;
    }
    if (nm == T.O_Psetp) {
        Tri pa = predval(v, (int)((q >> 12) & 7), (int)((q >> 15) & 1));
        Tri pb = predval(v, (int)((q >> 29) & 7), (int)((q >> 32) & 1));
        Tri pc = predval(v, (int)((q >> 39) & 7), (int)((q >> 42) & 1));
        Tri inner = bop((int)((q >> 24) & 3), pa, pb);
        int op2 = (int)((q >> 45) & 3);
        Tri r0 = bop(op2, inner, pc);
        Tri r1 = bop(op2, notTri(inner), pc);
        int d0 = (int)((q >> 3) & 7), d1 = (int)(q & 7);
        if (d0 != PT && r0 != TRI_U) out.put(PREG + d0, (u32)r0);
        if (d1 != PT && r1 != TRI_U) out.put(PREG + d1, (u32)r1);
        return;
    }
    if (nm == T.O_Iset) {
        u32 a, b;
        bool ha = regval(v, (int)((q >> 8) & 0xFF), &a);
        bool hb = srcbval(q, v, &b);
        bool sgn = (q >> 48) & 1;
        Tri c = TRI_U;
        if (ha && hb) {
            bool r;
            if (icmp_op((int)((q >> 49) & 7), a, b, sgn, &r)) c = r ? TRI_T : TRI_F;
        }
        Tri pv = predval(v, (int)((q >> 39) & 7), (int)((q >> 42) & 1));
        Tri r = bop((int)((q >> 45) & 3), c, pv);
        if (r == TRI_U) return;
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        int bf = (int)((q >> 44) & 1);
        out.put(d, r ? (bf ? 0x3F800000u : M32) : 0u);
        return;
    }
    if (nm == T.O_Imnmx) {
        u32 a, b;
        bool ha = regval(v, (int)((q >> 8) & 0xFF), &a);
        bool hb = srcbval(q, v, &b);
        Tri pv = predval(v, (int)((q >> 39) & 7), (int)((q >> 42) & 1));
        if (!ha || !hb || pv == TRI_U) return;
        bool sgn = (q >> 48) & 1;
        u32 r;
        if (sgn) {
            int32_t aa = s32(a), bb = s32(b);
            r = (u32)(pv ? std::min(aa, bb) : std::max(aa, bb));
        } else {
            r = pv ? std::min(a, b) : std::max(a, b);
        }
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        out.put(d, r & M32);
        return;
    }
    if (nm == T.O_Sel) {
        Tri pv = predval(v, (int)((q >> 39) & 7), (int)((q >> 42) & 1));
        if (pv == TRI_U) return;
        u32 x;
        bool ok = pv ? regval(v, (int)((q >> 8) & 0xFF), &x) : srcbval(q, v, &x);
        int d = (int)(q & 0xFF);
        if (d == RZ || !ok) return;
        out.put(d, x & M32);
        return;
    }
    if (nm == T.O_Shl) {
        u32 a, b;
        if (!regval(v, (int)((q >> 8) & 0xFF), &a)) return;
        if (!srcbval(q, v, &b)) return;
        bool wrap = (q >> 39) & 1;
        u32 sh = wrap ? (b & 31) : b;
        u32 r = (sh >= 32) ? 0u : ((a << sh) & M32);
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        out.put(d, r);
        return;
    }
    if (nm == T.O_Shr) {
        u32 a, b;
        if (!regval(v, (int)((q >> 8) & 0xFF), &a)) return;
        if (!srcbval(q, v, &b)) return;
        if ((q >> 40) & 1) return;
        bool wrap = (q >> 39) & 1;
        u32 sh = wrap ? (b & 31) : b;
        bool sgn = (q >> 48) & 1;
        u32 r;
        if (sh >= 32) r = (sgn && (a & 0x80000000u)) ? M32 : 0u;
        else if (sgn) r = (u32)(s32(a) >> sh);
        else r = a >> sh;
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        out.put(d, r);
        return;
    }
    if (nm == T.O_Iadd) {
        if ((q & ((u64)1 << 43)) || (q & ((u64)1 << 50))) return;
        u32 a, b;
        if (!regval(v, (int)((q >> 8) & 0xFF), &a)) return;
        if (!srcbval(q, v, &b)) return;
        if ((q >> 49) & 1) a = (u32)(-(int32_t)a) & M32;
        if ((q >> 48) & 1) b = (u32)(-(int32_t)b) & M32;
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        out.put(d, (a + b) & M32);
        return;
    }
    if (nm == T.O_Iadd32i) {
        if ((q & ((u64)1 << 53)) || (q & ((u64)1 << 54))) return;
        u32 a;
        if (!regval(v, (int)((q >> 8) & 0xFF), &a)) return;
        if ((q >> 56) & 1) a = (u32)(-(int32_t)a) & M32;
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        out.put(d, (a + imm32(q)) & M32);
        return;
    }
    if (nm == T.O_Lop) {
        if ((q >> 43) & 1) return;
        u32 a = 0, b = 0;
        bool ha = regval(v, (int)((q >> 8) & 0xFF), &a);
        bool hb = srcbval(q, v, &b);
        if (ha && ((q >> 39) & 1)) a ^= M32;
        if (hb && ((q >> 40) & 1)) b ^= M32;
        lop_out(q, (int)((q >> 41) & 3), ha, a, hb, b, (int)(q & 0xFF),
                (int)((q >> 48) & 7), (int)((q >> 44) & 3), out);
        return;
    }
    if (nm == T.O_Lop32i) {
        u32 a = 0;
        bool ha = regval(v, (int)((q >> 8) & 0xFF), &a);
        u32 b = imm32(q);
        if (ha && ((q >> 55) & 1)) a ^= M32;
        if ((q >> 56) & 1) b ^= M32;
        lop_out(q, (int)((q >> 53) & 3), ha, a, true, b, (int)(q & 0xFF), PT, 0,
                out);
        return;
    }
    if (nm == T.O_Ldc) {
        LdcFields f = ldc_fields(q);
        if (f.bank != 1 || f.mode != 0 || ((q >> 48) & 7) != 4) return;
        if (!fold_blob) return;
        u32 base = 0;
        if (f.ra != RZ) {
            const u32 *x = vmap_get(v, f.ra);
            if (!x) return;
            base = *x;
        }
        u32 x;
        if (!p->blob_u32((int)((base + (u32)f.off) & M32), &x)) return;
        if (f.rd == RZ) return;
        out.put(f.rd, x);
        return;
    }
}

void Spec::eval(int i, const VMap &v, EvalOut &out) const {
    eval5(i, v, out);
    if (out.present) return;
    if (!folds) return;

    const OpSets &T = S();
    int nm = p->op[i];
    u64 q = p->q[i];

    if (lmval && lm[(size_t)i].valid) {
        int off = lm[(size_t)i].off, w = lm[(size_t)i].w;
        bool is_store = lm[(size_t)i].store;
        if (is_store) {
            int src = (int)(q & 0xFF);
            for (int k = 0; k < w; k++) {
                if (src == RZ) out.put(LMVAL + off + k, 0);
                else {
                    const u32 *x = vmap_get(v, src + k);
                    if (x) out.put(LMVAL + off + k, *x);
                }
            }
        } else {
            int d = (int)(q & 0xFF);
            if (d == RZ) return;
            for (int k = 0; k < w; k++) {
                if (d + k >= RZ) break;
                const u32 *x = vmap_get(v, LMVAL + off + k);
                if (x) out.put(d + k, *x);
            }
        }
        return;
    }

    if (nm == T.O_Pset && (folds & FOLD_PSET)) {
        PsetF f = pset_fields(q);
        int d = f.rd;
        if (d == RZ) return;
        Tri pa = predval(v, f.pa, f.pain);
        Tri pb = predval(v, f.pb, f.pbin);
        Tri pc = predval(v, f.pc, f.pcin);
        Tri res = bop(f.outer, bop(f.inner, pa, pb), pc);
        if (res == TRI_U) return;
        if (res == TRI_F) { out.put(d, 0); return; }
        out.put(d, f.bf ? 0x3F800000u : M32);
        return;
    }

    if (nm == T.O_Fsetp || nm == T.O_Fset) {
        FsetpF f = (nm == T.O_Fsetp) ? fsetp_fields(q) : fset_fields(q);
        Tri pc = predval(v, f.pc, f.pcinv);
        Tri c = TRI_U;
        if (folds & FOLD_FCMP) {
            u32 ub;
            bool ha = false, hb = false;
            float a = 0, b = 0;
            {
                u32 x;
                if (regval(v, f.ra, &x)) { a = f32_of(x); ha = true; }
            }
            {
                int sf = srcb_form(q);
                if (sf == FORM_IMM) { b = f32_of(imm20i(q) << 12); hb = true; }
                else if (sf == FORM_CBUF) {
                    if (cb(cbuf_bank(q), cbuf_off(q), &ub)) { b = f32_of(ub); hb = true; }
                } else {
                    int r = (int)((q >> 20) & 0xFF);
                    if (r == RZ) { b = 0.0f; hb = true; }
                    else { const u32 *x = vmap_get(v, r); if (x) { b = f32_of(*x); hb = true; } }
                }
            }
            if (ha) {
                if (f.ftz_) a = ftz(a);
                if (f.absa) a = std::fabs(a);
                if (f.nega) a = -a;
            }
            if (hb) {
                if (f.ftz_) b = ftz(b);
                if (f.absb) b = std::fabs(b);
                if (f.negb) b = -b;
            }
            if (ha && hb) {
                bool r;
                if (fcmp_op(f.cmp, a, b, &r)) c = r ? TRI_T : TRI_F;
            }
        }
        if (!(folds & FOLD_FPRED) && c == TRI_U) return;
        if (nm == T.O_Fsetp) {
            Tri r0 = bop(f.bop_, c, pc);
            Tri r1 = bop(f.bop_, notTri(c), pc);
            if (f.d0 != PT && r0 != TRI_U) out.put(PREG + f.d0, (u32)r0);
            if (f.d1 != PT && r1 != TRI_U) out.put(PREG + f.d1, (u32)r1);
            return;
        }
        Tri res = bop(f.bop_, c, pc);
        if (res == TRI_U || f.rd == RZ || f.cc) return;
        out.put(f.rd, res ? (f.bf ? 0x3F800000u : M32) : 0u);
        return;
    }

    if (nm == T.O_Fmnmx && (folds & FOLD_FCMP)) {
        FmnmxF f = fmnmx_fields(q);
        if (f.rd == RZ || f.cc) return;
        Tri pv = predval(v, f.pc, f.pcinv);
        bool ha = false, hb = false;
        float a = 0, b = 0;
        { u32 x; if (regval(v, f.ra, &x)) { a = f32_of(x); ha = true; } }
        {
            int sf = srcb_form(q);
            u32 ub;
            if (sf == FORM_IMM) { b = f32_of(imm20i(q) << 12); hb = true; }
            else if (sf == FORM_CBUF) {
                if (cb(cbuf_bank(q), cbuf_off(q), &ub)) { b = f32_of(ub); hb = true; }
            } else {
                int r = (int)((q >> 20) & 0xFF);
                if (r == RZ) { b = 0.0f; hb = true; }
                else { const u32 *x = vmap_get(v, r); if (x) { b = f32_of(*x); hb = true; } }
            }
        }
        if (ha) { if (f.ftz_) a = ftz(a); if (f.absa) a = std::fabs(a); if (f.nega) a = -a; }
        if (hb) { if (f.ftz_) b = ftz(b); if (f.absb) b = std::fabs(b); if (f.negb) b = -b; }
        if (pv == TRI_U || !ha || !hb) return;
        if (std::isnan(a) || std::isnan(b)) return;
        float x = pv ? std::min(a, b) : std::max(a, b);
        out.put(f.rd, bits_of(x));
        return;
    }

    if ((folds & FOLD_FVAL) &&
        (nm == T.O_Fadd || nm == T.O_Fmul || nm == T.O_Ffma)) {
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        if ((q >> 50) & 1) return;
        auto srcb_f = [&](float *o) -> bool {
            int sf = srcb_form(q);
            u32 ub;
            if (sf == FORM_IMM) { *o = f32_of((u32)(imm20i(q) << 12)); return true; }
            if (sf == FORM_CBUF) {
                if (!cb(cbuf_bank(q), cbuf_off(q), &ub)) return false;
                *o = f32_of(ub);
                return true;
            }
            int r = (int)((q >> 20) & 0xFF);
            if (r == RZ) { *o = 0.0f; return true; }
            const u32 *x = vmap_get(v, r);
            if (!x) return false;
            *o = f32_of(*x);
            return true;
        };
        float a;
        { u32 x; if (!regval(v, (int)((q >> 8) & 0xFF), &x)) return; a = f32_of(x); }
        if (nm == T.O_Fadd) {
            if ((q >> 39) & 3) return;
            float b;
            if (!srcb_f(&b)) return;
            bool fz = (q >> 44) & 1;
            if (fz) { a = ftz(a); b = ftz(b); }
            if ((q >> 46) & 1) a = std::fabs(a);
            if ((q >> 48) & 1) a = -a;
            if ((q >> 49) & 1) b = std::fabs(b);
            if ((q >> 45) & 1) b = -b;
            float r = a + b;
            if (fz) r = ftz(r);
            out.put(d, bits_of(r));
            return;
        }
        if (nm == T.O_Fmul) {
            if (((q >> 39) & 3) || ((q >> 41) & 7)) return;
            float b;
            if (!srcb_f(&b)) return;
            bool fz = ((q >> 44) & 3) != 0;
            if (fz) { a = ftz(a); b = ftz(b); }
            float r = a * b;
            if ((q >> 48) & 1) r = -r;
            if (fz) r = ftz(r);
            out.put(d, bits_of(r));
            return;
        }

        if ((q >> 51) & 3) return;
        int top5 = cbuf_top5(q);
        float b, c2;
        bool okb = false, okc = false;
        u32 ub;
        if (top5 == 0b00110 || top5 == 0b00111) {
            b = f32_of((u32)(imm20i(q) << 12)); okb = true;
            u32 x; if (regval(v, (int)((q >> 39) & 0xFF), &x)) { c2 = f32_of(x); okc = true; }
        } else if (top5 == CBUF_SRCB_TOP5) {
            if (cb(cbuf_bank(q), cbuf_off(q), &ub)) { b = f32_of(ub); okb = true; }
            u32 x; if (regval(v, (int)((q >> 39) & 0xFF), &x)) { c2 = f32_of(x); okc = true; }
        } else if (top5 == CBUF_SRCC_TOP5) {
            u32 x; if (regval(v, (int)((q >> 20) & 0xFF), &x)) { b = f32_of(x); okb = true; }
            if (cb(cbuf_bank(q), cbuf_off(q), &ub)) { c2 = f32_of(ub); okc = true; }
        } else {
            u32 x;
            if (regval(v, (int)((q >> 20) & 0xFF), &x)) { b = f32_of(x); okb = true; }
            if (regval(v, (int)((q >> 39) & 0xFF), &x)) { c2 = f32_of(x); okc = true; }
        }
        if (!okb || !okc) return;
        bool fz = ((q >> 53) & 3) != 0;
        if (fz) { a = ftz(a); b = ftz(b); c2 = ftz(c2); }
        double pr = (double)a * (double)b;
        if ((q >> 48) & 1) pr = -pr;
        if ((q >> 49) & 1) c2 = -c2;
        float r = (float)(pr + (double)c2);
        if (fz) r = ftz(r);
        out.put(d, bits_of(r));
        return;
    }

    if (nm == T.O_Xmad && (folds & FOLD_XMAD)) {
        int sela, selb, psl, mrg, cbcc;
        if (!xmad_shape(q, &sela, &selb, &psl, &mrg, &cbcc)) return;
        int d = (int)(q & 0xFF);
        if (d == RZ) return;
        int ra = (int)((q >> 8) & 0xFF), rc = (int)((q >> 39) & 0xFF);
        u32 a, c;
        if (ra == RZ) a = 0; else { const u32 *x = vmap_get(v, ra); if (!x) return; a = *x; }
        if (rc == RZ) c = 0; else { const u32 *x = vmap_get(v, rc); if (!x) return; c = *x; }
        u32 b;
        int sf = srcb_form(q);
        if (sf == FORM_IMM) b = (u32)((q >> 20) & 0xFFFF);
        else if (sf == FORM_CBUF) { if (!cb(cbuf_bank(q), cbuf_off(q), &b)) return; }
        else {
            int rb = (int)((q >> 20) & 0xFF);
            if (rb == RZ) b = 0;
            else { const u32 *x = vmap_get(v, rb); if (!x) return; b = *x; }
        }
        out.put(d, xmad_value(a & M32, sela, b & M32, selb, c & M32, psl, mrg,
                              cbcc));
        return;
    }
}


void Spec::run(const std::vector<u32> &optvals, RunRes &R) {
    opt = &optvals;
    int n = p->n;

    R.visited.assign((size_t)n, 0);
    R.vals.assign((size_t)n, VMap());
    R.stacks.assign((size_t)n, {});
    R.pool = StackPoolV();

    std::vector<std::pair<int, int>> work;
    work.reserve(1 << 20);
    std::vector<std::vector<char>> inset((size_t)n);

    auto push = [&](int i, const std::vector<int64_t> &stk, const VMap &v) {
        if (i < 0 || i >= n) return;
        int sid = R.pool.intern(stk);
        bool changed = false;
        if (!R.visited[(size_t)i]) {
            R.visited[(size_t)i] = 1;
            R.vals[(size_t)i] = v;
            changed = true;
        } else {
            VMap &cur = R.vals[(size_t)i];
            size_t w = 0;
            for (size_t k = 0; k < cur.size(); k++) {
                const u32 *x = vmap_get(v, cur[k].first);
                if (x && *x == cur[k].second) cur[w++] = cur[k];
                else changed = true;
            }
            if (w != cur.size()) cur.resize(w);
        }
        auto &st = R.stacks[(size_t)i];
        if (changed)
            for (int s : st) work.push_back({i, s});
        bool have = false;
        for (int s : st) if (s == sid) { have = true; break; }
        if (!have) { st.push_back(sid); work.push_back({i, sid}); }
    };

    {
        std::vector<int64_t> empty;
        VMap ev;
        push(0, empty, ev);
    }

    size_t head = 0;
    long long steps = 0;
    VMap out;
    EvalOut ev;
    while (head < work.size()) {
        int i = work[head].first, sid = work[head].second;
        head++;
        steps++;
        if (steps > 40000000LL) fail("state explosion");
        const std::vector<int64_t> stk = R.pool.get(sid);
        const VMap &v = R.vals[(size_t)i];
        int nxt = (i + 1 < n) ? i + 1 : -1;
        int c = cat[(size_t)i];

        Tri g = nopred[(size_t)i] ? TRI_T
                                  : predval(v, pnum[(size_t)i], pinv[(size_t)i]);
        if (g == TRI_F) {
            if (nxt >= 0) push(nxt, stk, v);
            continue;
        }

        if (!dd[(size_t)i].empty()) {
            ev.present = false;
            ev.kv.clear();
            if (g == TRI_T) eval(i, v, ev);
            out = v;
            if (ev.present) {
                for (int32_t r : dd[(size_t)i]) {
                    const u32 *x = ev.get(r);
                    if (!x) vmap_erase(out, r);
                    else vmap_set(out, r, *x);
                }
            } else {
                for (int32_t r : dd[(size_t)i]) vmap_erase(out, r);
            }
        } else {
            out = v;
        }

        if (c == C_SSY || c == C_PBK || c == C_PCNT) {
            std::vector<int64_t> ns = stk;
            if ((int)stk.size() < MAX_DEPTH)
                ns.push_back(((int64_t)(c == C_SSY ? 0 : c == C_PBK ? 1 : 2) << 32) |
                             (int64_t)(u32)tgt[(size_t)i]);
            push(nxt, ns, out);
        } else if (c == C_SYNC) {
            if (!stk.empty() && (int)(stk.back() >> 32) == 0) {
                int t = (int)(int32_t)(u32)(stk.back() & 0xFFFFFFFF);
                if (t >= 0) {
                    std::vector<int64_t> ns(stk.begin(), stk.end() - 1);
                    push(t, ns, out);
                }
            }
            if (g != TRI_T && nxt >= 0) push(nxt, stk, out);
        } else if (c == C_BRK || c == C_CONT) {
            int want = (c == C_BRK) ? 1 : 2;
            int k = -1;
            for (int pp = (int)stk.size() - 1; pp >= 0; pp--)
                if ((int)(stk[(size_t)pp] >> 32) == want) { k = pp; break; }
            if (k >= 0) {
                int t = (int)(int32_t)(u32)(stk[(size_t)k] & 0xFFFFFFFF);
                if (t >= 0) {
                    std::vector<int64_t> ns(stk.begin(),
                        stk.begin() + (c == C_BRK ? k : k + 1));
                    push(t, ns, out);
                }
            }
            if (g != TRI_T && nxt >= 0) push(nxt, stk, out);
        } else if (c == C_BRA) {
            int t = tgt[(size_t)i];
            if (t >= 0) push(t, stk, out);
            if (g != TRI_T && nxt >= 0) push(nxt, stk, out);
        } else if (c == C_BRX) {
            int ra = (int)((p->q[i] >> 8) & 0xFF);
            u32 a;
            if (regval(out, ra, &a)) {
                int j = p->snap((int)(a & M32));
                if (j >= 0) {
                    int diff = p->rel[(size_t)j] - (int)(a & M32);
                    if (diff == 0 || diff == 8) push(j, stk, out);
                }
            }
            if (g != TRI_T && nxt >= 0) push(nxt, stk, out);
        } else if (c == C_EXIT) {
            if (g != TRI_T && nxt >= 0) push(nxt, stk, out);
        } else {
            if (nxt >= 0) push(nxt, stk, out);
        }
    }

    R.reach.clear();
    R.in_reach.assign((size_t)n, 0);
    for (int i = 0; i < n; i++)
        if (!R.stacks[(size_t)i].empty()) { R.reach.push_back(i); R.in_reach[(size_t)i] = 1; }
    R.states = steps;
}

void Spec::succ_of(const RunRes &R, std::vector<std::vector<int>> &succ) const {
    int n = p->n;
    succ.assign((size_t)n, {});
    VMap out;
    EvalOut ev;
    std::set<int> s;
    for (int i : R.reach) {
        const VMap &v = R.vals[(size_t)i];
        s.clear();
        int nxt = (i + 1 < n) ? i + 1 : -1;
        Tri g = nopred[(size_t)i] ? TRI_T
                                  : predval(v, pnum[(size_t)i], pinv[(size_t)i]);
        if (g == TRI_F) {
            if (nxt >= 0) succ[(size_t)i].push_back(nxt);
            continue;
        }
        if (!dd[(size_t)i].empty()) {
            ev.present = false; ev.kv.clear();
            eval(i, v, ev);
            out = v;
            if (ev.present) {
                for (int32_t r : dd[(size_t)i]) {
                    const u32 *x = ev.get(r);
                    if (!x) vmap_erase(out, r);
                    else vmap_set(out, r, *x);
                }
            } else {
                for (int32_t r : dd[(size_t)i]) vmap_erase(out, r);
            }
        } else {
            out = v;
        }
        int c = cat[(size_t)i];
        if (c == C_SSY || c == C_PBK || c == C_PCNT) {
            if (nxt >= 0) s.insert(nxt);
        } else if (c == C_SYNC) {
            for (int sid : R.stacks[(size_t)i]) {
                const std::vector<int64_t> &stk = R.pool.get(sid);
                if (!stk.empty() && (int)(stk.back() >> 32) == 0) {
                    int t = (int)(int32_t)(u32)(stk.back() & 0xFFFFFFFF);
                    if (t >= 0) s.insert(t);
                }
            }
            if (g != TRI_T && nxt >= 0) s.insert(nxt);
        } else if (c == C_BRK || c == C_CONT) {
            int want = (c == C_BRK) ? 1 : 2;
            for (int sid : R.stacks[(size_t)i]) {
                const std::vector<int64_t> &stk = R.pool.get(sid);
                for (int pp = (int)stk.size() - 1; pp >= 0; pp--) {
                    if ((int)(stk[(size_t)pp] >> 32) == want) {
                        int t = (int)(int32_t)(u32)(stk[(size_t)pp] & 0xFFFFFFFF);
                        if (t >= 0) s.insert(t);
                        break;
                    }
                }
            }
            if (g != TRI_T && nxt >= 0) s.insert(nxt);
        } else if (c == C_BRA) {
            int t = tgt[(size_t)i];
            if (t >= 0) s.insert(t);
            if (g != TRI_T && nxt >= 0) s.insert(nxt);
        } else if (c == C_BRX) {
            int ra = (int)((p->q[i] >> 8) & 0xFF);
            u32 a;
            if (regval(out, ra, &a)) {
                int j = p->snap((int)(a & M32));
                if (j >= 0) {
                    int diff = p->rel[(size_t)j] - (int)(a & M32);
                    if (diff == 0 || diff == 8) s.insert(j);
                }
            }
            if (g != TRI_T && nxt >= 0) s.insert(nxt);
        } else if (c == C_EXIT) {
            if (g != TRI_T && nxt >= 0) s.insert(nxt);
        } else {
            if (nxt >= 0) s.insert(nxt);
        }
        succ[(size_t)i].assign(s.begin(), s.end());
    }
}

void Spec::copyprop_pass(RunRes &R) const {
    int n = p->n;
    R.env.assign((size_t)n, EMap());
    std::vector<AvMap> av_in((size_t)n);

    typedef std::unordered_map<int, int> MulMap;
    R.mul_in.assign((size_t)(g_fmac ? n : 0), MulMap());
    MulMap omul;
    std::vector<char> has((size_t)n, 0);
    std::vector<char> inq((size_t)n, 0);
    std::vector<int> work;
    size_t head = 0;

    has[0] = 1;
    inq[0] = 1;
    work.push_back(0);

    EMap out;
    AvMap oav;
    while (head < work.size()) {
        int i = work[head++];
        inq[(size_t)i] = 0;

        const EMap &e = R.env[(size_t)i];
        const AvMap &av = av_in[(size_t)i];
        Tri g = R.guard[(size_t)i];
        out = e;
        oav = av;
        if (g_fmac) omul = R.mul_in[(size_t)i];

        if (g == TRI_F) {

        } else {
            const Mask &kill = dall_mask[(size_t)i];
            if (kill.any()) {
                for (auto it = out.begin(); it != out.end();) {
                    int32_t k = it->first, vv = it->second;
                    bool drop = (k < 263 && kill.test(k)) ||
                                (vv >= 0 && vv < 263 && kill.test(vv));
                    if (drop) it = out.erase(it); else ++it;
                }
            }
            if (lm[(size_t)i].valid && lmfwd) {
                int o = lm[(size_t)i].off, w = lm[(size_t)i].w;
                bool is_store = lm[(size_t)i].store;
                if (is_store) {
                    int sr = (int)(p->q[i] & 0xFF);
                    for (int k = 0; k < w; k++) {
                        int key = LMBASE + o + k;
                        if (g == TRI_T && (sr == RZ || sr + k < RZ)) {
                            int32_t val;
                            if (sr == RZ) val = RZ;
                            else {
                                auto it = e.find(sr + k);
                                val = (it != e.end()) ? it->second : (sr + k);
                            }
                            out[key] = val;
                        } else {
                            out.erase(key);
                        }
                    }
                } else if (g == TRI_T && w == 1) {
                    int d = (int)(p->q[i] & 0xFF);
                    auto it = e.find(LMBASE + o);
                    if (d != RZ && it != e.end() && it->second != d)
                        out[d] = it->second;
                }
            }
            int c = copy_src[(size_t)i];
            if (c >= 0 && g == TRI_T) {
                int d = c >> 8, sr = c & 0xFF;
                auto it = e.find(sr);
                int32_t canon = (it != e.end()) ? it->second : sr;
                if (canon != d) out[d] = canon;
            }
            if (cb_src_d[(size_t)i] >= 0 && g == TRI_T && cbfold)
                out[cb_src_d[(size_t)i]] = cb_src_key[(size_t)i];

            if (g_fmac) {
                if (kill.any() && !omul.empty()) {
                    for (auto it = omul.begin(); it != omul.end();) {
                        u64 qm = p->q[it->second];
                        int ma = (int)((qm >> 8) & 0xFF);
                        int mb = (((qm >> 59) & 0x1F) == 0x0B)
                                     ? (int)((qm >> 20) & 0xFF) : RZ;
                        bool drop = kill.test(it->first) ||
                                    (ma != RZ && kill.test(ma)) ||
                                    (mb != RZ && kill.test(mb));
                        if (drop) it = omul.erase(it); else ++it;
                    }
                }
                if (g == TRI_T && fmac_mul_ok(i))
                    omul[(int)(p->q[i] & 0xFF)] = i;
            }

            if (cse) {
                if (kill.any() && !oav.empty()) {
                    for (auto it = oav.begin(); it != oav.end();) {
                        if (it->second.dm.intersects(kill)) it = oav.erase(it);
                        else ++it;
                    }
                }
                if (cse_ok[(size_t)i] && g == TRI_T) {
                    int d = cse_dst[(size_t)i];
                    u64 q = p->q[i];
                    CseKey key;
                    key.op = p->op[i];
                    key.qm = cse_base_q[(size_t)i];
                    for (int o : cse_srcoff[(size_t)i]) {
                        int r = (int)((q >> o) & 0xFF);
                        auto it = e.find(r);
                        key.add(it != e.end() ? it->second : r);
                    }
                    auto pit = oav.find(key);
                    if (pit != oav.end() && pit->second.d != d) {
                        out[d] = pit->second.d;
                    } else {
                        AvVal av2;
                        av2.d = d;
                        av2.dm.set(d);
                        for (int32_t k2 = 0; k2 < key.ns; k2++) {
                            int32_t s = key.s[k2];
                            if (s >= 0 && s < 263) av2.dm.set(s);
                        }
                        av2.dm.unite(cse_pmask[(size_t)i]);
                        oav[key] = av2;
                    }
                }
            }
        }

        for (int t : R.succ[(size_t)i]) {
            if (!has[(size_t)t]) {
                has[(size_t)t] = 1;
                R.env[(size_t)t] = out;
                av_in[(size_t)t] = oav;
                if (g_fmac) R.mul_in[(size_t)t] = omul;
                if (!inq[(size_t)t]) { work.push_back(t); inq[(size_t)t] = 1; }
            } else {
                EMap &cur = R.env[(size_t)t];
                AvMap &ca = av_in[(size_t)t];
                bool ch = false;
                if (g_fmac) {
                    MulMap &cm = R.mul_in[(size_t)t];
                    for (auto it = cm.begin(); it != cm.end();) {
                        auto o = omul.find(it->first);
                        if (o == omul.end() || o->second != it->second) {
                            it = cm.erase(it);
                            ch = true;
                        } else ++it;
                    }
                }
                for (auto it = cur.begin(); it != cur.end();) {
                    auto o = out.find(it->first);
                    if (o == out.end() || o->second != it->second) {
                        it = cur.erase(it);
                        ch = true;
                    } else ++it;
                }
                for (auto it = ca.begin(); it != ca.end();) {
                    auto o = oav.find(it->first);
                    if (o == oav.end() || !(o->second == it->second)) {
                        it = ca.erase(it);
                        ch = true;
                    } else ++it;
                }
                if (ch && !inq[(size_t)t]) { work.push_back(t); inq[(size_t)t] = 1; }
            }
        }

        if (head > 4096 && head * 2 > work.size()) {
            work.erase(work.begin(), work.begin() + (long)head);
            head = 0;
        }
    }
}

static const u64 FFMA_RRR_BASE = 0x5980000000000000ull;
static const u64 FFMA_RCR_BASE = 0x4980000000000000ull;

#define MB(n) ((u64)1 << ((n) - 39))
static const u64 M_FTZ = MB(44), M_NEGB = MB(45),
                 M_ABSA = MB(46), M_NEGA = MB(48), M_ABSB = MB(49);

bool Spec::fmac_mul_ok(int j) const {
    const OpSets &T = S();
    if (p->op[j] != T.O_Fmul) return false;
    if (norw[(size_t)j]) return false;
    u64 q = p->q[j];
    int d = (int)(q & 0xFF);
    if (d == RZ) return false;
    int t5 = (int)((q >> 59) & 0x1F);
    if (t5 != 0x0B && t5 != 0x09) return false;
    u64 ms = (q >> 39) & 0xFFF;

    if (ms & ~(M_FTZ | M_NEGA)) return false;
    if (!(ms & M_FTZ)) return false;
    if ((int)((q >> 8) & 0xFF) == RZ) return false;
    if (t5 == 0x0B && (int)((q >> 20) & 0xFF) == RZ) return false;
    return true;
}

long long g_fm_shape = 0, g_fm_nofact = 0, g_fm_envmap = 0, g_fm_known = 0,
          g_fm_cb = 0, g_fm_mismatch = 0, g_fm_ok = 0;
long long g_fm_final = 0, g_fm_revert = 0, g_fm_progs = 0, g_fm_want = 0;

bool Spec::fmac_ok(const RunRes &R, int i, int *jout, int *slotout) const {
    if (!g_fmac || R.mul_in.empty()) return false;
    const OpSets &T = S();
    if (p->op[i] != T.O_Fadd) return false;
    if (norw[(size_t)i]) return false;
    if (R.guard[(size_t)i] != TRI_T) return false;
    u64 qa = p->q[i];
    if (((qa >> 59) & 0x1F) != 0x0B) return false;
    u64 ms = (qa >> 39) & 0xFFF;

    if (ms & ~(M_FTZ | M_NEGB | M_NEGA)) return false;
    if (!(ms & M_FTZ)) return false;
    const EMap &e = R.env[(size_t)i];
    if (cbfold_slot(i, e) >= 0) return false;
    const std::unordered_map<int, int> &mm = R.mul_in[(size_t)i];
    if (mm.empty()) return false;
    g_fm_shape++;
    int ra = (int)((qa >> 8) & 0xFF), rb = (int)((qa >> 20) & 0xFF);
    bool sawfact = false;
    for (int k = 0; k < 2; k++) {
        int slot = k ? 20 : 8;
        int pr = k ? rb : ra, other = k ? ra : rb;
        if (pr == RZ || pr == other) continue;
        auto it = mm.find(pr);
        if (it == mm.end()) {
            if (e.find(pr) != e.end()) g_fm_envmap++;
            continue;
        }
        sawfact = true;
        int j = it->second;

        if (e.find(pr) != e.end()) { g_fm_envmap++; continue; }
        if (vmap_get(R.vals[(size_t)i], pr)) { g_fm_known++; continue; }
        if (cbfold_slot(j, R.env[(size_t)j]) >= 0) { g_fm_cb++; continue; }
        u64 qm = p->q[j];
        bool ok = true;
        int nsrc = (((qm >> 59) & 0x1F) == 0x0B) ? 2 : 1;
        for (int t = 0; t < nsrc && ok; t++) {
            int r = (int)((qm >> (t ? 20 : 8)) & 0xFF);
            if (r == RZ) { ok = false; break; }
            auto a1 = e.find(r);
            auto a2 = R.env[(size_t)j].find(r);
            int32_t v1 = (a1 != e.end()) ? a1->second : r;
            int32_t v2 = (a2 != R.env[(size_t)j].end()) ? a2->second : r;
            if (v1 != v2 || v1 < 0) ok = false;
            const u32 *x1 = vmap_get(R.vals[(size_t)i], r);
            const u32 *x2 = vmap_get(R.vals[(size_t)j], r);
            if ((x1 != nullptr) != (x2 != nullptr)) ok = false;
            else if (x1 && *x1 != *x2) ok = false;
        }
        if (!ok) { g_fm_mismatch++; continue; }
        g_fm_ok++;
        if (jout) *jout = j;
        if (slotout) *slotout = slot;
        return true;
    }
    if (!sawfact) g_fm_nofact++;
    return false;
}

u64 Spec::fmac_word(const RunRes &R, int i, int j, int slot) const {
    (void)R;
    u64 qa = p->q[i], qm = p->q[j];
    int mt5 = (int)((qm >> 59) & 0x1F);
    u64 q = (mt5 == 0x0B) ? FFMA_RRR_BASE : FFMA_RCR_BASE;
    int creg = (slot == 8) ? (int)((qa >> 20) & 0xFF) : (int)((qa >> 8) & 0xFF);
    int negprod = (int)((qm >> 48) & 1) ^
                  (int)((qa >> (slot == 8 ? 48 : 45)) & 1);
    int negc = (int)((qa >> (slot == 8 ? 45 : 48)) & 1);
    q |= qa & 0xFFull;
    q |= ((qm >> 8) & 0xFFull) << 8;
    q |= qa & (0xFull << 16);
    if (mt5 == 0x0B) q |= ((qm >> 20) & 0xFFull) << 20;
    else             q |= qm & ((((u64)1 << 19) - 1) << 20);
    q |= (u64)creg << 39;
    q |= (u64)1 << 53;
    if (negprod) q |= (u64)1 << 48;
    if (negc)    q |= (u64)1 << 49;
    if (decode_op(q) != S().O_Ffma)
        fail("fmac: the word built at %d does not decode as FFMA", i);
    return q;
}

void Spec::fmac_uses(const RunRes &R, int i, std::vector<int> &out) const {
    out.clear();
    int j = R.fmac[(size_t)i], slot = R.fmac_slot[(size_t)i];
    int pr = (int)((p->q[i] >> (slot == 8 ? 8 : 20)) & 0xFF);
    for (int r : use_list[(size_t)i]) if (r != pr) out.push_back(r);
    u64 qm = p->q[j];
    int nsrc = (((qm >> 59) & 0x1F) == 0x0B) ? 2 : 1;
    for (int t = 0; t < nsrc; t++) {
        int r = (int)((qm >> (t ? 20 : 8)) & 0xFF);
        if (r != RZ) out.push_back(r);
    }
    std::sort(out.begin(), out.end());
    out.erase(std::unique(out.begin(), out.end()), out.end());
}

static long long *const FM_CTRS[] = {
    &g_fm_shape, &g_fm_nofact, &g_fm_envmap, &g_fm_known, &g_fm_cb,
    &g_fm_mismatch, &g_fm_ok, &g_fm_final, &g_fm_revert, &g_fm_progs,
    &g_fm_want};
static const int FM_N = (int)(sizeof FM_CTRS / sizeof FM_CTRS[0]);

struct Run3Cache {
    bool valid = false;
    const Spec *sp = nullptr;
    std::vector<u32> opt;
    bool fmac = false, fmac_all = false;
    RunRes R;
    long long d[FM_N] = {0};
};
static Run3Cache g_r3;
long long g_r3_hit = 0, g_r3_miss = 0;

void run3_cache_clear() {
    Run3Cache empty;
    g_r3 = std::move(empty);
}

const RunRes &run3_cached(Spec &sp, const std::vector<u32> &optvals) {
    if (g_r3.valid && g_r3.sp == &sp && g_r3.fmac == g_fmac &&
        g_r3.fmac_all == g_fmac_all && g_r3.opt == optvals) {
        sp.opt = &optvals;
        for (int i = 0; i < FM_N; i++) *FM_CTRS[i] += g_r3.d[i];
        g_r3_hit++;
        return g_r3.R;
    }
    run3_cache_clear();
    long long c0[FM_N];
    for (int i = 0; i < FM_N; i++) c0[i] = *FM_CTRS[i];
    sp.run3(optvals, g_r3.R);
    for (int i = 0; i < FM_N; i++) g_r3.d[i] = *FM_CTRS[i] - c0[i];
    g_r3.sp = &sp;
    g_r3.opt = optvals;
    g_r3.fmac = g_fmac;
    g_r3.fmac_all = g_fmac_all;
    g_r3.valid = true;
    g_r3_miss++;
    return g_r3.R;
}

void Spec::run3(const std::vector<u32> &optvals, RunRes &R) {
    const OpSets &T = S();
    int n = p->n;
    run(optvals, R);

    succ_of(R, R.succ);

    R.guard.assign((size_t)n, TRI_U);
    for (int i : R.reach)
        R.guard[(size_t)i] = nopred[(size_t)i]
            ? TRI_T
            : predval(R.vals[(size_t)i], pnum[(size_t)i], pinv[(size_t)i]);

    if (copyprop) copyprop_pass(R);
    else R.env.assign((size_t)n, EMap());

    R.fmac.assign((size_t)n, -1);
    R.fmac_slot.assign((size_t)n, 0);
    if (g_fmac && copyprop) {
        for (int i : R.reach) {
            int j = -1, slot = 0;
            if (fmac_ok(R, i, &j, &slot)) {
                R.fmac[(size_t)i] = j;
                R.fmac_slot[(size_t)i] = (int8_t)slot;
            }
        }
    }

    (void)T;
    dce_pass(R);
    if (g_fmac)
        for (int i : R.kept) if (R.fmac[(size_t)i] >= 0) g_fm_want++;

    for (int round = 0; g_fmac && !g_fmac_all && round < 4; round++) {
        bool again = false;
        for (int i : R.reach) {
            int j = R.fmac[(size_t)i];
            if (j >= 0 && R.need[(size_t)j]) {
                R.fmac[(size_t)i] = -1; again = true; g_fm_revert++;
            }
        }
        if (!again) break;
        dce_pass(R);
    }
    if (g_fmac) {
        g_fm_progs++;
        for (int i : R.kept) if (R.fmac[(size_t)i] >= 0) g_fm_final++;
    }
}

void Spec::dce_pass(RunRes &R) {
    const OpSets &T = S();
    int n = p->n;
    R.gen.assign((size_t)n, Mask());
    R.kill.assign((size_t)n, Mask());
    R.noop.assign((size_t)n, 0);

    for (int i : R.reach) {
        Tri g = R.guard[(size_t)i];
        if (g == TRI_F) continue;
        const EMap &e = R.env[(size_t)i];
        bool noop = false;
        if (g == TRI_T) {
            int c = copy_src[(size_t)i];
            if (c >= 0) {
                int d = c >> 8, sr = c & 0xFF;
                auto it = e.find(sr);
                int32_t a = (it != e.end()) ? it->second : sr;
                if (a == d) noop = true;
            } else if (lmfwd && lm[(size_t)i].valid) {
                const LmSlot &sl = lm[(size_t)i];
                if (!sl.store && sl.w == 1) {
                    auto it = e.find(LMBASE + sl.off);
                    if (it != e.end() && it->second == (int32_t)(p->q[i] & 0xFF))
                        noop = true;
                }
            } else if (cbfold && cb_src_d[(size_t)i] >= 0) {
                auto it = e.find(cb_src_d[(size_t)i]);
                if (it != e.end() && it->second == cb_src_key[(size_t)i])
                    noop = true;
            }
        }
        R.noop[(size_t)i] = (char)noop;
        if (noop) continue;

        const VMap &v = R.vals[(size_t)i];
        const std::vector<int> *drop = nullptr;
        int gp = -1;
        if (g == TRI_T) {
            R.kill[(size_t)i] = dall_mask[(size_t)i];
            drop = &maydef_set[(size_t)i];
            int pn = pnum[(size_t)i];
            gp = (nopred[(size_t)i] || pn == PT) ? -1 : PREG + pn;
        } else {
            R.kill[(size_t)i] = def_mask[(size_t)i];
        }
        bool rw = !norw[(size_t)i];
        bool texop = tex_rw[(size_t)i];
        int cbslot = cbfold_slot(i, e);
        int cbreg = (cbslot >= 0) ? (int)((p->q[i] >> cbslot) & 0xFF) : -1;
        Mask m;
        std::vector<int> eff;
        const std::vector<int> *ul = &use_list[(size_t)i];
        if (!R.fmac.empty() && R.fmac[(size_t)i] >= 0) {
            fmac_uses(R, i, eff);
            ul = &eff;
        }
        for (int r : *ul) {
            if (r == gp) continue;
            if (drop && std::binary_search(drop->begin(), drop->end(), r)) continue;
            if (r >= LMBIT) { m.set(r); continue; }
            if (r >= PREG) {
                if (vmap_get(v, r)) continue;
                m.set(r);
                continue;
            }
            const u32 *x = vmap_get(v, r);
            if (x && *x == 0 && rw && !texop) continue;
            int32_t a = r;
            if (rw) {
                auto it = e.find(r);
                if (it != e.end()) a = it->second;
            }
            if (a == RZ) {

                if (!texop) continue;
                a = r;
            }
            if (a < 0) {

                if (r == cbreg) continue;
                a = r;
            }
            m.set(a);
        }
        R.gen[(size_t)i] = m;
    }

    std::vector<int> div_sorted;
    for (int i : R.reach) {
        if (R.guard[(size_t)i] == TRI_F) continue;
        if (is_branchy[(size_t)i] && R.succ[(size_t)i].size() > 1)
            div_sorted.push_back(i);
    }
    std::unordered_map<int, char> need_push;
    std::set<std::pair<int, int>> kept_push_tgt;
    for (int i : R.reach) {
        if (!is_pushy[(size_t)i] || R.guard[(size_t)i] == TRI_F) continue;
        int t = tgt[(size_t)i];
        char v;
        if (t < 0) v = 1;
        else {
            size_t k = (size_t)(std::upper_bound(div_sorted.begin(),
                                                 div_sorted.end(), i) -
                                div_sorted.begin());
            v = (char)(k < div_sorted.size() && div_sorted[k] < t);
        }
        need_push[i] = v;
        if (v) kept_push_tgt.insert({cat[(size_t)i], tgt[(size_t)i]});
    }

    std::vector<char> base((size_t)n, 0);
    for (int i : R.reach) {
        if (R.guard[(size_t)i] == TRI_F) { base[(size_t)i] = 0; continue; }
        int nm = p->op[i];
        if (is_se[(size_t)i]) base[(size_t)i] = 1;
        else if (is_free[(size_t)i]) base[(size_t)i] = 0;
        else if (is_pushy[(size_t)i]) base[(size_t)i] = need_push[i];
        else if (is_branchy[(size_t)i]) {
            const std::vector<int> &sc = R.succ[(size_t)i];
            if (sc.size() > 1) base[(size_t)i] = 1;
            else if (!sc.empty() && sc[0] <= i) base[(size_t)i] = 1;
            else if (nm == T.O_Sync)
                base[(size_t)i] = (char)kept_push_tgt.count(
                    {C_SSY, sc.empty() ? -1 : sc[0]});
            else if (nm == T.O_Brk)
                base[(size_t)i] = (char)kept_push_tgt.count(
                    {C_PBK, sc.empty() ? -1 : sc[0]});
            else base[(size_t)i] = 0;
        } else base[(size_t)i] = 0;
    }

    R.live_in.assign((size_t)n, Mask());
    R.need = base;
    R.dead2.assign((size_t)n, 0);
    for (int i : R.reach)
        R.dead2[(size_t)i] = (char)(R.guard[(size_t)i] == TRI_F || R.noop[(size_t)i]);
    for (int i : R.reach) if (R.dead2[(size_t)i]) R.need[(size_t)i] = 0;
    if (stl_is_se)
        for (int i : R.reach)
            if (p->op[i] == T.O_Stl && !R.dead2[(size_t)i]) R.need[(size_t)i] = 1;

    std::vector<int> order(R.reach.rbegin(), R.reach.rend());
    int rounds = 0;
    bool converged = false;
    Mask lo, li;
    for (int rnd = 0; rnd < 512; rnd++) {
        rounds++;
        bool changed = false;
        for (int i : order) {
            lo.clear();
            for (int t : R.succ[(size_t)i]) lo |= R.live_in[(size_t)t];
            if (R.dead2[(size_t)i]) {
                if (lo != R.live_in[(size_t)i]) { R.live_in[(size_t)i] = lo; changed = true; }
                continue;
            }
            if (cat[(size_t)i] == C_EXIT) lo |= exit_mask;
            bool nd = R.need[(size_t)i] ||
                      dall_mask[(size_t)i].intersects(lo);
            if (nd) { li = lo; li.andnot_or(R.kill[(size_t)i], R.gen[(size_t)i]); }
            else li = lo;
            if (li != R.live_in[(size_t)i]) { R.live_in[(size_t)i] = li; changed = true; }
            if ((char)nd != R.need[(size_t)i]) { R.need[(size_t)i] = (char)nd; changed = true; }
        }
        if (!changed) { converged = true; break; }
    }
    if (!converged) fail("DVE fixpoint did not converge in 512 sweeps");
    R.rounds = rounds;

    R.kept.clear();
    for (int i : R.reach) if (R.need[(size_t)i]) R.kept.push_back(i);


}

}
