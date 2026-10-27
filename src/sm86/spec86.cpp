
#include "../uber.h"
#include "../spec.h"
#include <cstring>
#include <algorithm>

namespace ub {

using sm86::Inst;
using sm86::Operand;

namespace {

struct Ops {
    Inst in;
    Operand o[sm86::MAX_OPNDS];
    int n = 0;
    bool ok = false;
};

Ops decode_ops(const sm86::Word &q) {
    Ops r;
    r.ok = sm86::decode(q, &r.in);
    if (r.ok) r.n = sm86::operands(r.in, r.o, sm86::MAX_OPNDS);
    return r;
}

int op_key(const Operand &o) {
    switch (o.kind) {
    case sm86::O_GPR: return (int)o.reg;
    case sm86::O_UR: return o.reg >= 63 ? RZ : sm86::KEY_UR + (int)o.reg;
    case sm86::O_PRED: return o.reg >= 7 ? PT : sm86::KEY_P + (int)o.reg;
    case sm86::O_UPRED: return o.reg >= 7 ? PT : sm86::KEY_UP + (int)o.reg;
    default: return -1;
    }
}

}

template <>
int SpecT<Sm86>::cbfold_slot(int i, const EMap &env) const {
    (void)i; (void)env;
    return -1;
}

template <>
bool SpecT<Sm86>::fmac_ok(const RunRes &R, int i, int *jout, int *slotout) const {
    (void)R; (void)i; (void)jout; (void)slotout;
    return false;
}
template <>
sm86::Word SpecT<Sm86>::fmac_word(const RunRes &R, int i, int j, int slot) const {
    (void)R; (void)i; (void)j; (void)slot;
    fail("sm86 fmac_word: contraction is disabled");
}
template <>
void SpecT<Sm86>::fmac_uses(const RunRes &R, int i, std::vector<int> &out) const {
    (void)R; (void)i;
    out.clear();
}
template <>
bool SpecT<Sm86>::fmac_mul_ok(int j) const { (void)j; return false; }
template <>
void SpecT<Sm86>::fmac_mul_srcs(int j, int *ma, int *mb) const {
    (void)j;
    *ma = RZ; *mb = RZ;
}

template <>
bool SpecT<Sm86>::srcbval(sm86::Word q, const VMap &v, u32 *out) const {
    (void)q; (void)v; (void)out;
    return false;
}

template <>
void SpecT<Sm86>::lop_out(sm86::Word q, int lop, bool ha, u32 a, bool hb, u32 b, int d,
                          int pd, int pop, EvalOut &out) const {
    (void)q; (void)lop; (void)ha; (void)a; (void)hb; (void)b; (void)d; (void)pd; (void)pop;
    (void)out;
}

namespace {

struct Spec86Reader {
    const SpecT<Sm86> *sp;
    const VMap *v;

    bool reg_u32(int key, u32 *out) const {
        if (key == RZ || key < 0) { *out = 0; return true; }
        const u32 *x = vmap_get(*v, key);
        if (!x) return false;
        *out = *x;
        return true;
    }

    bool src(const Ops &w, const char *name, u32 *out) const {
        for (int k = 0; k < w.n; k++) {
            const Operand &o = w.o[k];
            if (!o.name || std::strcmp(o.name, name)) continue;
            u32 val;
            switch (o.kind) {
            case sm86::O_GPR:
            case sm86::O_UR:
            case sm86::O_PRED:
            case sm86::O_UPRED:
                if (!reg_u32(op_key(o), &val)) return false;
                break;
            case sm86::O_IMM:
            case sm86::O_FIMM:
                val = (u32)o.imm;
                break;
            case sm86::O_CBUF:
            case sm86::O_UCBUF: {

                int bank = -1; long long addr = -1; bool idx = false;
                for (int j = 0; j < w.n; j++) {
                    if (w.o[j].parent != k) continue;
                    if (w.o[j].kind == sm86::O_IMM && std::strstr(w.o[j].name, "bank")) bank = (int)w.o[j].imm;
                    else if (w.o[j].kind == sm86::O_IMM && std::strstr(w.o[j].name, "addr")) addr = w.o[j].imm;
                    else if (w.o[j].kind == sm86::O_GPR || w.o[j].kind == sm86::O_UR) idx = true;
                }
                if (idx || bank < 0 || addr < 0) return false;
                if (!sp->cb(bank, (int)addr, &val)) return false;
                break;
            }
            default:
                return false;
            }
            if (o.flags & sm86::F_NEG) val = (u32)(-(int32_t)val);
            if (o.flags & (sm86::F_INV | sm86::F_NOT)) val = ~val;
            *out = val;
            return true;
        }
        return false;
    }

    Tri pred(const Ops &w, const char *name) const {
        for (int k = 0; k < w.n; k++) {
            const Operand &o = w.o[k];
            if (!o.name || std::strcmp(o.name, name)) continue;
            if (o.kind != sm86::O_PRED && o.kind != sm86::O_UPRED) return TRI_U;
            int reg = (int)o.reg;
            bool inv = (o.flags & sm86::F_NOT) != 0;
            if (reg == 7) return inv ? TRI_F : TRI_T;
            const u32 *x = vmap_get(*v, op_key(o));
            if (!x) return TRI_U;
            bool b = (*x != 0) != inv;
            return b ? TRI_T : TRI_F;
        }
        return TRI_U;
    }

    int getv(const Ops &w, const char *name, int dflt) const {
        int vi = sm86::val_index(w.in.cls, name);
        return vi < 0 ? dflt : (int)sm86::get(w.in, vi);
    }

    int data_srcs(const Ops &w, u32 *out, int max, bool *known) const {
        int m = 0;
        *known = true;
        for (int k = 0; k < w.n && m < max; k++) {
            const Operand &o = w.o[k];
            if (o.parent >= 0) continue;
            bool is_imm = o.kind == sm86::O_IMM || o.kind == sm86::O_FIMM ||
                          o.kind == sm86::O_CBUF || o.kind == sm86::O_UCBUF;

            if (!is_imm && o.role != sm86::R_USE && o.role != sm86::R_DEFUSE) continue;
            u32 val;
            bool ok;
            switch (o.kind) {
            case sm86::O_GPR: case sm86::O_UR:
                ok = reg_u32(op_key(o), &val); break;
            case sm86::O_IMM: case sm86::O_FIMM:
                val = (u32)o.imm; ok = true; break;
            case sm86::O_CBUF: case sm86::O_UCBUF: {
                int bank = -1; long long addr = -1; bool idx = false;
                for (int j = 0; j < w.n; j++) {
                    if (w.o[j].parent != k) continue;
                    if (w.o[j].kind == sm86::O_IMM && std::strstr(w.o[j].name, "bank")) bank = (int)w.o[j].imm;
                    else if (w.o[j].kind == sm86::O_IMM && std::strstr(w.o[j].name, "addr")) addr = w.o[j].imm;
                    else if (w.o[j].kind == sm86::O_GPR || w.o[j].kind == sm86::O_UR) idx = true;
                }
                ok = !idx && bank >= 0 && addr >= 0 && sp->cb(bank, (int)addr, &val);
                break;
            }
            default:
                continue;
            }
            if (!ok) { *known = false; out[m++] = 0; continue; }
            if (o.flags & sm86::F_NEG) val = (u32)(-(int32_t)val);
            if (o.flags & (sm86::F_INV | sm86::F_NOT)) val = ~val;
            out[m++] = val;
        }
        return m;
    }
};

bool icmp86(int op, u32 a, u32 b, bool sgn, bool *out) {
    int32_t sa = (int32_t)a, sb = (int32_t)b;
    switch (op) {
    case 1: *out = sgn ? (sa < sb) : (a < b); return true;
    case 2: *out = (a == b); return true;
    case 3: *out = sgn ? (sa <= sb) : (a <= b); return true;
    case 4: *out = sgn ? (sa > sb) : (a > b); return true;
    case 5: *out = (a != b); return true;
    case 6: *out = sgn ? (sa >= sb) : (a >= b); return true;
    default: return false;
    }
}
Tri bop86(int op, Tri x, Tri y) {

    if (op == 0) { if (x == TRI_F || y == TRI_F) return TRI_F; if (x == TRI_T && y == TRI_T) return TRI_T; return TRI_U; }
    if (op == 1) { if (x == TRI_T || y == TRI_T) return TRI_T; if (x == TRI_F && y == TRI_F) return TRI_F; return TRI_U; }
    if (op == 2) { if (x == TRI_U || y == TRI_U) return TRI_U; return (x != y) ? TRI_T : TRI_F; }
    return TRI_U;
}
Tri notTri86(Tri x) { return x == TRI_U ? TRI_U : (x ? TRI_F : TRI_T); }

struct Op86Ids {
    int mov, umov, r2ur, cs2r, imad, uimad, iadd3, uiadd3, imnmx, sel, usel, shf, ushf,
        lop3, ulop3, plop3, uplop3, uisetp, uldc;
    Op86Ids() {
        auto id = [](const char *n) { return sm86::op_id(n); };
        mov = id("MOV"); umov = id("UMOV"); r2ur = id("R2UR"); cs2r = id("CS2R");
        imad = id("IMAD"); uimad = id("UIMAD"); iadd3 = id("IADD3"); uiadd3 = id("UIADD3");
        imnmx = id("IMNMX"); sel = id("SEL"); usel = id("USEL"); shf = id("SHF"); ushf = id("USHF");
        lop3 = id("LOP3"); ulop3 = id("ULOP3"); plop3 = id("PLOP3"); uplop3 = id("UPLOP3");
        uisetp = id("UISETP"); uldc = id("ULDC");
    }
};
const Op86Ids &op86() { static Op86Ids o; return o; }

u32 funnel_shift(u32 lo, u32 hi, u32 sh, bool left, bool arith, bool take_hi) {
    sh &= 63;
    uint64_t v = ((uint64_t)hi << 32) | lo;
    uint64_t r;
    if (left) r = (sh >= 64) ? 0 : (v << sh);
    else {
        if (arith && (hi & 0x80000000u)) {
            int64_t s = (int64_t)v;
            r = (uint64_t)(sh >= 63 ? (s >> 63) : (s >> sh));
        } else r = (sh >= 64) ? 0 : (v >> sh);
    }
    return take_hi ? (u32)(r >> 32) : (u32)r;
}

}

template <>
void SpecT<Sm86>::eval5(int i, const VMap &v, EvalOut &out) const {
    Ops w = decode_ops(p->q[i]);
    if (!w.ok) return;
    int nm = p->op[i];
    const OpSets &T = Sm86::sets();
    Spec86Reader R{this, &v};

    auto dest_key = [&]() -> int {
        for (int k = 0; k < w.n; k++)
            if ((w.o[k].kind == sm86::O_GPR || w.o[k].kind == sm86::O_UR) &&
                (w.o[k].role == sm86::R_DEF || w.o[k].role == sm86::R_DEFUSE))
                return op_key(w.o[k]);
        return -1;
    };

    u32 s[4]; bool known;
    int ns = R.data_srcs(w, s, 4, &known);

    if (nm == op86().mov || nm == op86().umov || nm == op86().r2ur) {
        if (nm == op86().mov && R.getv(w, "PixMaskU04", 0xf) != 0xf) return;
        int d = dest_key();
        if (known && ns >= 1 && d >= 0) out.put(d, s[0]);
        return;
    }
    if (nm == op86().cs2r) {

        int sra = R.getv(w, "SRa", 255);
        if (sra != 255) return;
        int d = dest_key();
        int sz = R.getv(w, "sz", 1);
        if (d >= 0) { out.put(d, 0); if (sz == 2 && is_gpr_key(d)) out.put(d + 1, 0); }
        return;
    }

    if (nm == op86().imad || nm == op86().uimad) {
        if (R.getv(w, "wide", 0) != 0) return;
        if (R.getv(w, "X", 0) != 0) return;
        int d = dest_key();
        if (known && ns >= 3 && d >= 0) out.put(d, (u32)((uint64_t)s[0] * s[1] + s[2]) & M32);
        return;
    }
    if (nm == op86().iadd3 || nm == op86().uiadd3) {
        if (R.getv(w, "X", 0) != 0) return;
        int d = dest_key();
        if (!known || d < 0) return;
        u32 r = 0;
        for (int k = 0; k < ns; k++) r += s[k];
        out.put(d, r & M32);
        return;
    }
    if (nm == op86().imnmx) {
        Tri pv = R.pred(w, "Pp");
        if (pv == TRI_U) pv = R.pred(w, "UPp");
        int d = dest_key();
        if (!known || ns < 2 || pv == TRI_U || d < 0) return;
        bool sgn = R.getv(w, "fmt", 1) != 0;
        u32 r;
        if (sgn) { int32_t aa = (int32_t)s[0], bb = (int32_t)s[1]; r = (u32)(pv ? std::min(aa, bb) : std::max(aa, bb)); }
        else r = pv ? std::min(s[0], s[1]) : std::max(s[0], s[1]);
        out.put(d, r & M32);
        return;
    }
    if (nm == op86().sel || nm == op86().usel) {
        Tri pv = R.pred(w, "Pp");
        if (pv == TRI_U) pv = R.pred(w, "UPp");
        int d = dest_key();
        if (pv == TRI_U || !known || ns < 2 || d < 0) return;
        out.put(d, (pv ? s[0] : s[1]) & M32);
        return;
    }
    if (nm == op86().shf || nm == op86().ushf) {
        int d = dest_key();
        if (!known || ns < 3 || d < 0) return;

        u32 a = s[0], sh = s[1], c = s[2];
        bool left = R.getv(w, "dir", 0) == 0;
        int fmt = R.getv(w, "fmt", 3);
        bool hilo = R.getv(w, "hilo", 0) != 0;

        u32 lo = left ? a : c, hi = left ? c : a;
        out.put(d, funnel_shift(lo, hi, sh, left, fmt == 2, hilo));
        return;
    }
    if (nm == op86().lop3 || nm == op86().ulop3) {
        if (!known || ns < 3) return;
        u32 a = s[0], b = s[1], c = s[2];
        int lut = R.getv(w, "imm8", -1);
        if (lut < 0) return;

        u32 r = 0;
        for (int bit = 0; bit < 32; bit++) {
            int idx = (((a >> bit) & 1) << 2) | (((b >> bit) & 1) << 1) | ((c >> bit) & 1);
            if ((lut >> idx) & 1) r |= (u32)1 << bit;
        }
        int d = dest_key();
        if (d >= 0) out.put(d, r);

        for (int k = 0; k < w.n; k++)
            if (w.o[k].kind == sm86::O_PRED && w.o[k].role == sm86::R_DEF && w.o[k].reg != 7)
                out.put(op_key(w.o[k]), r != 0 ? 1u : 0u);
        return;
    }
    if (nm == op86().plop3 || nm == op86().uplop3) {
        Tri pp = R.pred(w, "Pp"), pq = R.pred(w, "Pq");
        Tri pr = R.pred(w, "Pr");
        if (pr == TRI_U) pr = R.pred(w, "UPr");
        int lut = R.getv(w, "uimm8", -1);
        int lut2 = R.getv(w, "vimm8", 0);
        if (lut < 0 || pp == TRI_U || pq == TRI_U || pr == TRI_U) return;
        int idx = ((pp ? 1 : 0) << 2) | ((pq ? 1 : 0) << 1) | (pr ? 1 : 0);
        Tri ru = ((lut >> idx) & 1) ? TRI_T : TRI_F;
        Tri rv = ((lut2 >> idx) & 1) ? TRI_T : TRI_F;
        for (int k = 0; k < w.n; k++) {
            if ((w.o[k].kind == sm86::O_PRED || w.o[k].kind == sm86::O_UPRED) &&
                w.o[k].role == sm86::R_DEF && w.o[k].reg != 7) {
                const char *nmv = w.o[k].name;
                if (nmv && (!std::strcmp(nmv, "Pu") || !std::strcmp(nmv, "UPu")))
                    out.put(op_key(w.o[k]), ru ? 1u : 0u);
                else if (nmv && (!std::strcmp(nmv, "Pv") || !std::strcmp(nmv, "UPv")))
                    out.put(op_key(w.o[k]), rv ? 1u : 0u);
            }
        }
        return;
    }

    if (nm == T.O_Isetp || nm == op86().uisetp) {
        if (R.getv(w, "X", 0) != 0) return;
        bool sgn = R.getv(w, "fmt", 0) != 0;
        int icmp = R.getv(w, "icmp", 0), bopc = R.getv(w, "bop", 0);
        Tri c = TRI_U;
        if (known && ns >= 2) { bool r; if (icmp86(icmp, s[0], s[1], sgn, &r)) c = r ? TRI_T : TRI_F; }
        Tri pp = R.pred(w, "Pp");
        if (pp == TRI_U) pp = R.pred(w, "UPp");
        Tri r0 = bop86(bopc, c, pp);
        Tri r1 = bop86(bopc, notTri86(c), pp);
        for (int k = 0; k < w.n; k++) {
            if ((w.o[k].kind != sm86::O_PRED && w.o[k].kind != sm86::O_UPRED) ||
                w.o[k].role != sm86::R_DEF || w.o[k].reg == 7) continue;
            const char *nmv = w.o[k].name;
            Tri rr = (nmv && (!std::strcmp(nmv, "Pv") || !std::strcmp(nmv, "UPv"))) ? r1 : r0;
            if (rr != TRI_U) out.put(op_key(w.o[k]), (u32)rr);
        }
        return;
    }

    if (nm == T.O_Ldc) {
        int bank = R.getv(w, "Sa_bank", -1);
        if (bank != 1 && bank != this->bank) return;
        if (bank == 1 && !fold_blob) return;
        int ra = R.getv(w, "Ra", 255);
        u32 base = 0;
        if (ra != 255) { const u32 *x = vmap_get(v, ra); if (!x) return; base = *x; }
        int off = R.getv(w, "Ra_offset", 0);
        u32 x;
        if (!cb(bank, (int)((base + (u32)off) & M32), &x)) return;
        int d = dest_key();
        if (d >= 0) out.put(d, x);
        return;
    }
    if (nm == op86().uldc) {
        int bank = R.getv(w, "Sa_bank", -1);
        if (bank != 1 && bank != this->bank) return;
        if (bank == 1 && !fold_blob) return;

        u32 addr = 0; bool have = false;
        int ad = sm86::val_index(w.in.cls, "Sa_addr");
        if (ad >= 0) { addr = (u32)sm86::get(w.in, ad); have = true; }
        else {
            int ura = sm86::val_index(w.in.cls, "URa");
            if (ura >= 0) {
                const u32 *x = vmap_get(v, sm86::KEY_UR + (int)sm86::get(w.in, ura));
                if (!x) return;
                int off = R.getv(w, "Sa_offset", 0);
                addr = (*x + (u32)off) & M32; have = true;
            }
        }
        if (!have) return;
        int d = dest_key();
        if (d < 0) return;
        int nd = R.getv(w, "sz", 4) == 5 ? 2 : (R.getv(w, "sz", 4) == 6 ? 4 : 1);
        for (int k = 0; k < nd; k++) {
            u32 x;
            if (!cb(bank, (int)((addr + 4u * k) & M32), &x)) return;
            out.put(d + k, x);
        }
        return;
    }
}

template <>
void SpecT<Sm86>::eval(int i, const VMap &v, EvalOut &out) const {
    eval5(i, v, out);
}

}
