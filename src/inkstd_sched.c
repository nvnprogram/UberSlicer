
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#ifdef _MSC_VER
#include <intrin.h>

#endif

#ifdef INKV_LIB

#else
typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;
#endif

#include "sm50tab.h"

#define INSTR_START 0x80

#define RZ 255
#define PT 7

#ifndef INKV_LIB

#endif

static void *grow_arr(void *p, size_t elem, int oldcap, int newcap) {
    void *np = malloc(elem * (size_t)newcap);
    if (p) {
        memcpy(np, p, elem * (size_t)oldcap);
        free(p);
    }
    return np;
}

static int op_of(u64 q) {
    return SM50_TAB_NAME[q >> 50];
}
static unsigned props_of(u64 q) {
    return SM50_TAB_PROPS[q >> 50];
}

static int nm_is(u64 q, int op) { return (int)SM50_TAB_NAME[q >> 50] == op; }

static int gpr_fields(u64 q, int *offs) {
    unsigned p = props_of(q);
    int mov = nm_is(q, OP_Mov);
    int n = 0, tmp[8], i, j;
    if (p & PROP_RD)  tmp[n++] = 0;
    if (p & PROP_RA)  tmp[n++] = mov ? 20 : 8;
    if (p & PROP_RB)  tmp[n++] = 20;
    if (p & PROP_RC)  tmp[n++] = 39;
    if (p & PROP_RD2) tmp[n++] = 28;
    if (p & PROP_RB2) tmp[n++] = 39;

    int m = 0;
    for (i = 0; i < n; i++) {
        int v = tmp[i], dup = 0;
        for (j = 0; j < m; j++) if (offs[j] == v) { dup = 1; break; }
        if (!dup) offs[m++] = v;
    }
    for (i = 0; i < m; i++)
        for (j = i + 1; j < m; j++)
            if (offs[j] < offs[i]) { int t = offs[i]; offs[i] = offs[j]; offs[j] = t; }
    return m;
}

static int _rd(u64 q) { return q & 0xFF; }
static int _ra(u64 q) { return (q >> 8) & 0xFF; }
static int _rb(u64 q) { return (q >> 20) & 0xFF; }
static int _rc(u64 q) { return (q >> 39) & 0xFF; }
static int _pred(u64 q) { return (q >> 16) & 7; }
static int _pinv(u64 q) { return (q >> 19) & 1; }
static int cbuf_bank(u64 q) { return (q >> 34) & 0x1F; }
static int cbuf_off(u64 q) { return ((q >> 20) & 0x3FFF) << 2; }
static u32 imm20f_bits(u64 q) {
    u32 raw20 = (u32)(((q >> 37) & 0x80000) | ((q >> 20) & 0x7FFFF));
    return raw20 << 12;
}
static u32 imm32(u64 q) { return (u32)((q >> 20) & 0xFFFFFFFF); }

enum { FORM_IMM, FORM_CBUF, FORM_REG };
static int srcb_form(u64 q) {
    if (((q >> 61) & 7) == 1) return FORM_IMM;
    if (!((q >> 60) & 1)) return FORM_CBUF;
    return FORM_REG;
}

enum { OK_NONE, OK_REG, OK_CBUF, OK_IMM, OK_PRED };
typedef struct {
    int kind;
    int reg;
    int neg;
    int bank, off;
    u32 imm;
    int pnum;
} Op;

#define MAXOPS 8

static void op_reg(Op *o, int r, int neg) {
    o->kind = OK_REG; o->reg = (r == RZ) ? -1 : r; o->neg = neg;
    o->bank = o->off = -1; o->imm = 0; o->pnum = -1;
}
static void op_cbuf(Op *o, int bank, int off, int neg) {
    o->kind = OK_CBUF; o->reg = -1; o->neg = neg; o->bank = bank; o->off = off;
    o->imm = 0; o->pnum = -1;
}
static void op_imm(Op *o, u32 bits, int neg) {
    o->kind = OK_IMM; o->reg = -1; o->neg = neg; o->bank = o->off = -1;
    o->imm = bits; o->pnum = -1;
}
static void op_pred(Op *o, int pnum) {
    o->kind = OK_PRED; o->reg = -1; o->neg = 0; o->bank = o->off = -1;
    o->imm = 0; o->pnum = pnum;
}
static void op_none(Op *o) {
    o->kind = OK_NONE; o->reg = -1; o->neg = 0; o->bank = o->off = -1;
    o->imm = 0; o->pnum = -1;
}

static void op_srcb(Op *o, u64 q, int intimm) {
    int form = srcb_form(q);
    if (form == FORM_CBUF) op_cbuf(o, cbuf_bank(q), cbuf_off(q), 0);
    else if (form == FORM_IMM) {
        if (intimm) op_imm(o, (u32)(((q >> 37) & 0x80000) | ((q >> 20) & 0x7FFFF)), 0);
        else op_imm(o, imm20f_bits(q), 0);
    } else op_reg(o, _rb(q), 0);
}

static int decode_ops(u64 q, Op *ops) {
    if (q == 0) return 0;
    int nm = op_of(q);
    int n = 0;
    int nega, negc, negb, form;

    if (nm == OP_Ffma) {
        nega = (q >> 48) & 1; negc = (q >> 49) & 1;
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        if (((q >> 61) & 7) == 1) {
            op_imm(&ops[2], imm20f_bits(q), nega);
            op_reg(&ops[3], _rc(q), negc);
        } else if (!((q >> 60) & 1)) {
            op_cbuf(&ops[2], cbuf_bank(q), cbuf_off(q), nega);
            op_reg(&ops[3], _rc(q), negc);
        } else if (!((q >> 59) & 1)) {
            op_reg(&ops[2], _rc(q), nega);
            op_cbuf(&ops[3], cbuf_bank(q), cbuf_off(q), negc);
        } else {
            op_reg(&ops[2], _rb(q), nega);
            op_reg(&ops[3], _rc(q), negc);
        }
        return 4;
    }
    if (nm == OP_Fadd) {
        nega = (q >> 48) & 1; negb = (q >> 45) & 1;
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), nega);
        form = srcb_form(q);
        if (form == FORM_CBUF) op_cbuf(&ops[2], cbuf_bank(q), cbuf_off(q), negb);
        else if (form == FORM_IMM) op_imm(&ops[2], imm20f_bits(q), negb);
        else op_reg(&ops[2], _rb(q), negb);
        return 3;
    }
    if (nm == OP_Fmul) {
        nega = (q >> 48) & 1;
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        form = srcb_form(q);
        if (form == FORM_CBUF) op_cbuf(&ops[2], cbuf_bank(q), cbuf_off(q), nega);
        else if (form == FORM_IMM) op_imm(&ops[2], imm20f_bits(q), nega);
        else op_reg(&ops[2], _rb(q), nega);
        return 3;
    }
    if (nm == OP_Fmul32i) {
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        op_imm(&ops[2], imm32(q), 0);
        return 3;
    }
    if (nm == OP_Fadd32i) {
        nega = (q >> 56) & 1;
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), nega);
        op_imm(&ops[2], imm32(q), 0);
        return 3;
    }
    if (nm == OP_Mov32i) {
        op_reg(&ops[0], _rd(q), 0);
        op_imm(&ops[1], imm32(q), 0);
        return 2;
    }
    if (nm == OP_Mov) {
        op_reg(&ops[0], _rd(q), 0);
        if (!((q >> 60) & 1)) op_cbuf(&ops[1], cbuf_bank(q), cbuf_off(q), 0);
        else op_reg(&ops[1], _rb(q), 0);
        return 2;
    }
    if (nm == OP_Fmnmx) {
        nega = (q >> 48) & 1; negb = (q >> 45) & 1;
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), nega);
        form = srcb_form(q);
        if (form == FORM_CBUF) op_cbuf(&ops[2], cbuf_bank(q), cbuf_off(q), negb);
        else if (form == FORM_IMM) op_imm(&ops[2], imm20f_bits(q), 0);
        else op_reg(&ops[2], _rb(q), negb);
        op_pred(&ops[3], (q >> 39) & 7);
        return 4;
    }
    if (nm == OP_Fcmp) {
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        if (!((q >> 60) & 1)) { op_cbuf(&ops[2], cbuf_bank(q), cbuf_off(q), 0); op_reg(&ops[3], _rc(q), 0); }
        else if (!((q >> 59) & 1)) { op_reg(&ops[2], _rc(q), 0); op_cbuf(&ops[3], cbuf_bank(q), cbuf_off(q), 0); }
        else { op_reg(&ops[2], _rb(q), 0); op_reg(&ops[3], _rc(q), 0); }
        return 4;
    }
    if (nm == OP_Fset) {
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        op_srcb(&ops[2], q, 0);
        op_pred(&ops[3], (q >> 39) & 7);
        return 4;
    }
    if (nm == OP_Fsetp || nm == OP_Isetp) {
        op_pred(&ops[0], (q >> 3) & 7);
        op_pred(&ops[1], q & 7);
        op_reg(&ops[2], _ra(q), 0);
        if (nm == OP_Fsetp) {
            nega = (q >> 43) & 1; negb = (q >> 6) & 1;
            form = srcb_form(q);
            op_reg(&ops[2], _ra(q), nega);
            if (form == FORM_CBUF) op_cbuf(&ops[3], cbuf_bank(q), cbuf_off(q), negb);
            else if (form == FORM_IMM) op_imm(&ops[3], imm20f_bits(q), 0);
            else op_reg(&ops[3], _rb(q), negb);
        } else {
            op_srcb(&ops[3], q, 1);
        }
        op_pred(&ops[4], (q >> 39) & 7);
        return 5;
    }
    if (nm == OP_F2f || nm == OP_F2i || nm == OP_I2f || nm == OP_I2i) {
        op_reg(&ops[0], _rd(q), 0);
        op_srcb(&ops[1], q, 0);
        return 2;
    }
    if (nm == OP_Sel) {
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        op_srcb(&ops[2], q, 1);
        op_pred(&ops[3], (q >> 39) & 7);
        return 4;
    }
    if (nm == OP_Iset) {
        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        op_srcb(&ops[2], q, 1);
        op_pred(&ops[3], (q >> 39) & 7);
        return 4;
    }
    if (nm == OP_Ipa) {
        op_reg(&ops[0], _rd(q), 0);
        op_none(&ops[1]);
        op_reg(&ops[2], _rb(q), 0);
        return 3;
    }
    if (nm == OP_Texs || nm == OP_Tlds || nm == OP_Tld4s) {

        op_reg(&ops[0], _rd(q), 0);
        op_reg(&ops[1], _ra(q), 0);
        op_reg(&ops[2], _rb(q), 0);
        op_imm(&ops[3], (u32)((q >> 36) & 0x1FFF), 0);
        return 4;
    }

    if (nm == OP_Ast) {
        op_reg(&ops[n++], _rd(q), 0);
        op_reg(&ops[n++], _ra(q), 0);
        return n;
    }

    {
        unsigned p = props_of(q);
        int offs[8], m = gpr_fields(q, offs), i;
        if (p & PROP_RD) op_reg(&ops[n++], _rd(q), 0);
        for (i = 0; i < m; i++) if (offs[i] != 0) op_reg(&ops[n++], (q >> offs[i]) & 0xFF, 0);
        return n;
    }
}

typedef struct { u64 r[4]; u8 p; } RegSet;
static void rs_clear(RegSet *s) { s->r[0] = s->r[1] = s->r[2] = s->r[3] = 0; s->p = 0; }
static void rs_add_r(RegSet *s, int r) { if (r >= 0 && r < 255) s->r[r >> 6] |= (u64)1 << (r & 63); }
static void rs_add_p(RegSet *s, int p) { if (p >= 0 && p < 7) s->p |= (u8)1 << p; }

static void rs_or(RegSet *a, const RegSet *b) {
    a->r[0] |= b->r[0]; a->r[1] |= b->r[1]; a->r[2] |= b->r[2]; a->r[3] |= b->r[3]; a->p |= b->p;
}

static void rs_copy(RegSet *a, const RegSet *b) { *a = *b; }

static const int TEXS_MASKLUT[2][8] = {
    {0x1, 0x2, 0x4, 0x8, 0x3, 0x9, 0xA, 0xC},
    {0x7, 0xB, 0xD, 0xE, 0xF, 0x0, 0x0, 0x0},
};
static int popcount4(int x) { int c = 0; while (x) { c += x & 1; x >>= 1; } return c; }

static void tex_defs(u64 q, RegSet *out) {
    int nm = op_of(q);
    if (nm == OP_Texs || nm == OP_Tlds || nm == OP_Tld4s) {
        int dest = q & 0xFF, dest2 = (q >> 28) & 0xFF;
        int wm = nm == OP_Tld4s ? 4 : (int)((q >> 50) & 0x7);
        int comp = popcount4(TEXS_MASKLUT[dest2 == 255 ? 0 : 1][wm]), i;
        for (i = 0; i < comp; i++) {
            int high = i >> 1, low = i & 1;
            int rd = high ? dest2 : dest;
            if (rd != 255) rs_add_r(out, rd + low);
        }
        return;
    }
    if (nm == OP_Tex || nm == OP_Tld || nm == OP_Tld4 ||
        nm == OP_Tmml || nm == OP_Txq || nm == OP_Txd ||
        nm == OP_TexB || nm == OP_TldB || nm == OP_Tld4B ||
        nm == OP_TxdB || nm == OP_TxqB || nm == OP_TmmlB) {
        int dest = q & 0xFF, wm = (q >> 31) & 0xF, k = 0, bit;
        if (dest != 255)
            for (bit = 0; bit < 4; bit++) if (wm & (1 << bit)) rs_add_r(out, dest + k++);
        return;
    }
}

static const int TEXS_SRC[14][2] = {
    {1,0},{1,1},{1,1},{2,1},{2,1},{2,2},{2,1},{2,1},{2,1},{2,2},{2,1},{2,1},{2,1},{2,2}
};

static void tlds_src(int tgt, int *nA, int *nB) {
    switch (tgt) {
        case 0x0: *nA=1; *nB=0; return; case 0x1: *nA=1; *nB=1; return;
        case 0x2: *nA=1; *nB=1; return; case 0x4: *nA=1; *nB=2; return;
        case 0x5: *nA=2; *nB=1; return; case 0x6: *nA=1; *nB=2; return;
        case 0x7: *nA=2; *nB=1; return; case 0x8: *nA=2; *nB=1; return;
        case 0xc: *nA=2; *nB=2; return; default: *nA=2; *nB=2; return;
    }
}
static void tex_uses_texs(u64 q, RegSet *out) {
    int nm = op_of(q);
    int srcA = (q >> 8) & 0xFF, srcB = (q >> 20) & 0xFF, nA, nB, k;
    if (nm == OP_Tld4s) { nA = 2; nB = 1; }
    else {
        int tgt = (q >> 53) & 0xF;
        if (nm == OP_Texs) { nA = TEXS_SRC[tgt > 13 ? 13 : tgt][0]; nB = TEXS_SRC[tgt > 13 ? 13 : tgt][1]; }
        else tlds_src(tgt, &nA, &nB);
    }
    for (k = 0; k < nA; k++) if (srcA + k < 255) rs_add_r(out, srcA + k);
    for (k = 0; k < nB; k++) if (srcB + k < 255) rs_add_r(out, srcB + k);
}

static int is_tex_base(u64 q) {
    int nm = op_of(q);
    return nm == OP_Texs||nm == OP_Tlds||nm == OP_Tld4s||
           nm == OP_Tld4||nm == OP_Tld||nm == OP_Tex||
           nm == OP_Tmml||nm == OP_Txq||nm == OP_Txd||
           nm == OP_TexB||nm == OP_TldB||nm == OP_Tld4B||
           nm == OP_TxdB||nm == OP_TxqB||nm == OP_TmmlB;
}

static int is_no_dest(u64 q) {
    switch (op_of(q)) {
        case OP_Bra: case OP_Brx: case OP_Jmp: case OP_Jmx:
        case OP_Sync: case OP_Ssy: case OP_Brk: case OP_Pbk:
        case OP_Cont: case OP_Pcnt: case OP_Exit: case OP_Ret:
        case OP_Kil: case OP_Nop: case OP_Membar: case OP_Depbar:
        case OP_Bar: case OP_Red: case OP_St: case OP_Stg:
        case OP_Sts: case OP_Stl: case OP_Ast: case OP_Cctl: case OP_Cctll:
        case OP_Pexit: case OP_Cal: case OP_Jcal: case OP_Rtt:
        case OP_Setcrsptr: case OP_Plongjmp: case OP_Pret: case OP_Vote:
            return 1;
        default:
            return 0;
    }
}

static int _pb_widemem = 1;
static int mem_data_regs(u64 q) {
    if (!_pb_widemem) return 1;
    switch (op_of(q)) {
        case OP_Ldc: case OP_Ld: case OP_Ldg: case OP_Ldl: case OP_Lds:
        case OP_St:  case OP_Stg: case OP_Stl: case OP_Sts:
            break;
        default: return 1;
    }
    switch ((int)((q >> 48) & 7)) {
        case 5: return 2;
        case 6: case 7: return 4;
        default: return 1;
    }
}
static int mem_is_store(u64 q) {
    switch (op_of(q)) {
        case OP_St: case OP_Stg: case OP_Stl: case OP_Sts: return 1;
        default: return 0;
    }
}

static int _pb_preddst = 1;

static void parse_du(u64 q, RegSet *guard, RegSet *defs, RegSet *uses) {
    rs_clear(guard); rs_clear(defs); rs_clear(uses);
    if (q == 0) return;
    int pred = _pred(q), pinv = _pinv(q);

    int has_pred = !(nm_is(q, OP_Ssy) || nm_is(q, OP_Pbk) || nm_is(q, OP_Pcnt));
    int predicated = has_pred && ((pred != PT) || pinv);
    if (has_pred && pred != PT) { rs_add_p(guard, pred); }

    Op ops[MAXOPS];
    int nops = decode_ops(q, ops);
    int nm = op_of(q);
    int has_dest = !is_no_dest(q) && nops > 0;

    #define ADD_USES(lo_, hi_) do { for (int _i = (lo_); _i < (hi_); _i++) { \
        if (ops[_i].kind == OK_REG && ops[_i].reg >= 0) rs_add_r(uses, ops[_i].reg); \
        else if (ops[_i].kind == OK_PRED && ops[_i].pnum != PT) rs_add_p(uses, ops[_i].pnum); } } while (0)

    if (!has_dest) {
        ADD_USES(0, nops);

        if (mem_is_store(q) && nops > 0 && ops[0].kind == OK_REG && ops[0].reg >= 0 && ops[0].reg < 255) {
            int nw = mem_data_regs(q);
            for (int w = 1; w < nw && ops[0].reg + w < 255; w++) rs_add_r(uses, ops[0].reg + w);
        }
    } else if (ops[0].kind == OK_PRED) {

        if (!predicated) rs_add_p(defs, ops[0].pnum);
        if (nops > 1 && ops[1].kind == OK_PRED && ops[1].pnum != PT) {
            if (!predicated) rs_add_p(defs, ops[1].pnum);
            ADD_USES(2, nops);
        } else {
            ADD_USES(1, nops);
        }
        if (predicated) ADD_USES(0, nops);
    } else if (is_tex_base(q)) {
        RegSet dests; rs_clear(&dests);
        tex_defs(q, &dests);
        if (predicated) rs_or(uses, &dests);
        else rs_or(defs, &dests);
        if (nm == OP_Texs||nm == OP_Tlds||nm == OP_Tld4s) {
            RegSet u2; rs_clear(&u2); tex_uses_texs(q, &u2); rs_or(uses, &u2);
        } else {
            int srcA = (q >> 8) & 0xFF, nA, srcB, k;
            if (nm == OP_Txq || nm == OP_TxqB) { nA = 1; srcB = 255; }
            else if (nm == OP_Tmml || nm == OP_TmmlB) { nA = 2; srcB = 255; }
            else {
                srcB = (q >> 20) & 0xFF;
                int is_b = (nm==OP_TexB||nm==OP_TldB||nm==OP_Tld4B||nm==OP_TxdB);

                static const int dim_coords[8] = {1,2,2,3,3,3,3,4};
                int dim = (q >> 28) & 7;
                nA = dim_coords[dim];

                if ((q >> 50) & 1) nA++;

                int lod = is_b ? (int)((q >> 37) & 7) : (int)((q >> 55) & 7);

                if (lod == 2 || lod == 3) nA++;
            }
            for (k = 0; k < nA; k++) if (srcA + k < 255) rs_add_r(uses, srcA + k);
            if (srcB < 255) rs_add_r(uses, srcB);
        }
    } else if (ops[0].kind == OK_REG && ops[0].reg >= 0) {

        int nw = (ops[0].reg < 255) ? mem_data_regs(q) : 1;
        for (int w = 0; w < nw; w++) {
            int rr = ops[0].reg + w;
            if (w && rr >= 255) break;
            if (predicated) rs_add_r(uses, rr);
            else rs_add_r(defs, rr);
        }
        ADD_USES(1, nops);
        if (predicated) { if (ops[0].reg >= 0) rs_add_r(uses, ops[0].reg); }
    } else {
        ADD_USES(0, nops);
    }

    if (_pb_preddst) {
        unsigned _pr = props_of(q);
        if ((_pr & (PROP_PD | PROP_LPD)) == PROP_LPD) {
            int _pn = (int)((q >> 48) & 7);
            if (_pn != PT) {
                if (predicated) rs_add_p(uses, _pn);
                else            rs_add_p(defs, _pn);
            }
        }

        {
            int _nm = op_of(q);
            if (_nm == OP_Fsetp || _nm == OP_Isetp || _nm == OP_Dsetp ||
                _nm == OP_Hsetp2 || _nm == OP_Csetp || _nm == OP_Psetp ||
                _nm == OP_Vsetp) {
                int _p0 = (int)((q >> 3) & 7), _p1 = (int)(q & 7);
                if (_p0 != PT) { if (predicated) rs_add_p(uses, _p0); else rs_add_p(defs, _p0); }
                if (_p1 != PT) { if (predicated) rs_add_p(uses, _p1); else rs_add_p(defs, _p1); }
            }
        }
    }
    rs_or(uses, guard);
    #undef ADD_USES
}

typedef struct { int n, cap; int *v; int inl[2]; } IdxList;

static void il_init(IdxList *l) { l->n = 0; l->cap = 2; l->v = l->inl; }
static void il_free(IdxList *l) { if (l->v != l->inl) free(l->v); }
static void il_add(IdxList *l, int j) {
    for (int k = 0; k < l->n; k++) if (l->v[k] == j) return;
    if (l->n >= l->cap) {
        int nc = l->cap * 2;
        if (l->v == l->inl) {
            int *nv = (int *)malloc(sizeof(int) * nc);
            memcpy(nv, l->inl, sizeof(int) * l->n);
            l->v = nv;
        } else l->v = (int *)grow_arr(l->v, sizeof(int), l->cap, nc);
        l->cap = nc;
    }
    l->v[l->n++] = j;
}

typedef struct { int depth; u8 typ[40]; int tgt[40]; } Stk;

static int stk_eq(const Stk *a, const Stk *b) {
    if (a->depth != b->depth) return 0;
    for (int i = 0; i < a->depth; i++)
        if (a->typ[i] != b->typ[i] || a->tgt[i] != b->tgt[i]) return 0;
    return 1;
}

typedef struct {
    Stk *v; int n, cap;
    int *tab; u32 mask;
} StkPool;

static u32 stk_hash(const Stk *s) {
    u32 h = 2166136261u;
    h = (h ^ (u32)s->depth) * 16777619u;
    for (int i = 0; i < s->depth; i++) {
        h = (h ^ s->typ[i]) * 16777619u;
        h = (h ^ (u32)s->tgt[i]) * 16777619u;
    }
    return h;
}

static void sp_init(StkPool *p) {
    p->n = 0; p->cap = 64;
    p->v = (Stk *)malloc(sizeof(Stk) * p->cap);
    p->mask = 127;
    p->tab = (int *)malloc(sizeof(int) * 128);
    memset(p->tab, 0xFF, sizeof(int) * 128);
}
static void sp_free(StkPool *p) { free(p->v); free(p->tab); }

static int sp_intern(StkPool *p, const Stk *s) {
    u32 h = stk_hash(s), at = h & p->mask;
    while (p->tab[at] >= 0) {
        if (stk_eq(&p->v[p->tab[at]], s)) return p->tab[at];
        at = (at + 1) & p->mask;
    }
    if (p->n >= p->cap) {
        p->v = (Stk *)grow_arr(p->v, sizeof(Stk), p->cap, p->cap * 2);
        p->cap *= 2;
    }
    int idx = p->n++;
    p->v[idx] = *s;
    p->tab[at] = idx;
    if ((u32)p->n * 2 > p->mask) {
        u32 nm = (p->mask + 1) * 2 - 1;
        int *nt = (int *)malloc(sizeof(int) * (nm + 1));
        memset(nt, 0xFF, sizeof(int) * (nm + 1));
        for (int k = 0; k < p->n; k++) {
            u32 a2 = stk_hash(&p->v[k]) & nm;
            while (nt[a2] >= 0) a2 = (a2 + 1) & nm;
            nt[a2] = k;
        }
        free(p->tab); p->tab = nt; p->mask = nm;
    }
    return idx;
}

#include <setjmp.h>
#include <math.h>

#define ctz64 __builtin_ctzll

#define PBL_FMAI 6
#define PBL_FXU 6
#define PBL_FMA64 8

#define PBL_LSU 24
#define PBL_BRU 6
#define PBL_XU 12
#define PBL_XUOP 13
#define PBL_SU 30
#define PBL_TEX 300
#define PBL_ADU 24

#define PB_SB_RAW_DELAY 2

enum { PBC_COUPLED=0, PBC_DECOUPLED=1, PBC_REDIRECTED=2 };

enum { PBVQ_NONE=0, PBVQ_FMA64=1, PBVQ_XU=2, PBVQ_ADU=3, PBVQ_IPA_PASS=4,
       PBVQ_IPA_MUL=5, PBVQ_SHM=6, PBVQ_TEX=7, PBVQ_REDIR=8 };
#define PBVQ_ORDERED_FIRST PBVQ_FMA64
#define PBVQ_ORDERED_LAST  PBVQ_REDIR

#define PBR_FMAI  0x001
#define PBR_FXU   0x002
#define PBR_FMA64 0x004
#define PBR_LSU   0x020
#define PBR_BRU   0x040
#define PBR_XU    0x080
#define PBR_SU    0x100
#define PBR_TEX   0x200
#define PBR_ADU   0x400

#define PB_P(n) (300+(n))
#define PB_CC   320
#define PB_NTOK 321

#define PB_MAX_DEFS 8
#define PB_MAX_USES 16

static int pb_is_tex_batch_op(int op);
static int _pb_texph = 1;
static int _pb_leafxu = 1;
static int _pb_rsb_suses = 1;

static int _pb_lvinreq = 0;
static int _pb_lvin_log = 0;

typedef struct {

    u64 q;
    u32 rel;
    unsigned short op;
    u8  coupled;
    u8  vq;
    u8  is_pred;
    u8  pred_neg;
    u8  pred_reg;
    u8  is_longlat;
    u8  high_cost_sb;
    u8  needs_rsb;
    u8  needs_wsb;
    u8  defs_ccp;
    u8  tex_phase;
    u8  singleton;
    unsigned short res;
    unsigned short latency;
    unsigned short lat_full;
    u8 n_defs, n_uses;
    short defs[PB_MAX_DEFS];
    short uses[PB_MAX_USES];

    u8 n_suses;
    short suses[PB_MAX_USES];
} PBInst;

static int rs_to_arr(const RegSet *s, short *out, int cap) {
    int n = 0;
    for (int w = 0; w < 4; w++) {
        u64 m = s->r[w];
        while (m && n < cap) {
            int b = ctz64(m), r = (w << 6) + b;
            m &= m - 1;
            if (r < 255) out[n++] = (short)r;
        }
    }
    for (int p = 0; p < 7; p++)
        if (((s->p >> p) & 1) && n < cap) out[n++] = (short)PB_P(p);
    return n;
}

static int pb_is_true_source(u64 q, int reg_num) {
    int offs[8], nf = gpr_fields(q, offs);
    for (int i = 1; i < nf; i++)
        if (((q >> offs[i]) & 0xFF) == (unsigned)reg_num) return 1;
    return 0;
}

static int pb_depbar_sb(u64 q) { return (int)((q >> 26) & 7); }
static int pb_depbar_thr(u64 q) { return (int)((q >> 20) & 0x3F); }
static int pb_depbar_le(u64 q)  { return (int)((q >> 29) & 1); }
static int pb_depbar_req(u64 q) { return (int)(q & 0x3F); }

static int _pb_ppoa = 1;
static int _pb_odord = 1;
static int _pb_prohreuse = 1;

static int _pb_dbreal_hits = 0;

#define INKV_DBREQ_MAX 64
typedef struct { int pos; u8 sb, cnt; } InkDbReq;
static InkDbReq _inkv_dbreq[INKV_DBREQ_MAX];
static int _inkv_dbreq_n;
static int _inkv_dbreq_over;
static int _inkv_dbrec_arm;
static int _inkv_dbrec_lo = -1;
static int _inkv_dbrec_hi = -2;
static int _pb_ppoaopex = 0;

static int pb_is_ppoa_depbar(int op, u64 q) {
    if (!_pb_ppoa || op != OP_Depbar) return 0;
    return !pb_depbar_le(q) && pb_depbar_thr(q) == 0 && pb_depbar_sb(q) == 0 &&
           pb_depbar_req(q) != 0;
}

static int pb_has_alu_srcb(int nm) {
    switch (nm) {
    case OP_Fadd: case OP_Fmul: case OP_Ffma:
    case OP_Dadd: case OP_Dmul: case OP_Dfma:
    case OP_Iadd: case OP_Iadd3: case OP_Imad: case OP_Imul: case OP_Imadsp:
    case OP_Iscadd: case OP_Xmad: case OP_Lea: case OP_LeaHi:
    case OP_Fmnmx: case OP_Fset: case OP_Fsetp: case OP_Fchk: case OP_Fswzadd:
    case OP_Imnmx: case OP_Iset: case OP_Isetp: case OP_Icmp: case OP_Fcmp:
    case OP_Dset: case OP_Dsetp: case OP_Dmnmx:
    case OP_Lop: case OP_Lop3:
    case OP_Shl: case OP_Shr: case OP_Shf: case OP_Bfe: case OP_Bfi: case OP_Prmt:
    case OP_F2f: case OP_F2i: case OP_I2f: case OP_I2i:
    case OP_Popc: case OP_Flo:
    case OP_Mov: case OP_Sel:
    case OP_Rro:
    case OP_Hfma2: case OP_Hmul2: case OP_Hadd2: case OP_Hset2: case OP_Hsetp2:
    case OP_Vadd: case OP_Vmad:
        return 1;
    default: return 0;
    }
}
static int pb_has_cbuf(u64 q) {
    if (!pb_has_alu_srcb(op_of(q))) return 0;
    return srcb_form(q) == FORM_CBUF;
}

static unsigned _pb_cls_mask = 0x1F;

static int _pb_ldcbank = 2;

static int _pb_tav_mode = 1 | 2 | 16 | 32 | 256;
static int _pb_tav_dbg = -1;

static int _pb_dbwin = 10;

static int _pb_phaseA = 0;

static void pb_classify(PBInst *ip) {
    int nm = ip->op;
    ip->coupled = PBC_COUPLED;
    ip->vq = PBVQ_NONE;
    ip->latency = 0;
    ip->res = 0;
    ip->is_longlat = 0;
    ip->high_cost_sb = 0;
    ip->needs_rsb = 0;
    ip->needs_wsb = 0;
    ip->singleton = 0;

    #define PB_COUPLED()       do { ip->coupled = PBC_COUPLED; } while(0)
    #define PB_DEC_NOSB()      do { ip->coupled = PBC_DECOUPLED; } while(0)
    #define PB_DEC_RO()        do { ip->coupled = PBC_DECOUPLED; ip->needs_rsb=1; } while(0)
    #define PB_DEC_RW()        do { ip->coupled = PBC_DECOUPLED; ip->needs_rsb=1; ip->needs_wsb=1; } while(0)
    #define PB_REDIR_RW()      do { ip->coupled = PBC_REDIRECTED; ip->needs_rsb=1; ip->needs_wsb=1; } while(0)

    int is64 = ((ip->q >> 51) & 1);

    if (nm == OP_Mufu) {
        ip->res |= PBR_XU; PB_DEC_RW(); ip->vq = PBVQ_XU; ip->latency = (_pb_cls_mask&1)?PBL_XUOP:PBL_XU;
    } else if (nm == OP_Ipa) {

        ip->res |= PBR_SU; PB_DEC_RW();
        ip->vq = (_pb_cls_mask&2) ? PBVQ_NONE
               : (((ip->q >> 54) & 3) == 0 ? PBVQ_IPA_PASS : PBVQ_IPA_MUL);
    } else if (nm == OP_F2f || nm == OP_F2i || nm == OP_I2f || nm == OP_I2i) {

        ip->res |= PBR_XU; PB_DEC_RW(); ip->vq = PBVQ_XU; ip->latency = (_pb_cls_mask&1)?PBL_XUOP:PBL_XU;
    } else if (nm == OP_Tex || nm == OP_Texs || nm == OP_Tld || nm == OP_Tlds ||
               nm == OP_Tld4 || nm == OP_Tld4s || nm == OP_Tmml || nm == OP_Txq ||
               nm == OP_Txd || nm == OP_Txa ||
               nm == OP_TexB || nm == OP_TldB || nm == OP_Tld4B || nm == OP_TxdB ||
               nm == OP_TxqB || nm == OP_TmmlB ||
               nm == OP_TexsF16 || nm == OP_TldsF16 || nm == OP_Tld4sF16) {
        PB_DEC_RW(); ip->vq = PBVQ_TEX; ip->is_longlat = 1; ip->res |= PBR_TEX;
    } else if (nm == OP_Ldc) {

        PB_DEC_RW(); ip->res |= PBR_ADU;
        { int _ldc_bank10 = (int)((ip->q >> 36) & 0x1F) == 10;
          int _ldc_indexed = (int)((ip->q >> 8) & 0xFF) != 255;
          int quad = (_pb_ldcbank == 0) ? 1
                   : (_pb_ldcbank == 1) ? _ldc_bank10
                   : (_pb_ldcbank == 2) ? _ldc_indexed
                   : (_ldc_indexed || _ldc_bank10);
          ip->latency = ((_pb_cls_mask&4) && quad) ? PBL_ADU * 2 : PBL_ADU;
          ip->vq      = (_pb_cls_mask&4) ? PBVQ_NONE   : PBVQ_ADU; }
    } else if (nm == OP_Lds) {
        ip->res |= PBR_LSU; PB_DEC_RW(); ip->vq = PBVQ_SHM; ip->latency = PBL_LSU;
    } else if (nm == OP_Ald) {
        ip->res |= PBR_LSU; PB_DEC_RW(); ip->vq = PBVQ_SHM; ip->latency = PBL_LSU;
    } else if (nm == OP_Ldg || nm == OP_Ldl || nm == OP_Ld) {
        ip->res |= PBR_TEX; PB_DEC_RW(); ip->vq = PBVQ_TEX; ip->is_longlat = 1;
    } else if (nm == OP_Sts || nm == OP_Ast) {
        ip->res |= PBR_LSU; PB_DEC_RO(); ip->vq = PBVQ_SHM;
    } else if (nm == OP_Stg || nm == OP_Stl || nm == OP_St || nm == OP_Red) {
        ip->res |= PBR_TEX; PB_DEC_RO(); ip->vq = PBVQ_TEX;
    } else if (nm == OP_Mov) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_Mov32i) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_S2r) {
        ip->res |= PBR_LSU; PB_DEC_RW();
    } else if (nm == OP_Cs2r) {
        ip->res |= PBR_FXU; ip->latency = PBL_FXU;
    } else if (nm == OP_Shfl) {
        ip->res |= PBR_LSU; PB_DEC_RW(); ip->vq = PBVQ_SHM; ip->latency = PBL_LSU;
    } else if (nm == OP_Atoms || nm == OP_AtomsCas) {
        ip->res |= PBR_LSU; PB_DEC_RW(); ip->vq = PBVQ_SHM; ip->latency = PBL_LSU;
    } else if (nm == OP_Atom || nm == OP_AtomCas) {
        PB_DEC_RW(); ip->res |= PBR_TEX; ip->vq = PBVQ_TEX;
        ip->latency = PBL_TEX; ip->is_longlat = 1;
    } else if (nm == OP_Popc || nm == OP_Flo) {
        ip->res |= PBR_XU; PB_DEC_RW(); ip->vq = PBVQ_XU;
        ip->latency = (_pb_cls_mask&1)?PBL_XUOP:PBL_XU;
    } else if (nm == OP_Bfe || nm == OP_Bfi || nm == OP_Icmp || nm == OP_Fcmp ||
               nm == OP_Prmt || nm == OP_Rro || nm == OP_Shf ||
               nm == OP_Shl || nm == OP_Shr) {
        ip->res |= PBR_FXU;
    } else if (nm == OP_P2r || nm == OP_R2p) {
        ip->res |= PBR_FXU; ip->singleton = 1;
    } else if (nm == OP_Imnmx || nm == OP_Isetp || nm == OP_Iset ||
               nm == OP_Iscadd || nm == OP_Iscadd32i) {

        ip->res |= (_pb_cls_mask&8) ? PBR_FXU : (PBR_FMAI | PBR_FXU);
    } else if (nm == OP_Lea) {

        ip->res |= _pb_leafxu ? PBR_FXU : (PBR_FMAI | PBR_FXU);
    } else if (nm == OP_Lop || nm == OP_Lop3 || nm == OP_Lop32i ||
               nm == OP_Xmad || nm == OP_LeaHi ||
               nm == OP_Iadd || nm == OP_Iadd3 || nm == OP_Iadd32i) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_Nop) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_Depbar) {
        PB_DEC_NOSB();
    } else if (nm == OP_Bra || nm == OP_Brx || nm == OP_Jmp || nm == OP_Jmx ||
               nm == OP_Sync || nm == OP_Brk || nm == OP_Cont || nm == OP_Ret ||
               nm == OP_Exit || nm == OP_Kil || nm == OP_Pret || nm == OP_Pbk ||
               nm == OP_Pcnt || nm == OP_Cal || nm == OP_Jcal || nm == OP_Rtt ||
               nm == OP_Pexit || nm == OP_Bpt || nm == OP_Plongjmp ||
               nm == OP_Ram || nm == OP_Sam || nm == OP_Ssy) {
        ip->res |= PBR_BRU; PB_DEC_NOSB();
    } else if (nm == OP_Fmul || nm == OP_Fmul32i) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_Fadd || nm == OP_Fadd32i) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_Ffma || nm == OP_Ffma32i) {
        ip->res |= PBR_FMAI | PBR_FXU;
    } else if (nm == OP_Fmnmx || nm == OP_Fset || nm == OP_Fsetp || nm == OP_Fswzadd) {
        ip->res |= PBR_FXU;
    } else if (nm == OP_Fchk) {
        ip->res |= PBR_FXU;
    } else if (nm == OP_Dadd || nm == OP_Dmul || nm == OP_Dfma ||
               nm == OP_Dset || nm == OP_Dsetp || nm == OP_Dmnmx) {
        ip->latency = PBL_FMA64; ip->vq = PBVQ_FMA64; PB_DEC_RW();
    } else if (nm == OP_Imad || nm == OP_Imadsp || nm == OP_Imul ||
               nm == OP_Imul32i || nm == OP_Imad32i) {
        ip->latency = PBL_FMA64; ip->vq = PBVQ_FMA64; PB_DEC_RW();
    } else if (nm == OP_Pixld) {
        PB_DEC_RW();
    } else if (nm == OP_Bar) {
        ip->res |= PBR_LSU; PB_DEC_RO(); ip->vq = PBVQ_SHM;
    } else if (nm == OP_Membar) {
        ip->res |= PBR_LSU; PB_DEC_RO();
    } else if (nm == OP_Sel) {
        ip->res |= PBR_FXU;
    } else if (nm == OP_Vote || nm == OP_Votevtg) {
        ip->res |= PBR_FXU;
    } else if (nm == OP_Al2p || nm == OP_Isberd || nm == OP_B2r ||
               nm == OP_Cctl || nm == OP_Cctll || nm == OP_Cctlt) {
        PB_DEC_RW();
    } else if (nm == OP_Out) {
        PB_DEC_RW();
    } else if (nm == OP_Pset || nm == OP_Psetp || nm == OP_Cset || nm == OP_Csetp) {
        ip->res |= PBR_FXU;
    } else if (nm == OP_Suld || nm == OP_SuldB || nm == OP_SuldD || nm == OP_SuldDB) {
        PB_DEC_RW(); ip->vq = PBVQ_TEX; ip->is_longlat = 1; ip->res |= PBR_TEX;
    } else if (nm == OP_Sust || nm == OP_SustB || nm == OP_SustD || nm == OP_SustDB) {
        PB_DEC_RO(); ip->vq = PBVQ_TEX; ip->res |= PBR_TEX;
    } else if (nm == OP_Sured || nm == OP_SuredB) {
        PB_DEC_RW(); ip->vq = PBVQ_TEX; ip->is_longlat = 1; ip->res |= PBR_TEX;
    } else if (nm == OP_Suatom || nm == OP_SuatomB || nm == OP_SuatomB2 ||
               nm == OP_SuatomCas || nm == OP_SuatomCasB) {
        PB_DEC_RW(); ip->vq = PBVQ_TEX; ip->is_longlat = 1; ip->res |= PBR_TEX;
    } else {
        ip->res |= PBR_FXU;
    }
    if (ip->is_longlat) ip->high_cost_sb = 1;
    if (ip->coupled != PBC_DECOUPLED && ip->coupled != PBC_REDIRECTED)
        ip->coupled = PBC_COUPLED;

    #undef PB_COUPLED
    #undef PB_DEC_NOSB
    #undef PB_DEC_RO
    #undef PB_DEC_RW
    #undef PB_REDIR_RW
}

static int pb_base_latency(const PBInst *ip) {
    if (ip->is_longlat) return PBL_TEX;
    if (ip->latency) return ip->latency;
    if (ip->res & PBR_XU)    return PBL_XU;
    if (ip->res & PBR_SU)    return PBL_SU;
    if (ip->res & PBR_ADU)   return PBL_ADU;
    if (ip->res & PBR_LSU)   return PBL_LSU;
    if (ip->res & PBR_TEX)   return PBL_TEX;
    if (ip->res & PBR_BRU)   return PBL_BRU;
    if (ip->res & PBR_FMA64) return PBL_FMA64;
    if (ip->res & (PBR_FMAI | PBR_FXU)) return PBL_FMAI;
    return PBL_FMAI;
}

static void pb_decode_inst(u64 q, u32 rel, PBInst *ip) {
    memset(ip, 0, sizeof(*ip));
    ip->rel = rel;
    ip->q = q;
    ip->op = (unsigned short)op_of(q);

    { int pr = _pred(q), pn = _pinv(q);
      ip->pred_reg = (u8)pr;
      ip->pred_neg = (u8)pn;
      ip->is_pred = (pr != 7); }
    ip->tex_phase = 0;

    { RegSet g, d, u;
      RegSet g2, d2, u2;
      u64 qu;
      parse_du(q, &g, &d, &u);

      qu = (q & ~(0xFULL << 16)) | (0x7ULL << 16);
      if (qu == q) { g2 = g; d2 = d; u2 = u; }
      else parse_du(qu, &g2, &d2, &u2);
      if (ip->is_pred && d.r[0] == 0 && d.r[1] == 0 && d.r[2] == 0 &&
          d.r[3] == 0 && d.p == 0) {

          ip->n_defs = (u8)rs_to_arr(&d2, ip->defs, PB_MAX_DEFS);
      } else {
          ip->n_defs = (u8)rs_to_arr(&d, ip->defs, PB_MAX_DEFS);
      }
      ip->n_uses = (u8)rs_to_arr(&u, ip->uses, PB_MAX_USES);
      { RegSet su; rs_copy(&su, &u2); rs_or(&su, &g);
        ip->n_suses = (u8)rs_to_arr(&su, ip->suses, PB_MAX_USES); } }

    ip->defs_ccp = 0;
    for (int k = 0; k < ip->n_defs; k++)
        if ((ip->defs[k] >= 300 && ip->defs[k] <= 306) || ip->defs[k] == 320)
            ip->defs_ccp = 1;
    pb_classify(ip);

    if (_pb_cls_mask & 16) switch (ip->op) {
    case OP_Bra: case OP_Brx: case OP_Brk: case OP_Cont:
    case OP_Ssy: case OP_Pbk: case OP_Pcnt: case OP_Pret: case OP_Pexit:
    case OP_Jmp: case OP_Jmx: case OP_Cal: case OP_Jcal: case OP_Ret:
    case OP_Exit: case OP_Plongjmp: case OP_Bpt: case OP_Rtt:
        ip->is_pred = 0; break;
    default: break;
    }
    { int _bl = pb_base_latency(ip);
      ip->lat_full = (unsigned short)(_bl + (ip->defs_ccp ? 7 : 0)); }
}

static PBInst *pb_build(const u8 *bc, u32 constOff, int *nout) {

    int cap = 3 * (int)((constOff - INSTR_START) / 32);
    int n = 0;
    PBInst *arr = (PBInst *)malloc(sizeof(PBInst) * (cap > 0 ? cap : 1));
    u32 off;
    for (off = INSTR_START; off + 32 <= constOff; off += 32) {

        for (int s = 0; s < 3; s++) {
            u32 ioff = off + 8 + s * 8;
            u64 q;
            if (ioff + 8 > constOff) break;
            memcpy(&q, bc + ioff, 8);
            pb_decode_inst(q, ioff - INSTR_START, &arr[n]);
            n++;
        }
    }

    for (int i = 0; i < n; i++) {
        if (!pb_is_tex_batch_op(arr[i].op)) continue;
        arr[i].tex_phase = 2;
        if (i > 0 && pb_is_tex_batch_op(arr[i-1].op)) arr[i-1].tex_phase = 1;
    }
    *nout = n;
    return arr;
}

static int pb_is_branch_addr_op(int op) {
    return op == OP_Bra || op == OP_Jmp || op == OP_Jmx || op == OP_Pbk ||
           op == OP_Pcnt || op == OP_Ssy || op == OP_Cal || op == OP_Jcal ||
           op == OP_Pret || op == OP_Plongjmp || op == OP_Bpt;
}

static int pb_is_bb_ender(int op) {
    return op == OP_Bra || op == OP_Brx || op == OP_Jmp || op == OP_Jmx ||
           op == OP_Sync || op == OP_Brk || op == OP_Cont || op == OP_Ret ||
           op == OP_Exit || op == OP_Cal || op == OP_Jcal ||
           op == OP_Rtt || op == OP_Pexit || op == OP_Bpt ||
           op == OP_Ram || op == OP_Sam;
}

typedef struct { int start, end; } PBBlock;

static int _pb_bbsnap = 1;
static int _pb_padrule = 1;
static int _pb_reqrel  = 0;
static int _pb_reqglob = 1;
static u8 *_pb_reqll_p = NULL, *_pb_reqpred_p = NULL;
static PBBlock *pb_basic_blocks(const PBInst *inst, int n, int *nbb) {

    u8 *is_tgt = (u8 *)calloc(n > 0 ? n : 1, 1);
    for (int i = 0; i < n; i++) {
        if (!pb_is_branch_addr_op(inst[i].op)) continue;

        u32 tgt_raw;
        if (inst[i].op == OP_Bra || inst[i].op == OP_Ssy || inst[i].op == OP_Pbk ||
            inst[i].op == OP_Pcnt || inst[i].op == OP_Cal || inst[i].op == OP_Pret ||
            inst[i].op == OP_Plongjmp) {
            int offs24 = (int)((inst[i].q >> 20) & 0xFFFFFF);
            if (offs24 & 0x800000) offs24 |= ~0xFFFFFF;
            tgt_raw = (u32)((int)inst[i].rel + 8 + offs24);
        } else continue;

        int found = 0;
        for (int j = 0; j < n; j++)
            if (inst[j].rel == tgt_raw) { is_tgt[j] = 1; found = 1; break; }
        if (!found && _pb_bbsnap)
            for (int j = 0; j < n; j++)
                if ((u32)inst[j].rel >= tgt_raw) { is_tgt[j] = 1; break; }
    }

    int cnt = 1;
    for (int i = 1; i < n; i++) {
        if (is_tgt[i]) cnt++;
        else if (i > 0 && pb_is_bb_ender(inst[i-1].op)) cnt++;
    }
    PBBlock *bbs = (PBBlock *)malloc(sizeof(PBBlock) * (cnt + 1));
    int nb = 0;
    u8 *starts = (u8 *)calloc(n > 0 ? n : 1, 1);
    starts[0] = 1;
    for (int i = 1; i < n; i++) {
        if (is_tgt[i]) starts[i] = 1;
        if (i > 0 && pb_is_bb_ender(inst[i-1].op)) starts[i] = 1;
    }
    for (int i = 0; i < n; i++) {
        if (!starts[i]) continue;
        int e = n;
        for (int j = i + 1; j < n; j++) {
            if (starts[j]) { e = j; break; }
        }
        bbs[nb].start = i; bbs[nb].end = e; nb++;
    }
    free(is_tgt); free(starts);
    *nbb = nb;
    return bbs;
}

static int pb_has_lldepbar(const PBInst *inst, int n) {
    for (int i = 0; i < n; i++)
        if (inst[i].high_cost_sb && inst[i].needs_wsb) return 1;
    return 0;
}

typedef struct {
    int *wbar, *rbar; u8 *wait;
} PBSBResult;

static PBSBResult pb_sb_alloc(int n) {
    PBSBResult r;
    r.wbar = (int *)malloc(n * sizeof(int));
    r.rbar = (int *)malloc(n * sizeof(int));
    r.wait = (u8 *)calloc(n, 1);
    for (int i = 0; i < n; i++) { r.wbar[i] = -1; r.rbar[i] = -1; }
    return r;
}
static void pb_sb_free(PBSBResult *r) {
    free(r->wbar); free(r->rbar); free(r->wait);
    r->wbar = r->rbar = NULL; r->wait = NULL;
}

static unsigned _pb_sb_knobs = 0xFFFFFFFFu & ~0x100u;

static int _pb_sbexit = 3 | 4;

static int _pb_retc = 0;
static void pb_assign_adv(const PBInst *insts, int n, const PBBlock *bbs, int nbb,
                          int has_ll, PBSBResult *out);

static void pb_assign_all(const PBInst *insts, int n, const PBBlock *bbs, int nbb,
                          int has_ll, PBSBResult *out) {
    pb_assign_adv(insts, n, bbs, nbb, has_ll, out);
}

static int _pb_uniref = 1 | 2;

static int pb_srcc_is_cbuf(u64 q) {
    switch (op_of(q)) {
    case OP_Bfi: case OP_Dfma: case OP_Fcmp: case OP_Ffma:
    case OP_Icmp: case OP_Imad: case OP_Imadsp: case OP_Prmt: case OP_Xmad:
        break;
    default: return 0;
    }
    return (int)((q >> 59) & 0x1F) == 0x0A;
}
static int pb_has_uniform_ref(u64 q) {
    if (pb_has_cbuf(q)) return 1;
    if ((_pb_uniref & 1) && op_of(q) == OP_Ldc) return 1;
    if ((_pb_uniref & 2) && pb_srcc_is_cbuf(q)) return 1;
    return 0;
}

static int pb_can_pair(const PBInst *a, const PBInst *b) {
    if (a->coupled == PBC_DECOUPLED || a->singleton) return 0;
    if (b->coupled != PBC_DECOUPLED || b->singleton) return 0;
    if (pb_has_uniform_ref(a->q) && (pb_has_uniform_ref(b->q) || b->high_cost_sb)) return 0;

    int predToo = (_pb_tav_mode & 512) == 0;
    for (int i = 0; i < a->n_defs; i++) {
        int r = a->defs[i];
        if (r == 255 || r < 0) continue;
        if (r > 255 && !predToo) continue;
        for (int j = 0; j < b->n_uses; j++)
            if (b->uses[j] == r) return 0;
    }
    if (a->coupled == PBC_REDIRECTED) {
        for (int i = 0; i < a->n_uses; i++) {
            int r = a->uses[i]; if (r >= 255) continue;
            for (int j = 0; j < b->n_defs; j++)
                if (b->defs[j] == r) return 0;
        }
        for (int i = 0; i < a->n_defs; i++) {
            int r = a->defs[i]; if (r >= 255) continue;
            for (int j = 0; j < b->n_defs; j++)
                if (b->defs[j] == r) return 0;
        }
    }
    return 1;
}

static int _pb_pair_mode = 0;
static void pb_pair_flags(const PBInst *block, int n, const PBSBResult *res, u8 *pair) {
    int sb_pending[6]; memset(sb_pending, 0, sizeof(sb_pending));
    memset(pair, 0, n);
    int i = 0;
    while (i + 1 < n) {
        int do_pair = pb_can_pair(&block[i], &block[i+1]);
        if (_pb_pair_mode == 1) {   }
        else if (_pb_pair_mode == 2) { if (block[i+1].op == OP_Depbar) do_pair = 0; }
        else if (do_pair && block[i+1].op == OP_Depbar) {
            int sb = pb_depbar_sb(block[i+1].q), thr = pb_depbar_thr(block[i+1].q);
            if (sb_pending[sb] > thr) do_pair = 0;
        }
        if (do_pair) {
            pair[i] = 1;
            if (res->wbar[i] >= 0) sb_pending[res->wbar[i]]++;
            if (res->wbar[i+1] >= 0) sb_pending[res->wbar[i+1]]++;
            if (block[i].op == OP_Depbar) {
                int sb = pb_depbar_sb(block[i].q), thr = pb_depbar_thr(block[i].q);
                if (sb_pending[sb] > thr) sb_pending[sb] = thr;
            }
            if (block[i+1].op == OP_Depbar) {
                int sb = pb_depbar_sb(block[i+1].q), thr = pb_depbar_thr(block[i+1].q);
                if (sb_pending[sb] > thr) sb_pending[sb] = thr;
            }
            if (res->wait[i]) for (int s=0;s<6;s++) if ((res->wait[i]>>s)&1) sb_pending[s]=0;
            i += 2;
        } else {
            if (res->wbar[i] >= 0) sb_pending[res->wbar[i]]++;
            if (block[i].op == OP_Depbar) {
                int sb = pb_depbar_sb(block[i].q), thr = pb_depbar_thr(block[i].q);
                if (sb_pending[sb] > thr) sb_pending[sb] = thr;
            }
            if (res->wait[i]) for (int s=0;s<6;s++) if ((res->wait[i]>>s)&1) sb_pending[s]=0;
            i++;
        }
    }
}

static int pb_comp_pred(const PBInst *a, const PBInst *b) {
    return a->is_pred && b->is_pred && a->pred_reg == b->pred_reg && a->pred_neg != b->pred_neg;
}

typedef struct {
    int inst, opc, tav, wtav, wy, nsg, maxccp, dct, wt, mccp, mwt;

    int has_v2;
    int nbod;
    int coupling;
    int vq;
    int lat;
    int res;
    int flags;
    int reqsb;
    int wsb;
    int rsb;
    int texph;
    int reuse;
    int iidx;
} PBGt;

static PBGt *_pb_gt = NULL;
static int   _pb_gt_n = 0;
static int   _pb_gt_base = -1;
static unsigned _pb_gt_inject = 0;

static int *_pb_dbg_tav, *_pb_dbg_dct, *_pb_dbg_mwt, *_pb_dbg_ns;
static int *_pb_dbg_stall, *_pb_dbg_opex, *_pb_dbg_T;

static int *_pb_dbgp_tav, *_pb_dbgp_dct, *_pb_dbgp_mwt, *_pb_dbgp_ns;
static int *_pb_dbgp_stall, *_pb_dbgp_opex, *_pb_dbgp_T;
static int *_pb_dbgp_bb;

static int *_pb_dbg_wtav, *_pb_dbg_opex0, *_pb_dbg_nsg, *_pb_dbg_mccpi;
static int *_pb_dbg_wt,   *_pb_dbg_mccp,  *_pb_dbg_mwt2, *_pb_dbg_nbod;
static int *_pb_dbgp_wtav, *_pb_dbgp_opex0, *_pb_dbgp_nsg, *_pb_dbgp_mccpi;
static int *_pb_dbgp_wt,   *_pb_dbgp_mccp,  *_pb_dbgp_mwt2, *_pb_dbgp_nbod;
static u8  *_pb_dbg_reqll,  *_pb_dbg_reqpred;
static u8  *_pb_dbgp_reqll, *_pb_dbgp_reqpred;

static const PBGt *pb_gt_at(int k) {
    if (_pb_gt_base < 0 || !_pb_gt) return NULL;
    int gi = _pb_gt_base + k;
    if (gi < 0 || gi >= _pb_gt_n) return NULL;
    return &_pb_gt[gi];
}

typedef struct { int inst, opc, tav, reqsb, wsb, rsb, iord, bbi; } PBSbd;
static PBSbd *_pb_sbd = NULL;
static int    _pb_sbd_n = 0;
static int    _pb_sbd_use = 0;

static int _pb_dep_debug_gi = -1;
static int pb_dep_ready(const PBInst *block, int i, const int *T,
                        const int *lw, const int *lw_prior, int late, int vq) {
    int t = 0;
    const PBInst *ip = &block[i];
    int pred_defs[PB_MAX_DEFS], npd = 0;
    if (ip->is_pred) {
        for (int k = 0; k < ip->n_defs; k++)
            if (ip->defs[k] < 255) pred_defs[npd++] = ip->defs[k];
    }
    for (int grp = 0; grp < 2; grp++) {
        const short *arr = grp == 0 ? ip->uses : ip->defs;
        int cnt = grp == 0 ? ip->n_uses : ip->n_defs;
        int is_output = (grp == 1);
        for (int k = 0; k < cnt; k++) {
            int r = arr[k];
            int p = lw[r]; if (p < 0) continue;
            const PBInst *pp = &block[p];
            if (pp->coupled == PBC_DECOUPLED) {
                if (_pb_dep_debug_gi >= 0)
                    printf("    dep i=%d grp=%d r=%d p=%d SKIP(dec)\n",
                           _pb_dep_debug_gi, grp, r, p);
                continue;
            }
            if (pb_comp_pred(pp, ip)) {
                int p2 = lw_prior[r]; if (p2 < 0) continue;
                pp = &block[p2]; p = p2;
                if (pp->coupled == PBC_DECOUPLED) continue;
            }
            int lat;
            if (is_output) {
                lat = late ? 0 : 1;
            } else {
                int is_pd = 0;
                for (int z = 0; z < npd; z++) if (pred_defs[z] == r) { is_pd = 1; break; }
                if (is_pd && !pb_is_true_source(ip->q, r)) {
                    lat = late ? 0 : 1;
                } else {
                    int pwp = pp->defs_ccp;
                    if (pwp) lat = 13;
                    else if (pp->latency && pp->coupled == PBC_COUPLED &&
                             !(pp->res & (PBR_FMAI | PBR_FXU))) lat = pp->latency;
                    else if (late) {
                        if (pp->coupled == PBC_REDIRECTED)
                            lat = (vq == PBVQ_TEX || vq == PBVQ_XU) ? 4 : 6;
                        else
                            lat = (vq == PBVQ_TEX || vq == PBVQ_XU) ? 2 : 4;
                    } else lat = 6;
                }
            }
            if (_pb_dep_debug_gi >= 0)
                printf("    dep i=%d grp=%d r=%d p=%d T[p]=%d lat=%d -> %d\n",
                       _pb_dep_debug_gi, grp, r, p, T[p], lat, T[p]+lat);
            if (T[p] + lat > t) t = T[p] + lat;
        }
    }
    if (_pb_dep_debug_gi >= 0)
        printf("  dep_ready(%d) = %d (late=%d vq=%d)\n", _pb_dep_debug_gi, t, late, vq);
    return t;
}

static void pb_forward_times(const PBInst *block, int n, const PBSBResult *res,
                             u8 *pair, int *T, int *offdeck) {
    int *lw = (int *)malloc(PB_NTOK * sizeof(int));
    int *lw_prior = (int *)malloc(PB_NTOK * sizeof(int));
    for (int k = 0; k < PB_NTOK; k++) { lw[k] = -1; lw_prior[k] = -1; }
    int setter[6]; int setter_dec[6];
    memset(setter, 0xFF, sizeof(setter)); memset(setter_dec, 0, sizeof(setter_dec));
    memset(T, 0, n * sizeof(int)); memset(offdeck, 0, n * sizeof(int));
    int clock = 0;

    #define COMMIT(idx) do { \
        const PBInst *_ip = &block[idx]; \
        for (int _k=0; _k<_ip->n_defs; _k++) { \
            int _r = _ip->defs[_k]; \
            if (_ip->is_pred) lw_prior[_r] = lw[_r]; \
            lw[_r] = idx; \
        } \
        for (int _k=0; _k<_ip->n_uses; _k++) { \
            int _r = _ip->uses[_k]; \
            if (_ip->is_pred) lw_prior[_r] = lw[_r]; \
            lw[_r] = lw[_r];   \
        } \
        int _dec = (_ip->coupled == PBC_DECOUPLED); \
        if (res->wbar[idx] >= 0) { setter[res->wbar[idx]] = idx; setter_dec[res->wbar[idx]] = _dec; } \
        if (res->rbar[idx] >= 0) { setter[res->rbar[idx]] = idx; setter_dec[res->rbar[idx]] = _dec; } \
        for (int _s=0; _s<6; _s++) if ((res->wait[idx]>>_s)&1) setter[_s]=-1; \
    } while(0)

    int i = 0;
    while (i < n) {
        int late0 = block[i].coupled == PBC_DECOUPLED || res->rbar[i] >= 0;
        int t = clock;
        { int dr = pb_dep_ready(block, i, T, lw, lw_prior, late0, block[i].vq);
          if (dr > t) t = dr; }
        int od = 0;
        for (int s = 0; s < 6; s++) {
            if (!((res->wait[i] >> s) & 1) || setter[s] < 0) continue;
            if (T[setter[s]] + PB_SB_RAW_DELAY > t) t = T[setter[s]] + PB_SB_RAW_DELAY;
            if (setter[s] == i - 1 && setter_dec[s] && !block[i].is_pred)
                if (6 > od) od = 6;
        }
        if (od && i > 0) { if (od > offdeck[i-1]) offdeck[i-1] = od; }
        T[i] = t;
        if (pair[i] && i + 1 < n) {
            COMMIT(i);
            int j = i + 1;
            int late1 = block[j].coupled == PBC_DECOUPLED || res->rbar[j] >= 0;
            int dep2 = pb_dep_ready(block, j, T, lw, lw_prior, late1, block[j].vq);
            if (dep2 > T[i] + 8) {
                pair[i] = 0;
                int t2 = clock; if (dep2 > t2) t2 = dep2;
                int od2 = 0;
                for (int s=0;s<6;s++) {
                    if (!((res->wait[j]>>s)&1)||setter[s]<0) continue;
                    if (T[setter[s]]+PB_SB_RAW_DELAY>t2) t2=T[setter[s]]+PB_SB_RAW_DELAY;
                    if (setter[s]==i && setter_dec[s] && !block[j].is_pred) if(6>od2)od2=6;
                }
                if (od2) { if(od2>offdeck[i]) offdeck[i]=od2; }
                T[j] = t2;
                COMMIT(j); clock = T[j]+1; i+=2;
            } else {
                int pair_t = t; if (dep2 > pair_t) pair_t = dep2;
                int _t2 = pair_t; int od2 = 0;
                for (int s=0;s<6;s++) {
                    if (!((res->wait[j]>>s)&1)||setter[s]<0) continue;
                    if (T[setter[s]]+PB_SB_RAW_DELAY>_t2) _t2=T[setter[s]]+PB_SB_RAW_DELAY;
                    if (setter[s]==i && setter_dec[s] && !block[j].is_pred) if(6>od2)od2=6;
                }
                if (od2) { if(od2>offdeck[i]) offdeck[i]=od2; }
                if (_t2 > pair_t) pair_t = _t2;
                T[i] = pair_t; T[j] = pair_t;
                COMMIT(j); clock = T[j]+1; i+=2;
            }
        } else {
            COMMIT(i); clock = T[i]+1; i++;
        }
    }
    #undef COMMIT
    free(lw); free(lw_prior);
}

static int pb_is_tex_batch_op(int op);
static int pb_min_issue(int op);
static int pb_is_flowctrl(int op);
#define PB_SHORT_STALL_T 7

#define PBD_FLOW   0
#define PBD_OUTPUT 1
#define PBD_ANTI   2

typedef struct { int to; unsigned char type; } PBDep;

#define PBD_INL 6
typedef struct { PBDep *d; int n, cap; PBDep inl[PBD_INL]; } PBDepList;

static void pbd_reset(PBDepList *l) { l->d = l->inl; l->n = 0; l->cap = PBD_INL; }
static void pbd_free(PBDepList *l) { if (l->d != l->inl) free(l->d); l->d = NULL; }

static void pbd_add(PBDepList *l, int to, int type) {
    for (int k = 0; k < l->n; k++)
        if (l->d[k].to == to && l->d[k].type == type) return;
    if (l->n >= l->cap) {
        int nc = l->cap * 2;
        if (l->d == l->inl) {
            PBDep *nd = (PBDep *)malloc(sizeof(PBDep) * (size_t)nc);
            if (!nd) return;
            memcpy(nd, l->inl, sizeof(PBDep) * (size_t)l->n);
            l->d = nd;
        } else {
            l->d = (PBDep *)grow_arr(l->d, sizeof(PBDep), l->cap, nc);
        }
        l->cap = nc;
    }
    l->d[l->n].to = to; l->d[l->n].type = (unsigned char)type; l->n++;
}

#define PB_MAX_RES  13
#define PB_MAX_DISP 3
#define PB_MODELED_RES (PBR_FMAI | PBR_FXU | PBR_LSU | PBR_FMA64)
static const int pb_res_busy[PB_MAX_RES] = {
     2,  2,  128, 0, 0,  4, 0, 0, 0, 0, 0, 0, 0
};
static const int pb_res_disp[PB_MAX_RES] = {
    0,0,1,0,0,1,0,0,0,0,0,0,0
};

static int pb_same_ordered_vq(const PBInst *a, const PBInst *b) {
    if (!a || !b) return 0;
    return a->vq == b->vq && a->vq >= PBVQ_ORDERED_FIRST && a->vq <= PBVQ_ORDERED_LAST;
}

static int pb_lat_flow(const PBInst *f, const PBInst *t) {
    if (pb_is_tex_batch_op(f->op)) return PBL_TEX;
    if (f->is_longlat) return PBL_TEX;
    int lat = f->lat_full ? f->lat_full : pb_base_latency(f);
    if (t != NULL && f->coupled != PBC_DECOUPLED && !f->defs_ccp) {
        if (t->coupled == PBC_DECOUPLED) {
            int texu = (t->vq == PBVQ_TEX || t->vq == PBVQ_XU);
            if (f->coupled == PBC_COUPLED) lat = texu ? 2 : 4;
            else                           lat = texu ? 4 : 6;
        }
    }
    return lat;
}

static int pb_read_sb_latency(const PBInst *f) {
    if (f->coupled == PBC_REDIRECTED) return PB_SB_RAW_DELAY;

    int nrr = 0;
    if (_pb_rsb_suses) {
        for (int k = 0; k < f->n_suses; k++) if (f->suses[k] >= 0 && f->suses[k] < 255) nrr++;
    } else {
        for (int k = 0; k < f->n_uses; k++) if (f->uses[k] >= 0 && f->uses[k] < 255) nrr++;
    }
    if (nrr < 1) nrr = 1;
    int lat = 8 + (nrr - 1) * 2;
    if (f->vq == PBVQ_TEX || f->op == OP_Ld || f->op == OP_St) lat += 3;
    if (f->needs_wsb) { int l2 = pb_lat_flow(f, NULL); if (l2 < lat) lat = l2; }
    return lat;
}
static int pb_write_sb_latency(const PBInst *f) {
    if (f->coupled == PBC_REDIRECTED) return PB_SB_RAW_DELAY;
    return pb_lat_flow(f, NULL);
}

static int pb_has_sb_reg_antidep(const PBInst *f, const PBInst *t) {
    for (int i = 0; i < f->n_uses; i++) {
        int r = f->uses[i]; if (r < 0 || r >= 255) continue;
        for (int j = 0; j < t->n_defs; j++)
            if (t->defs[j] == r) return 1;
    }
    return 0;
}

static int pb_lat_output(const PBInst *f, const PBInst *t) {
    if (f->coupled == PBC_DECOUPLED) {
        if (pb_same_ordered_vq(f, t)) return 1;
        return pb_lat_flow(f, t);
    }
    if (f->coupled == PBC_COUPLED) {
        if (t && t->coupled == PBC_DECOUPLED) return 0;
        return 1;
    }

    if (t) {
        if (t->coupled == PBC_DECOUPLED) return 0;
        if (t->coupled == PBC_REDIRECTED) return 1;
    }
    return 3;
}

static int pb_lat_anti(const PBInst *f, const PBInst *t) {
    if (!pb_has_sb_reg_antidep(f, t)) return 0;
    if (pb_same_ordered_vq(f, t)) return 0;
    if (f->coupled == PBC_COUPLED) return 0;
    return pb_read_sb_latency(f);
}

static int pb_dep_latency(const PBInst *f, const PBInst *t, int type) {
    if (type == PBD_FLOW)   return pb_lat_flow(f, t);
    if (type == PBD_OUTPUT) return pb_lat_output(f, t);
    return pb_lat_anti(f, t);
}

static int _pb_anti_pclass = 0;

static int _pb_drop_guard = 0;
static int pb_real_uses(const PBInst *ip, short *out) {
    int m = 0;

    int gp = (_pb_drop_guard && ip->pred_reg != 7) ? PB_P(ip->pred_reg) : -1;
    if (_pb_tav_mode & 64) {
        for (int k = 0; k < ip->n_suses; k++)
            if (ip->suses[k] != gp) out[m++] = ip->suses[k];
        return m;
    }
    for (int k = 0; k < ip->n_uses; k++) {
        int r = ip->uses[k];
        if (ip->is_pred && r < 255) {
            int isdef = 0;
            for (int j = 0; j < ip->n_defs; j++) if (ip->defs[j] == r) { isdef = 1; break; }
            if (isdef && !pb_is_true_source(ip->q, r)) continue;
        }
        if (r == gp) continue;
        out[m++] = (short)r;
    }
    return m;
}

typedef struct { int ip, lastDefP, prevDefP, lastDefNotP, prevDefNotP; } PBRegState;

static int _pb_cpd = 1;

static int *_pb_dbcons = NULL;
static int  _pb_blk_base = 0;

#define PBDBG_BASE ((_pb_gt_base >= 0) ? _pb_gt_base : _pb_blk_base)
static int  _pb_dbc_use = 1;
static int  _pb_dbc_ppoa = 1;
static int  _pb_ppoareq = 1;
static int  _pb_dbc_mismatch = 0;
static int  _pb_reuselat = 1;

static int pbc_cmp_pred(const PBInst *b, int a, int c) {
    if (a < 0 || c < 0) return 0;
    if (b[a].is_pred != b[c].is_pred) return 0;
    if (!b[a].is_pred) return 0;
    return b[a].pred_reg == b[c].pred_reg;
}
static int pbc_compl_pred(const PBInst *b, int a, int c) {
    return pbc_cmp_pred(b, a, c) && b[a].pred_neg != b[c].pred_neg;
}
static int pbc_ident_pred(const PBInst *b, int a, int c) {
    return pbc_cmp_pred(b, a, c) && b[a].pred_neg == b[c].pred_neg;
}
static int pbc_defines(const PBInst *b, int i, int reg) {
    if (i < 0) return 0;
    for (int k = 0; k < b[i].n_defs; k++) if (b[i].defs[k] == reg) return 1;
    return 0;
}

static int pbc_are_compl(const PBInst *b, int a, int c, int reg) {
    if (a < 0 || c < 0) return 0;
    if (!pbc_compl_pred(b, a, c)) return 0;
    if (reg >= 300 && reg <= 306 && b[a].pred_reg == reg - 300) {
        if (pbc_defines(b, a, reg) || pbc_defines(b, c, reg)) return 0;
    }
    return 1;
}

static int pbc_most_recent(const int *ord, int a, int c) {
    int ai = (a >= 0) ? ord[a] : 0, ci = (c >= 0) ? ord[c] : 0;
    return (ai > ci) ? a : c;
}

static void pbc_add_dep(PBDepList *dep, int from, int to, int type) {
    if (from < 0) return;
    if (type == PBD_ANTI) pbd_add(&dep[to], from, PBD_ANTI);
    else                  pbd_add(&dep[from], to, type);
}

static int pbc_add_noncompl(const PBInst *b, PBDepList *dep, int i, int i2,
                            int reg, int type) {
    if (!pbc_are_compl(b, i2, i, reg)) { pbc_add_dep(dep, i2, i, type); return 1; }
    return 0;
}

static void pbc_add_compl_deps(const PBInst *b, PBDepList *dep, const PBRegState *st,
                               const int *ord, int i, int reg, int type, u8 *prohibit) {
    if (type == PBD_FLOW && prohibit &&
        (pbc_are_compl(b, i, st->lastDefNotP, reg) ||
         pbc_are_compl(b, st->lastDefP, i, reg)))
        prohibit[i] = 1;
    if (b[i].is_pred) {
        int inst3 = pbc_most_recent(ord, st->lastDefP, st->lastDefNotP);
        int earliest = (inst3 == st->lastDefP) ? st->lastDefNotP : st->lastDefP;
        int latest = pbc_most_recent(ord, st->prevDefP, st->prevDefNotP);
        int inst2 = pbc_most_recent(ord, earliest, latest);
        int inst1 = (inst2 == earliest) ? latest : earliest;
        int c32 = pbc_are_compl(b, inst3, inst2, reg);
        int c21 = pbc_are_compl(b, inst2, inst1, reg);
        int add3 = pbc_add_noncompl(b, dep, i, inst3, reg, type);
        if (!add3 || c32) pbc_add_noncompl(b, dep, i, inst2, reg, type);
        if (!add3 && c21) pbc_add_noncompl(b, dep, i, inst1, reg, type);
    } else {
        int latest = pbc_most_recent(ord, st->lastDefP, st->lastDefNotP);
        int earliest = (latest == st->lastDefP) ? st->lastDefNotP : st->lastDefP;
        pbc_add_dep(dep, latest, i, type);
        if (pbc_are_compl(b, latest, earliest, reg))
            pbc_add_dep(dep, earliest, i, type);
    }
}

static void pbc_update_tables(const PBInst *b, PBRegState *st, int i) {
    if (!b[i].is_pred || !b[i].pred_neg) {
        if (!pbc_ident_pred(b, i, st->lastDefP)) st->prevDefP = st->lastDefP;
        st->lastDefP = i;
    } else {
        if (!pbc_ident_pred(b, i, st->lastDefNotP)) st->prevDefNotP = st->lastDefNotP;
        st->lastDefNotP = i;
    }
    st->ip = i;
}

static void pb_calc_deps_x(const PBInst *block, int n, PBDepList *dep, u8 *prohibit) {
    int *lastdef = (int *)malloc(PB_NTOK * sizeof(int));
    short ru[PB_MAX_USES]; int nru;
    for (int i = 0; i < n; i++) pbd_reset(&dep[i]);

    if (_pb_cpd) {
        PBRegState *tab = (PBRegState *)malloc(PB_NTOK * sizeof(PBRegState));
        int *ord = (int *)malloc((n ? n : 1) * sizeof(int));

        for (int k = 0; k < PB_NTOK; k++)
            tab[k].ip = tab[k].lastDefP = tab[k].prevDefP =
            tab[k].lastDefNotP = tab[k].prevDefNotP = -1;
        for (int i = 0; i < n; i++) ord[i] = i + 1;
        for (int i = 0; i < n; i++) {
            const PBInst *ip = &block[i];
            nru = pb_real_uses(ip, ru);
            for (int k = nru - 1; k >= 0; k--) {
                int r = ru[k]; PBRegState *st = &tab[r];
                if (st->ip >= 0 && st->ip != i) {
                    if (r == PB_CC) pbd_add(&dep[st->ip], i, PBD_FLOW);
                    else pbc_add_compl_deps(block, dep, st, ord, i, r, PBD_FLOW, prohibit);
                }
            }
            for (int k = ip->n_defs - 1; k >= 0; k--) {
                int r = ip->defs[k]; PBRegState *st = &tab[r];
                if (st->ip >= 0 && st->ip != i) {
                    if (r == PB_CC) pbd_add(&dep[st->ip], i, PBD_OUTPUT);
                    else pbc_add_compl_deps(block, dep, st, ord, i, r, PBD_OUTPUT, NULL);
                }
                pbc_update_tables(block, st, i);
            }
        }

        for (int k = 0; k < PB_NTOK; k++)
            tab[k].ip = tab[k].lastDefP = tab[k].prevDefP =
            tab[k].lastDefNotP = tab[k].prevDefNotP = -1;
        for (int i = 0; i < n; i++) ord[i] = n - i;
        for (int i = n - 1; i >= 0; i--) {
            const PBInst *ip = &block[i];
            nru = pb_real_uses(ip, ru);
            for (int k = nru - 1; k >= 0; k--) {
                int r = ru[k];
                if (r >= 255 && !_pb_anti_pclass) continue;
                PBRegState *st = &tab[r];
                if (st->ip >= 0 && st->ip != i) {
                    if (r == PB_CC) pbd_add(&dep[i], st->ip, PBD_ANTI);
                    else pbc_add_compl_deps(block, dep, st, ord, i, r, PBD_ANTI, NULL);
                }
            }
            for (int k = ip->n_defs - 1; k >= 0; k--) {
                int r = ip->defs[k];
                if (r >= 255 && !_pb_anti_pclass) continue;
                pbc_update_tables(block, &tab[r], i);
            }
        }
        free(ord); free(tab); free(lastdef);
        return;
    }

    for (int k = 0; k < PB_NTOK; k++) lastdef[k] = -1;
    for (int i = 0; i < n; i++) {
        const PBInst *ip = &block[i];
        nru = pb_real_uses(ip, ru);
        for (int k = nru - 1; k >= 0; k--) {
            int r = ru[k], p = lastdef[r];
            if (p >= 0 && p != i) pbd_add(&dep[p], i, PBD_FLOW);
        }
        for (int k = ip->n_defs - 1; k >= 0; k--) {
            int r = ip->defs[k], p = lastdef[r];
            if (p >= 0 && p != i) pbd_add(&dep[p], i, PBD_OUTPUT);
            lastdef[r] = i;
        }
    }

    for (int k = 0; k < PB_NTOK; k++) lastdef[k] = -1;
    for (int i = n - 1; i >= 0; i--) {
        const PBInst *ip = &block[i];
        nru = pb_real_uses(ip, ru);
        for (int k = nru - 1; k >= 0; k--) {
            int r = ru[k]; if (r >= 255) continue;
            int p = lastdef[r];
            if (p >= 0 && p != i) pbd_add(&dep[i], p, PBD_ANTI);
        }
        for (int k = ip->n_defs - 1; k >= 0; k--) {
            int r = ip->defs[k]; if (r >= 255) continue;
            lastdef[r] = i;
        }
    }
    free(lastdef);
}

static void pb_calc_deps(const PBInst *block, int n, PBDepList *dep) {
    pb_calc_deps_x(block, n, dep, NULL);
}

static void pb_calc_prohibit_reuse(const PBInst *block, int n, u8 *prohibit) {
    if (n <= 0 || !_pb_cpd) return;
    PBRegState *tab = (PBRegState *)malloc(PB_NTOK * sizeof(PBRegState));
    short ru[PB_MAX_USES];
    if (!tab) return;
    for (int k = 0; k < PB_NTOK; k++)
        tab[k].ip = tab[k].lastDefP = tab[k].prevDefP =
        tab[k].lastDefNotP = tab[k].prevDefNotP = -1;
    for (int i = 0; i < n; i++) {
        const PBInst *ip = &block[i];
        int nru = pb_real_uses(ip, ru);
        for (int k = nru - 1; k >= 0; k--) {
            int r = ru[k];
            if (r == PB_CC) continue;
            PBRegState *st = &tab[r];
            if (st->ip < 0 || st->ip == i) continue;
            if (pbc_are_compl(block, i, st->lastDefNotP, r) ||
                pbc_are_compl(block, st->lastDefP, i, r))
                prohibit[i] = 1;
        }
        for (int k = ip->n_defs - 1; k >= 0; k--)
            pbc_update_tables(block, &tab[ip->defs[k]], i);
    }
    free(tab);
}

typedef struct {
    int time;
    int resTimeFree[PB_MAX_RES];
    int dispTimeFree[PB_MAX_DISP];
    int numInBundle;
    int ipInBundle;
    int sb[6];
    int nextTexTime;
    int lastTexTime;

    int waitTime;
    int maxWaitTime;
    int maxCcOrPTime;
    int numInstsSinceLastGroup;
    int cumuWaitSinceEndGroup;
    int numBundlesSinceOffDeck;
    int priorNumBundlesSinceOffDeck;
    int ipPriorSched;
    int ipPriorOffDeck;
    int ipPriorTex;
    int sbTimeSet[6];
} PBMach;

static int pb_ready_time(PBMach *m, const PBInst *ip, int tav_i, int excl_res, int *pRes) {
    int readyTime = tav_i;
    if (!pb_is_tex_batch_op(ip->op)) {
        if (m->lastTexTime > readyTime) readyTime = m->lastTexTime;
    }
    if (readyTime < m->time) readyTime = m->time;
    int res = ip->res;
    if ((res & PB_MODELED_RES) == 0) return readyTime;
    int best = -1, bestTime = 99999;
    int exclDisp = -1;
    if (excl_res >= 0) {
        res &= ~(1 << excl_res);
        if (res == 0) return 99999;
        exclDisp = pb_res_disp[excl_res];
    }
    int rr = res;
    for (int ii = 0; ii < PB_MAX_RES; ii++) {
        if (rr & 1) {
            int du = pb_res_disp[ii];
            if (du != exclDisp) {
                int rt = m->resTimeFree[ii];
                if (m->dispTimeFree[du] > rt) rt = m->dispTimeFree[du];
                if (rt <= readyTime) { best = ii; bestTime = readyTime; break; }
                if (rt < bestTime)   { best = ii; bestTime = rt; }
            }
        }
        rr >>= 1;
        if (rr == 0) break;
    }
    if (best < 0) return 99999;
    if (pRes) *pRes = best;
    return bestTime;
}

static void pb_update_res(PBMach *m, const PBInst *ip, int resToUse) {
    if (pb_is_tex_batch_op(ip->op)) {
        if (m->time < m->nextTexTime) m->time = m->nextTexTime;
        m->nextTexTime = m->time + 1;
        m->lastTexTime = m->time;
    }
    if ((ip->res & PB_MODELED_RES) != 0 && resToUse >= 0) {
        m->resTimeFree[resToUse] = m->time + pb_res_busy[resToUse];
        m->dispTimeFree[pb_res_disp[resToUse]] = m->time + 1;
    }
}

static void pb_update_tav_from_sb(PBMach *m, const PBInst *ip, int req, int wbar, int rbar,
                                  int *tav_i, int *wtav_i) {
    int myTime = *tav_i;
    if (req) {
        for (int ii = 0; ii < 6; ii++) {
            if (!((req >> ii) & 1)) continue;
            if (m->sb[ii] > myTime) myTime = m->sb[ii];
            if (m->sb[ii] > -1) {

                if (wtav_i) {
                    int sbT = m->sbTimeSet[ii] + PB_SB_RAW_DELAY;
                    if (sbT > *wtav_i) *wtav_i = sbT;
                }
                m->sb[ii] = -1;
            }
        }
    }
    *tav_i = myTime;
    if (rbar >= 0) {
        int t = pb_read_sb_latency(ip) + myTime;
        if (t > m->sb[rbar]) m->sb[rbar] = t;
    }
    if (wbar >= 0) {
        int t = pb_write_sb_latency(ip) + myTime;
        if (t > m->sb[wbar]) m->sb[wbar] = t;
    }
}

static const int pb_opexWait[32] = {
   15, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15,
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9,10,11,15, 6, 8,15
};
#define PBO_DRAIN   0
#define PBO_PAIR    16
#define PBO_PIXBAR  28
#define PBO_ODY6    29
#define PBO_ODY8    30
#define PBO_OD      31
#define PB_MAXINST_BETWEEN_GROUPS 5

static int pbo_is_group(int w)  { return w >= 1 && w <= 15; }
static int pbo_is_odly(int w)   { return w == 0 || (w >= 28 && w <= 31); }

static int _pb_opex_mode = 5;

typedef struct {
    const PBInst *b;
    int n;
    const PBSBResult *res;
    PBDepList *dep;
    PBMach *M;
    int *tav, *dct, *wtav;
    int *mccp_i;
    int *nsg_i, *cwseg_i;
    int *opex;
    u8  *req_ll, *req_pred;

    int *snap_wt, *snap_mwt, *snap_mccp, *snap_nbod, *snap_nsg;
    int *snap_wtav, *snap_mccpi, *snap_opex;
} PBOpexCtx;

static void pbo_update_wait_info(PBOpexCtx *C, int prior, int i, int waitLatency);
static int  pbo_calc_wait_yield(PBOpexCtx *C, int i);

static int pbo_ccorp_lat(const PBInst *ip) {
    int l = pb_base_latency(ip); if (!l) l = 6;
    l += 7; if (l > 15) l = 15;
    return l;
}

static int pbo_special_opex(const PBInst *ip, int *minWait, int *isNop) {
    (void)minWait;
    int guarded = (ip->pred_reg != 7);
    switch (ip->op) {
    case OP_Ret: case OP_Exit:
        if (!guarded) return PBO_OD;
        break;
    case OP_Bar:
        if (!guarded) return PBO_OD;
        break;
    case OP_Membar:
        if (!guarded) return PBO_OD;
        break;
    default: break;
    }
    (void)isNop;
    return -1;
}

static int pbo_use_group(PBOpexCtx *C, int i, int wait) {
    if (wait > 11) return 1;
    if (C->b[i].coupled == PBC_DECOUPLED) return 0;

    if (C->nsg_i[i] >= PB_MAXINST_BETWEEN_GROUPS) return 1;
    return 0;
}

static int pbo_wait_or_pair(PBOpexCtx *C, int i, int wait) {
    if (wait == 0) return PBO_PAIR;
    if (!pbo_use_group(C, i, wait)) return PBO_PAIR + wait;
    if (wait < 15) return PBO_DRAIN + wait;
    return 15;
}

static void pbo_set_offdeck_state(PBMach *M, int i) {
    M->priorNumBundlesSinceOffDeck = M->numBundlesSinceOffDeck;
    M->ipPriorOffDeck = i;
    M->numBundlesSinceOffDeck = 0;
}

static int pbo_calc_opex(PBOpexCtx *C, int i) {
    PBMach *M = C->M;
    const PBInst *ip = &C->b[i];
    int curThr = PB_SHORT_STALL_T;
    int minWait = pb_min_issue(ip->op);
    int isNop = 0;
    int wait;

    int sp = pbo_special_opex(ip, &minWait, &isNop);
    if (sp != -1) return sp;

    int myTav = C->tav[i];
    int isLast = (i == C->n - 1);
    int isFC = pb_is_flowctrl(ip->op);

    if (isLast || isFC) {
        wait = M->maxWaitTime - M->waitTime;
        if (wait < minWait) wait = minWait;
        if (isFC && !isNop && wait <= 8 && M->maxCcOrPTime <= myTav) {
            if (wait <= 6) return PBO_ODY6;
            return PBO_ODY8;
        }
        if (wait < 1) wait = 1;
    } else {
        int j = i + 1;
        wait = C->wtav[j] - M->waitTime;
        if (wait < minWait) wait = minWait;

        if (wait <= 0 && C->tav[j] != C->tav[i]) wait = 1;
        int minArchWait = wait;
        if (C->dct[i] > myTav) myTav = C->dct[i];
        int exposed = wait;
        if (C->tav[j] - myTav > exposed) exposed = C->tav[j] - myTav;
        int ccStall = M->maxCcOrPTime - myTav; if (ccStall < 0) ccStall = 0;

        if (C->req_ll[j]) {
            pbo_set_offdeck_state(M, i);
            if (ccStall > wait) wait = ccStall;
            M->maxCcOrPTime -= ccStall;
        } else if (exposed > ccStall && !C->req_pred[j]) {
            wait = exposed - ccStall;
            if      (M->numBundlesSinceOffDeck >= 48) { if (3 < curThr) curThr = 3; }
            else if (M->numBundlesSinceOffDeck >= 32) { if (3 < curThr) curThr = 3; }
            else if (M->numBundlesSinceOffDeck >= 12) { if (5 < curThr) curThr = 5; }
            if      (wait <= curThr)                    return pbo_wait_or_pair(C, i, minArchWait);
            else if (wait <= 15 && minArchWait <= 6)    return PBO_ODY6;
            else if (wait <  15 && minArchWait <= 8)    return PBO_ODY8;
            else if (wait >= 15)                        return PBO_OD;
            wait = minArchWait;
        }
    }
    return pbo_wait_or_pair(C, i, wait);
}

static int pbo_calc_wait_yield(PBOpexCtx *C, int i) {
    PBMach *M = C->M;

    if (_pb_ppoa && _pb_ppoaopex) {
        const PBInst *cip = &C->b[i];
        if ((_pb_ppoaopex & 1) && pb_is_ppoa_depbar(cip->op, cip->q)) return PBO_OD;
        if ((_pb_ppoaopex & 2) && i + 1 < C->n &&
            pb_is_ppoa_depbar(C->b[i+1].op, C->b[i+1].q) &&
            cip->coupled != PBC_DECOUPLED && cip->defs_ccp)
            return PBO_DRAIN + pbo_ccorp_lat(cip);
    }
    int wy = pbo_calc_opex(C, i);
    if (!pbo_is_odly(wy)) return wy;

    int myTav = C->tav[i]; if (C->dct[i] > myTav) myTav = C->dct[i];
    int ccStall = M->maxCcOrPTime - myTav; if (ccStall < 0) ccStall = 0;

    if (i > 0 && ccStall > 0 && !C->b[i].defs_ccp) {
        int p = i - 1;
        int wyPrev = C->opex[p];
        if (wyPrev != PBO_PIXBAR) {
            int pTav = C->tav[p]; if (C->dct[p] > pTav) pTav = C->dct[p];
            int wyPrevTime = pb_opexWait[wyPrev];
            int isPrevGroup = pbo_is_group(wyPrev);
            int nw = (myTav - pTav) + ccStall;
            if (nw < wyPrevTime) nw = wyPrevTime;
            if (nw > 15) nw = 15;
            M->maxCcOrPTime -= ccStall;
            M->waitTime = C->wtav[p];
            C->opex[p] = (isPrevGroup || nw > 11) ? (PBO_DRAIN + nw) : (PBO_PAIR + nw);
            pbo_update_wait_info(C, p, i, nw);
        }
    }
    return wy;
}

static void pbo_update_offdeck_info(PBOpexCtx *C, int p) {
    PBMach *M = C->M;
    if (p < 0) return;
    if (pbo_is_odly(C->opex[p])) {
        if (M->ipPriorOffDeck >= 0 && M->numBundlesSinceOffDeck <= 6 &&
            M->ipPriorOffDeck != p)
        {
            int q  = M->ipPriorOffDeck;
            int oT = M->time, oW = M->waitTime, oC = M->maxCcOrPTime;
            int oN = M->numBundlesSinceOffDeck;
            M->numBundlesSinceOffDeck = 0;
            M->time         = C->tav[q];
            M->waitTime     = C->wtav[q];
            M->maxCcOrPTime = C->mccp_i[q];
            int nw = pbo_calc_wait_yield(C, q);
            if (!pbo_is_odly(nw)) {
                nw = pbo_wait_or_pair(C, q, pb_opexWait[nw]);
                C->opex[q] = nw;
            }
            M->time = oT; M->waitTime = oW; M->maxCcOrPTime = oC;
            M->numBundlesSinceOffDeck = oN;
        }
        pbo_set_offdeck_state(M, p);
    }
    if (C->opex[p] != PBO_PAIR)
        M->numBundlesSinceOffDeck++;
}

static void pbo_update_wait_info(PBOpexCtx *C, int prior, int i, int waitLatency) {
    PBMach *M = C->M;
    const PBInst *ip = &C->b[i];

    if (prior == -2) {
        int wl = C->wtav[i] - M->waitTime; if (wl < 0) wl = 0;
        M->waitTime += wl;
        C->wtav[i] = M->waitTime;
        if (wl != 0) M->numBundlesSinceOffDeck++;
    } else if (prior >= 0) {
        if (waitLatency == -1) {
            int wy = pbo_calc_wait_yield(C, prior);
            C->opex[prior] = wy;
            waitLatency = pb_opexWait[wy];
        }
        M->waitTime += waitLatency;
        C->wtav[i] = M->waitTime;
        pbo_update_offdeck_info(C, prior);
    }

    if (ip->coupled != PBC_DECOUPLED) {
        for (int k = 0; k < C->dep[i].n; k++) {
            int to = C->dep[i].d[k].to, ty = C->dep[i].d[k].type;
            int t = M->waitTime + pb_dep_latency(ip, &C->b[to], ty);
            if (t > C->wtav[to]) C->wtav[to] = t;
        }
        int commit = M->waitTime + pb_lat_flow(ip, NULL);
        if (commit > M->maxWaitTime) M->maxWaitTime = commit;
        if (ip->defs_ccp) {
            int t = C->tav[i] + pbo_ccorp_lat(ip);
            if (t > M->maxCcOrPTime) M->maxCcOrPTime = t;
        }
    }
    C->mccp_i[i] = M->maxCcOrPTime;

    if (ip->coupled != PBC_COUPLED) {
        if (C->res->rbar[i] >= 0) M->sbTimeSet[C->res->rbar[i]] = M->waitTime;
        if (C->res->wbar[i] >= 0) M->sbTimeSet[C->res->wbar[i]] = M->waitTime;

        for (int k = 0; k < C->dep[i].n; k++) {
            if (C->dep[i].d[k].type != PBD_ANTI) continue;
            int to = C->dep[i].d[k].to;
            int add = pb_has_sb_reg_antidep(ip, &C->b[to]) ? PB_SB_RAW_DELAY : 0;
            int dt = M->waitTime + add, at = C->tav[i] + add;
            if (dt > C->wtav[to]) C->wtav[to] = dt;
            if (at > C->tav[to])  C->tav[to]  = at;
        }
        if (M->waitTime + PB_SB_RAW_DELAY > M->maxWaitTime)
            M->maxWaitTime = M->waitTime + PB_SB_RAW_DELAY;
    }
    if (pb_is_tex_batch_op(ip->op)) M->ipPriorTex = i;
}

static void pbo_update_last_group(PBOpexCtx *C, int prior, int i) {
    PBMach *M = C->M;
    if (prior < 0) { C->nsg_i[i] = M->numInstsSinceLastGroup;
                     C->cwseg_i[i] = M->cumuWaitSinceEndGroup; return; }
    int wy = C->opex[prior];
    M->cumuWaitSinceEndGroup += pb_opexWait[wy];
    if (wy >= 17 && wy <= 27) M->numInstsSinceLastGroup++;
    if (wy >= 1 && wy <= 11) { M->numInstsSinceLastGroup = 0; M->cumuWaitSinceEndGroup = 0; }
    C->nsg_i[i]   = M->numInstsSinceLastGroup;
    C->cwseg_i[i] = M->cumuWaitSinceEndGroup;
}

static void pbo_add_to_bundle(PBOpexCtx *C, int i) {
    PBMach *M = C->M;
    int f = M->ipInBundle;
    if (f < 0) return;
    if (C->wtav[i] > C->wtav[f]) C->wtav[f] = C->wtav[i];
    int pr = f - 1;
    if (pr >= 0 && M->ipPriorOffDeck == pr)
        M->numBundlesSinceOffDeck = M->priorNumBundlesSinceOffDeck;
    M->maxCcOrPTime = (pr >= 0) ? C->mccp_i[pr] : 0;
    M->waitTime     = (pr >= 0) ? C->wtav[pr]   : 0;
    pbo_update_wait_info(C, pr >= 0 ? pr : -2, f, -1);
}

static void pbo_calc_req_flags(const PBInst *b, int n, const PBSBResult *res,
                               u8 *req_ll, u8 *req_pred) {
    int lastProd[6];
    for (int s = 0; s < 6; s++) lastProd[s] = -1;
    for (int i = 0; i < n; i++) {
        req_ll[i] = req_pred[i] = 0;
        if (b[i].op == OP_Depbar) req_ll[i] = 1;
        for (int s = 0; s < 6; s++) {
            if (!((res->wait[i] >> s) & 1)) continue;
            int p = lastProd[s];
            if (p < 0) continue;
            if (res->wbar[p] != s) continue;
            if (b[p].is_longlat) req_ll[i] = 1;
            if (b[p].is_pred)    req_pred[i] = 1;
        }

        if (_pb_reqrel)
            for (int s = 0; s < 6; s++) if ((res->wait[i] >> s) & 1) lastProd[s] = -1;
        if (res->rbar[i] >= 0) lastProd[res->rbar[i]] = i;
        if (res->wbar[i] >= 0) lastProd[res->wbar[i]] = i;
    }
}

typedef struct {
    int ne;
    int *opex;
    int *wtav_out;

    int *s_wtav, *s_opex, *s_nsg, *s_mccpi, *s_wt, *s_mccp, *s_mwt, *s_nbod;
    u8  *s_reqll, *s_reqpred;

    const u8 *in_reqll, *in_reqpred;
} PBOpexReq;

static void pb_replay_tav(const PBInst *block, int n, const PBSBResult *res,
                          const u8 *pair, int *tav, int *dct_out, PBOpexReq *OR) {
    PBDepList *dep = (PBDepList *)calloc(n, sizeof(PBDepList));
    pb_calc_deps(block, n, dep);

    PBMach M; memset(&M, 0, sizeof M);
    M.ipInBundle = -1;
    M.lastTexTime = -999;
    M.ipPriorSched = M.ipPriorOffDeck = M.ipPriorTex = -1;
    for (int k = 0; k < 6; k++) M.sb[k] = -1;
    int *resToUse = (int *)calloc(n, sizeof(int));
    int *dct = (int *)calloc(n, sizeof(int));
    for (int i = 0; i < n; i++) { tav[i] = 0; resToUse[i] = -1; }

    int doOpex = (OR && OR->ne > 0);
    PBOpexCtx C; memset(&C, 0, sizeof C);
    if (doOpex) {
        C.b = block; C.n = OR->ne; C.res = res; C.dep = dep; C.M = &M;
        C.tav = tav; C.dct = dct;
        C.wtav    = (int *)calloc(n, sizeof(int));
        C.mccp_i  = (int *)calloc(n, sizeof(int));
        C.nsg_i   = (int *)calloc(n, sizeof(int));
        C.cwseg_i = (int *)calloc(n, sizeof(int));
        C.opex    = OR->opex;
        C.req_ll   = (u8 *)calloc(n, 1);
        C.req_pred = (u8 *)calloc(n, 1);
        if (_pb_reqglob && OR->in_reqll) {
            memcpy(C.req_ll,   OR->in_reqll,   n);
            memcpy(C.req_pred, OR->in_reqpred, n);
        } else {
            pbo_calc_req_flags(block, n, res, C.req_ll, C.req_pred);
        }
        if (OR->s_reqll)   memcpy(OR->s_reqll,   C.req_ll,   n);
        if (OR->s_reqpred) memcpy(OR->s_reqpred, C.req_pred, n);
        for (int i = 0; i < n; i++) C.opex[i] = PBO_PAIR;
    }

    int fcTail = doOpex ? C.n : n;
    while (fcTail > 0 && pb_is_flowctrl(block[fcTail - 1].op)) fcTail--;

    for (int i = 0; i < n; i++) {
        const PBInst *ip = &block[i];
        if (_pb_phaseA && ip->op == OP_Depbar) { tav[i] = 0; continue; }
        int inFcTail = (_pb_tav_mode & 256) && doOpex && i >= fcTail && i < C.n;
        int ToBePaired = (i > 0 && M.ipInBundle == i - 1 && pair[i - 1]);

        int finishPath = (_pb_tav_mode & 128) && doOpex && i == C.n - 1 && i > 0 &&
                         M.ipInBundle == i - 1 && pb_is_flowctrl(ip->op);
        if (finishPath && !ToBePaired) {
            const PBInst *f = &block[i - 1];
            int ok = f->coupled != PBC_DECOUPLED && !f->singleton;
            if (ok && f->defs_ccp) {
                int mw = 0, nop = 0;
                if (pbo_special_opex(ip, &mw, &nop) != -1) ok = 0;
            }
            if (ok) {
                for (int a = 0; a < f->n_defs && ok; a++) {
                    int r = f->defs[a]; if (r >= PB_NTOK) continue;
                    for (int b2 = 0; b2 < ip->n_uses; b2++)
                        if (ip->uses[b2] == r) { ok = 0; break; }
                }
            }
            if (ok) ToBePaired = 1;
        }

        int excl = -1;
        if (ToBePaired && M.ipInBundle >= 0 && !finishPath) excl = resToUse[M.ipInBundle];
        if (_pb_tav_dbg >= 0 && PBDBG_BASE + i == _pb_tav_dbg)
            printf("  AT %d: incoming tav=%d machine time=%d req=%02x wb=%d rb=%d sb=[%d %d %d %d %d %d]\n",
                   _pb_tav_dbg, tav[i], M.time, res->wait[i], res->wbar[i], res->rbar[i],
                   M.sb[0],M.sb[1],M.sb[2],M.sb[3],M.sb[4],M.sb[5]);
        int rt = pb_ready_time(&M, ip, tav[i], excl, &resToUse[i]);
        if (rt == 99999) { ToBePaired = 0; rt = pb_ready_time(&M, ip, tav[i], -1, &resToUse[i]); }
        if (_pb_tav_dbg >= 0 && PBDBG_BASE + i == _pb_tav_dbg)
            printf("  RT %d: res=%x rt=%d resToUse=%d paired=%d resFree[0,1,2,5]=%d,%d,%d,%d disp[0,1]=%d,%d nInB=%d ipInB=%d\n",
                   _pb_tav_dbg, ip->res, rt, resToUse[i], ToBePaired,
                   M.resTimeFree[0],M.resTimeFree[1],M.resTimeFree[2],M.resTimeFree[5],
                   M.dispTimeFree[0],M.dispTimeFree[1], M.numInBundle,
                   M.ipInBundle<0?-1:PBDBG_BASE+M.ipInBundle);
        tav[i] = rt;

        if (ip->op == OP_Depbar && !_pb_phaseA && _pb_dbc_use && _pb_dbcons) {
            int cg = _pb_dbcons[_pb_blk_base + i];
            int cj = (cg >= 0) ? cg - _pb_blk_base : -1;
            if (cj >= 0 && cj < n && dct[cj] > tav[i]) tav[i] = dct[cj];
        } else if (ip->op == OP_Depbar && !_pb_phaseA) {

            int base = -1;
            for (int j = i + 1; j < n && j <= i + _pb_dbwin && block[j].op != OP_Depbar; j++) {
                if (dct[j] <= 0) continue;
                if (base < 0) base = dct[j];
                if (dct[j] - base > 10) break;
                if (dct[j] > tav[i]) tav[i] = dct[j];
            }
        }
        if (!_pb_phaseA)
            pb_update_tav_from_sb(&M, ip, res->wait[i], res->wbar[i], res->rbar[i], &tav[i],
                                  (doOpex && i < C.n) ? &C.wtav[i] : NULL);

        int noDelayTest = finishPath || inFcTail;
        if (ToBePaired && !noDelayTest && tav[i] > M.time + 8) ToBePaired = 0;

        if (!ToBePaired) {
            if (M.numInBundle > 0) {
                M.time += 1;
                M.numInBundle = 0; M.ipInBundle = -1;
                pb_ready_time(&M, ip, tav[i], -1, &resToUse[i]);
            }
        } else if (finishPath) {

            if (tav[i] > M.time) M.time = tav[i];
            tav[M.ipInBundle] = M.time;
            if (i < C.n) pbo_add_to_bundle(&C, i);
        } else {
            if (tav[i] > M.time) {
                int f = M.ipInBundle;
                tav[f] = tav[i];

                if (_pb_tav_mode & 4) {
                    int save = M.time; M.time = tav[f];
                    pb_update_res(&M, &block[f], resToUse[f]);
                    M.time = save;
                } else {
                    pb_update_res(&M, &block[f], resToUse[f]);
                }
                for (int k = 0; k < dep[f].n; k++) {
                    int to = dep[f].d[k].to;
                    int t = tav[f] + pb_dep_latency(&block[f], &block[to], dep[f].d[k].type);
                    if (_pb_tav_dbg >= 0 && PBDBG_BASE + to == _pb_tav_dbg)
                        printf("  PAIRdep -> %d : from=%d type=%d t=%d (cur tav=%d)\n",
                               _pb_tav_dbg, PBDBG_BASE + f, dep[f].d[k].type, t, tav[to]);
                    if (t > tav[to]) tav[to] = t;
                }

            }

            if (doOpex && i < C.n) pbo_add_to_bundle(&C, i);
        }

        if (tav[i] > M.time) M.time = tav[i];

        for (int k = 0; k < dep[i].n; k++) {
            int to = dep[i].d[k].to, ty = dep[i].d[k].type;
            int lat = pb_dep_latency(ip, &block[to], ty);
            int t = M.time + lat;
            if (_pb_tav_dbg >= 0 && PBDBG_BASE + to == _pb_tav_dbg)
                printf("  dep -> %d : from=%d type=%d lat=%d time=%d t=%d (cur tav=%d)\n",
                       _pb_tav_dbg, PBDBG_BASE + i, ty, lat, M.time, t, tav[to]);
            if (t > tav[to]) tav[to] = t;

            if (ty == PBD_FLOW && ip->high_cost_sb && t > dct[to]) dct[to] = t;
        }

        tav[i] = M.time;

        if (_pb_gt_inject & 1) {
            const PBGt *g = pb_gt_at(i);
            if (g) { tav[i] = g->tav; M.time = g->tav; }
        }

        if (!doOpex && (_pb_tav_mode & 16) && ip->coupled != PBC_COUPLED) {
            for (int k = 0; k < dep[i].n; k++) {
                if (dep[i].d[k].type != PBD_ANTI) continue;
                int to = dep[i].d[k].to;
                int availTime = tav[i] +
                    (pb_has_sb_reg_antidep(ip, &block[to]) ? PB_SB_RAW_DELAY : 0);
                if (availTime > tav[to]) tav[to] = availTime;
            }
        }
        pb_update_res(&M, ip, resToUse[i]);
        { int mn = pb_min_issue(ip->op); if (mn != 0) M.time += mn - 1; }
        M.numInBundle++;
        if (M.numInBundle == 2) { M.time += 1; M.numInBundle = 0; M.ipInBundle = -1; }
        else M.ipInBundle = i;

        if (inFcTail && M.numInBundle > 0) {
            M.time += 1; M.numInBundle = 0; M.ipInBundle = -1;
        }

        if (doOpex && i < C.n) {
            int P = M.ipPriorSched;
            pbo_update_wait_info(&C, P, i, -1);
            pbo_update_last_group(&C, P, i);
            M.ipPriorSched = i;

            if (P >= 0) {
                if (OR->s_wtav)  OR->s_wtav[P]  = C.wtav[P];
                if (OR->s_opex)  OR->s_opex[P]  = C.opex[P];
                if (OR->s_mccpi) OR->s_mccpi[P] = C.mccp_i[P];
                if (OR->s_nsg)   OR->s_nsg[P]   = M.numInstsSinceLastGroup;
                if (OR->s_wt)    OR->s_wt[P]    = M.waitTime;
                if (OR->s_mccp)  OR->s_mccp[P]  = M.maxCcOrPTime;
                if (OR->s_mwt)   OR->s_mwt[P]   = M.maxWaitTime;
                if (OR->s_nbod)  OR->s_nbod[P]  = M.numBundlesSinceOffDeck;
            }
            if (i == C.n - 1) {
                C.opex[i] = pbo_calc_wait_yield(&C, i);

                if (C.n == 1 && ip->op == OP_Bra) C.opex[i] = PBO_OD;
                if (OR->s_wtav)  OR->s_wtav[i]  = C.wtav[i];
                if (OR->s_opex)  OR->s_opex[i]  = C.opex[i];
                if (OR->s_mccpi) OR->s_mccpi[i] = C.mccp_i[i];
                if (OR->s_nsg)   OR->s_nsg[i]   = M.numInstsSinceLastGroup;
                if (OR->s_wt)    OR->s_wt[i]    = M.waitTime;
                if (OR->s_mccp)  OR->s_mccp[i]  = M.maxCcOrPTime;
                if (OR->s_mwt)   OR->s_mwt[i]   = M.maxWaitTime;
                if (OR->s_nbod)  OR->s_nbod[i]  = M.numBundlesSinceOffDeck;
            }
        }
    }

    if (dct_out) for (int i = 0; i < n; i++) dct_out[i] = dct[i];
    if (doOpex && OR->wtav_out) for (int i = 0; i < n; i++) OR->wtav_out[i] = C.wtav[i];
    if (doOpex) { free(C.wtav); free(C.mccp_i); free(C.nsg_i); free(C.cwseg_i);
                  free(C.req_ll); free(C.req_pred); }
    for (int i = 0; i < n; i++) pbd_free(&dep[i]);
    free(dep); free(resToUse); free(dct);
}

#define PBA_NSB 6
#define PBA_OVQ_FIRST PBVQ_ORDERED_FIRST
#define PBA_OVQ_COUNT (PBVQ_ORDERED_LAST - PBVQ_ORDERED_FIRST + 1)

typedef struct { int n, cap; int *v; } PBAList;
static void pal_init(PBAList *l) { l->n = 0; l->cap = 0; l->v = NULL; }
static void pal_free(PBAList *l) { free(l->v); l->v = NULL; l->n = l->cap = 0; }
static void pal_clear(PBAList *l) { l->n = 0; }
static void pal_push(PBAList *l, int x) {
    if (l->n >= l->cap) { int nc = l->cap ? l->cap * 2 : 4;
        l->v = (int *)grow_arr(l->v, sizeof(int), l->cap, nc); l->cap = nc; }
    l->v[l->n++] = x;
}
static int pal_find(const PBAList *l, int x) {
    for (int i = 0; i < l->n; i++) if (l->v[i] == x) return 1; return 0;
}
static void pal_push_uniq(PBAList *l, int x) { if (!pal_find(l, x)) pal_push(l, x); }
static void pal_remove_one(PBAList *l, int x) {
    for (int i = 0; i < l->n; i++) if (l->v[i] == x) {
        memmove(l->v + i, l->v + i + 1, (l->n - i - 1) * sizeof(int)); l->n--; return; }
}
static void pal_remove_all(PBAList *l, int x) {
    int m = 0; for (int i = 0; i < l->n; i++) if (l->v[i] != x) l->v[m++] = l->v[i]; l->n = m;
}

typedef struct {
    unsigned char pk;
    unsigned char subq;
    unsigned char deleted;
    signed char   predKind;
    int issueOrder;
    int def;
    int reg;
    PBAList uses;
} PBAVsb;

typedef struct {
    PBAList succ, pred;
    int loopHdr, loopRegion;
    int unknown;
} PBACfgBB;

static int pba_pred_kind(const PBInst *ip) {
    if (!ip->is_pred) return 0;
    return ip->pred_neg ? (15 - (ip->pred_reg + 1)) : (ip->pred_reg + 1);
}
static int pba_is_compl(int a, int b) { return (a + b) == 15; }

static int pba_sovq(const PBInst *ip) {
    if (ip->vq >= PBVQ_ORDERED_FIRST && ip->vq <= PBVQ_ORDERED_LAST)
        return ip->vq - PBA_OVQ_FIRST;
    return -1;
}

static void pba_build_cfg1(const PBInst *inst, int n, const PBBlock *bbs, int nbb,
                           PBACfgBB *cfg, const int *brxTgt, int nBrxTgt) {
    enum { C_SSY, C_PBK, C_PCNT, C_SYNC, C_BRK, C_CONT, C_BRA, C_BRX, C_EXIT, C_OTHER };
    int *cat = (int *)malloc(sizeof(int) * (n ? n : 1));
    int *tgt = (int *)malloc(sizeof(int) * (n ? n : 1));
    int *guarded = (int *)malloc(sizeof(int) * (n ? n : 1));
    int *bbof = (int *)malloc(sizeof(int) * (n ? n : 1));
    for (int bi = 0; bi < nbb; bi++)
        for (int i = bbs[bi].start; i < bbs[bi].end; i++) bbof[i] = bi;

    for (int i = 0; i < n; i++) {
        u64 q = inst[i].q;
        int nm = inst[i].op;
        int has_pred = !(nm == OP_Ssy || nm == OP_Pbk || nm == OP_Pcnt);
        guarded[i] = has_pred && (((q >> 16) & 7) != PT);
        int branch = (nm == OP_Bra || nm == OP_Jmp || nm == OP_Ssy ||
                      nm == OP_Pbk || nm == OP_Pcnt || nm == OP_Cal);
        int tj = -1;
        if (branch) {
            int off24 = (int)((q >> 20) & 0xFFFFFF);
            if (off24 & 0x800000) off24 |= ~0xFFFFFF;
            int tr = (int)inst[i].rel + 8 + off24;
            for (int j = 0; j < n; j++) if ((int)inst[j].rel == tr) { tj = j; break; }

            if (tj < 0)
                for (int j = 0; j < n; j++) if ((int)inst[j].rel >= tr) { tj = j; break; }
        }
        tgt[i] = tj;
        if      (nm == OP_Ssy)  cat[i] = C_SSY;
        else if (nm == OP_Pbk)  cat[i] = C_PBK;
        else if (nm == OP_Pcnt) cat[i] = C_PCNT;
        else if (nm == OP_Sync) cat[i] = C_SYNC;
        else if (nm == OP_Brk)  cat[i] = C_BRK;
        else if (nm == OP_Cont) cat[i] = C_CONT;
        else if (nm == OP_Bra || nm == OP_Jmp) cat[i] = C_BRA;
        else if (nm == OP_Brx || nm == OP_Jmx) cat[i] = C_BRX;
        else if (nm == OP_Exit || nm == OP_Ret) cat[i] = C_EXIT;
        else cat[i] = C_OTHER;
    }

    IdxList *isucc = (IdxList *)malloc(sizeof(IdxList) * (n ? n : 1));
    for (int i = 0; i < n; i++) il_init(&isucc[i]);
    u8 *unk = (u8 *)calloc(n ? n : 1, 1);
    #define ADD_S(i_, j_) do { int _j=(j_); if (_j>=0 && _j<n) il_add(&isucc[i_], _j); } while (0)

    StkPool pool; sp_init(&pool);
    IdxList *states = (IdxList *)malloc(sizeof(IdxList) * (n ? n : 1));
    for (int i = 0; i < n; i++) il_init(&states[i]);
    int wcap = 4096, wlen = 0, ok = 1;
    int *wq_i = (int *)malloc(sizeof(int) * wcap);
    int *wq_s = (int *)malloc(sizeof(int) * wcap);
    int budget = 8 * n + 4096;
    #define PUSH_ST(ii, sk) do { int _ii=(ii); \
        if (_ii>=0 && _ii<n) { int _si = sp_intern(&pool, &(sk)); int _seen=0; \
            for (int _k=0;_k<states[_ii].n;_k++) if (states[_ii].v[_k]==_si) { _seen=1; break; } \
            if (!_seen) { il_add(&states[_ii], _si); \
                if (wlen>=wcap) { wq_i=(int*)grow_arr(wq_i,sizeof(int),wcap,wcap*2); \
                    wq_s=(int*)grow_arr(wq_s,sizeof(int),wcap,wcap*2); wcap*=2; } \
                wq_i[wlen]=_ii; wq_s[wlen]=_si; wlen++; if (wlen>budget) ok=0; } } } while (0)

    Stk *tstk = (Stk *)calloc(nbb ? nbb : 1, sizeof(Stk));
    { Stk cur; cur.depth = 0; int tb = 0;
      for (int i = 0; i < n; i++) {
          while (tb < nbb && bbs[tb].start == i) tstk[tb++] = cur;
          int c = cat[i];
          if (c == C_SSY || c == C_PBK || c == C_PCNT) {
              if (cur.depth < 40) { cur.typ[cur.depth] = (u8)(c==C_SSY?'s':c==C_PBK?'b':'c');
                                    cur.tgt[cur.depth] = tgt[i]; cur.depth++; }
          } else if (c == C_SYNC) {
              if (cur.depth > 0 && cur.typ[cur.depth-1] == 's') cur.depth--;
          } else if (c == C_BRK) {
              for (int p = cur.depth - 1; p >= 0; p--) if (cur.typ[p] == 'b') { cur.depth = p; break; }
          }
      } }

    Stk empty; empty.depth = 0;
    int head = 0;
    if (n) PUSH_ST(0, empty);
    for (;;) {
    while (head < wlen && ok) {
        int ci = wq_i[head];
        Stk stk = pool.v[wq_s[head]];
        head++;
        int nxt = (ci + 1 < n) ? ci + 1 : -1;
        int c = cat[ci];
        if (c == C_SSY || c == C_PBK || c == C_PCNT) {
            ADD_S(ci, nxt);
            Stk ns = stk;
            if (ns.depth < 40) { ns.typ[ns.depth] = (u8)(c==C_SSY?'s':c==C_PBK?'b':'c');
                                 ns.tgt[ns.depth] = tgt[ci]; ns.depth++; }
            else ok = 0;
            PUSH_ST(nxt, ns);
        } else if (c == C_SYNC) {
            if (stk.depth > 0 && stk.typ[stk.depth-1] == 's') {
                int j = stk.tgt[stk.depth-1];
                ADD_S(ci, j); Stk ns = stk; ns.depth--; PUSH_ST(j, ns);
            } else unk[ci] = 1;
            if (guarded[ci]) { ADD_S(ci, nxt); PUSH_ST(nxt, stk); }
        } else if (c == C_BRK || c == C_CONT) {
            int want = (c == C_BRK) ? 'b' : 'c', k = -1;
            for (int p = stk.depth - 1; p >= 0; p--) if (stk.typ[p] == want) { k = p; break; }
            if (k >= 0) {
                int j = stk.tgt[k]; ADD_S(ci, j);
                Stk ns = stk; ns.depth = (c == C_BRK) ? k : k + 1; PUSH_ST(j, ns);
            } else unk[ci] = 1;
            if (guarded[ci]) { ADD_S(ci, nxt); PUSH_ST(nxt, stk); }
        } else if (c == C_BRA) {
            if (tgt[ci] >= 0) { ADD_S(ci, tgt[ci]); PUSH_ST(tgt[ci], stk); }
            else unk[ci] = 1;
            if (guarded[ci]) { ADD_S(ci, nxt); PUSH_ST(nxt, stk); }
        } else if (c == C_BRX) {
            if (nBrxTgt > 0) {
                for (int t = 0; t < nBrxTgt; t++) { ADD_S(ci, brxTgt[t]); PUSH_ST(brxTgt[t], stk); }
            } else unk[ci] = 1;
            if (guarded[ci]) { ADD_S(ci, nxt); PUSH_ST(nxt, stk); }
        } else if (c == C_EXIT) {
            if (guarded[ci]) { ADD_S(ci, nxt); PUSH_ST(nxt, stk); }
        } else {
            ADD_S(ci, nxt); PUSH_ST(nxt, stk);
        }
    }
    if (!ok) break;

    { int seed = -1, seedbi = 0;
      for (int bi = 0; bi < nbb; bi++) {
          int s0 = bbs[bi].start;
          if (s0 < n && states[s0].n == 0) { seed = s0; seedbi = bi; break; }
      }
      if (seed < 0) break;
      PUSH_ST(seed, tstk[seedbi]);
    }
    }
    free(tstk);

    for (int bi = 0; bi < nbb; bi++) {
        pal_init(&cfg[bi].succ); pal_init(&cfg[bi].pred);
        cfg[bi].loopHdr = -1; cfg[bi].loopRegion = -1; cfg[bi].unknown = 0;
    }
    if (!ok) { for (int bi = 0; bi < nbb; bi++) cfg[bi].unknown = 1; }
    else {
        for (int bi = 0; bi < nbb; bi++) {
            int last = bbs[bi].end - 1;
            if (last < bbs[bi].start) { cfg[bi].unknown = 1; continue; }
            if (unk[last]) cfg[bi].unknown = 1;
            if (states[last].n == 0) cfg[bi].unknown = 1;
            for (int k = 0; k < isucc[last].n; k++) {
                int sb = bbof[isucc[last].v[k]];
                pal_push_uniq(&cfg[bi].succ, sb);
            }
        }
        for (int bi = 0; bi < nbb; bi++)
            for (int k = 0; k < cfg[bi].succ.n; k++)
                pal_push_uniq(&cfg[cfg[bi].succ.v[k]].pred, bi);

        for (int span = nbb; span >= 0; span--)
            for (int t = 0; t < nbb; t++)
                for (int k = 0; k < cfg[t].succ.n; k++) {
                    int h = cfg[t].succ.v[k];
                    if (h > t) continue;
                    if (t - h != span) continue;
                    for (int b = h; b <= t; b++) { cfg[b].loopHdr = h; cfg[b].loopRegion = t; }
                }
    }

    for (int i = 0; i < n; i++) { il_free(&isucc[i]); il_free(&states[i]); }
    free(isucc); free(states); sp_free(&pool);
    free(wq_i); free(wq_s); free(unk);
    free(cat); free(tgt); free(guarded); free(bbof);
    #undef ADD_S
    #undef PUSH_ST
}

static void pba_build_cfg(const PBInst *inst, int n, const PBBlock *bbs, int nbb,
                          PBACfgBB *cfg) {
    pba_build_cfg1(inst, n, bbs, nbb, cfg, NULL, 0);
    int hasBrx = 0;
    for (int bi = 0; bi < nbb; bi++) {
        int last = bbs[bi].end - 1;
        if (last >= bbs[bi].start && (inst[last].op == OP_Brx || inst[last].op == OP_Jmx))
            hasBrx = 1;
    }
    if (!hasBrx) return;
    int *tg = (int *)malloc(sizeof(int) * (nbb ? nbb : 1));
    int ntg = 0;
    for (int bi = 1; bi < nbb; bi++)
        if (cfg[bi].pred.n == 0 && bbs[bi].end > bbs[bi].start) tg[ntg++] = bbs[bi].start;
    if (ntg) {
        for (int bi = 0; bi < nbb; bi++) { pal_free(&cfg[bi].succ); pal_free(&cfg[bi].pred); }
        memset(cfg, 0, sizeof(PBACfgBB) * (nbb ? nbb : 1));
        pba_build_cfg1(inst, n, bbs, nbb, cfg, tg, ntg);
    }
    free(tg);
}

typedef struct {

    int DoDepBar, LLsbDesignated, DoCrossBlock, DoAcrossBackedge, DoReqCommit;
    int firstSB, lastSB, lastNonLLSb, llsb, firstLlsbPsb, psbReassignStallLimit;
    unsigned knobs;

    PBAVsb *v; int nv, capv, nvmax;

    PBAList *ird, *iwr, *ireq;
    PBAList rdOf[PB_NTOK], wrOf[PB_NTOK];
    PBAList q[PBA_OVQ_COUNT * 2];
    int lastIssueOrder;

    int psbNo[PBA_NSB];
    int psbHasInst[PBA_NSB];
    int psbTepid[PBA_NSB];
    int psbWrProt[PBA_NSB];
    PBAList psbProd[PBA_NSB];

    int lvinUsed[PBA_NSB];
    u8 *lvinRd[PBA_NSB], *lvinWr[PBA_NSB];
    int regLvInRd[PB_NTOK], regLvInWr[PB_NTOK];
    u8  *lvOutRd, *lvOutWr;
    int *lvOutDep;
    u8  *liveRegLlsb, *liveRegPsb;
    int blockIndexLastPsb[PBA_NSB];

    int depCnt[PB_NTOK], depOther[PB_NTOK];
    signed char depPred[PB_NTOK];

    int dbLeCnt, dbLLAfter, dbDist, dbBeforeIp;
    int dbConsumer;

    int dbGenCons[128]; int nDbGen;
    int dbRealNext;
    int *dbConsumerOf;

    int *wbar, *rbar; u8 *req;
    const int *tav;
    const PBInst *insts;

    int *loc; int nloc;
    int nglob;
    int bbstart, bbend;
} PBACtx;

#define PBA_DUMMY 0x7FFFFFFF

static int pba_gi(PBACtx *C, int k) { return C->loc[k]; }
static const PBInst *pba_ip(PBACtx *C, int k) { return &C->insts[C->loc[k]]; }
static int pba_tav(PBACtx *C, int k) { return C->tav ? C->tav[C->loc[k]] : 0; }

static int pba_new_vsb(PBACtx *C, int def, int reg, int pk, int predKind) {
    if (C->nv + 1 >= C->capv) {
        int nc = C->capv ? C->capv * 2 : 256;
        C->v = (PBAVsb *)grow_arr(C->v, sizeof(PBAVsb), C->capv, nc);
        C->capv = nc;
    }
    int id = ++C->nv;
    PBAVsb *V = &C->v[id];

    PBAList keep;
    if (id <= C->nvmax) keep = V->uses;
    else { pal_init(&keep); C->nvmax = id; }
    memset(V, 0, sizeof(*V));
    V->uses = keep; V->uses.n = 0;
    V->pk = (unsigned char)pk; V->subq = 3; V->def = def; V->reg = (short)reg;
    V->predKind = (signed char)predKind;
    return id;
}
static void pba_protect(PBACtx *C, int reg, int vsb, int pk) {
    if (pk & 1) pal_push_uniq(&C->rdOf[reg], vsb);
    if (pk & 2) pal_push_uniq(&C->wrOf[reg], vsb);
}
static void pba_release(PBACtx *C, int vsb) {
    PBAVsb *V = &C->v[vsb];
    if (V->pk == 0) return;
    if (V->reg >= 0) {
        if (V->pk & 1) pal_remove_one(&C->rdOf[V->reg], vsb);
        if (V->pk & 2) pal_remove_one(&C->wrOf[V->reg], vsb);
    }
    V->pk = 0;
}
static void pba_add_req(PBACtx *C, int k, int vsb) {
    PBAVsb *V = &C->v[vsb];
    pal_remove_all(&V->uses, k);
    pal_push(&V->uses, k);
    pal_remove_one(&C->ireq[k], vsb);
    pal_push(&C->ireq[k], vsb);
}
static void pba_delete_vsb(PBACtx *C, int vsb) {
    PBAVsb *V = &C->v[vsb];
    if (V->def >= 0) {
        pal_remove_all(&C->ird[V->def], vsb);
        pal_remove_all(&C->iwr[V->def], vsb);
        pal_remove_all(&C->ireq[V->def], vsb);
        V->def = -1;
    }
    for (int i = 0; i < V->uses.n; i++) pal_remove_all(&C->ireq[V->uses.v[i]], vsb);
    pal_clear(&V->uses);
    V->deleted = 1;
}
static int pba_vsb_sovq(PBACtx *C, int vsb) {
    int d = C->v[vsb].def;
    if (d < 0) return -1;
    return pba_sovq(pba_ip(C, d));
}

static void pba_assign_vsb(PBACtx *C) {
    int n = C->nloc;
    for (int r = 0; r < PB_NTOK; r++) { pal_clear(&C->rdOf[r]); pal_clear(&C->wrOf[r]); }
    for (int i = 0; i < PBA_OVQ_COUNT * 2; i++) pal_clear(&C->q[i]);
    for (int i = 0; i < n; i++) { pal_clear(&C->ird[i]); pal_clear(&C->iwr[i]); pal_clear(&C->ireq[i]); }
    C->nv = 0;
    C->lastIssueOrder = 0;

    PBAList inV, outV;  pal_init(&inV); pal_init(&outV);

    for (int k = 0; k < n; k++) {
        const PBInst *ip = pba_ip(C, k);
        int ipPred = pba_pred_kind(ip);
        pal_clear(&inV); pal_clear(&outV);

        for (int t = ip->n_suses - 1; t >= 0; t--) {
            int r = ip->suses[t];
            if (r < 0 || r >= PB_NTOK) continue;
            for (int z = 0; z < C->wrOf[r].n; z++) pal_push_uniq(&inV, C->wrOf[r].v[z]);
        }

        for (int t = 0; t < ip->n_defs; t++) {
            int r = ip->defs[t];
            if (r < 0 || r >= PB_NTOK) continue;
            for (int z = 0; z < C->rdOf[r].n; z++) pal_push_uniq(&outV, C->rdOf[r].v[z]);
            for (int z = 0; z < C->wrOf[r].n; z++) pal_push_uniq(&outV, C->wrOf[r].v[z]);
        }

        for (int a = 0; a < inV.n; a++) {
            int vsb = inV.v[a];
            if ((C->knobs & 1) && ip->is_pred &&
                pba_is_compl(ipPred, C->v[vsb].predKind))
                continue;
            pba_add_req(C, k, vsb);
            pba_release(C, vsb);
            pal_remove_one(&outV, vsb);

            int d = C->v[vsb].def;
            if (d >= 0) {
                PBAList *rl = &C->ird[d];
                for (int z = 0; z < rl->n; ) {
                    int rv = rl->v[z];
                    if (C->v[rv].pk != 0) {
                        pba_delete_vsb(C, rv);
                        pba_release(C, rv);
                        pal_remove_one(&outV, rv);
                        continue;
                    }
                    z++;
                }
            }
        }

        {
            int qip = pba_sovq(ip);
            for (int a = 0; a < outV.n; a++) {
                int vsb = outV.v[a];
                if ((C->knobs & 1) && ip->is_pred &&
                    pba_is_compl(ipPred, C->v[vsb].predKind))
                    continue;
                int vq = pba_vsb_sovq(C, vsb);
                if (vq == qip && vq >= 0) continue;
                pba_add_req(C, k, vsb);
                pba_release(C, vsb);
            }
        }

        if ((C->knobs & 2) && k == n - 1) {
            int op = ip->op;
            if (op == OP_Cal || op == OP_Jcal || op == OP_Ret || op == OP_Exit) {

                int finalExit = (op == OP_Exit) || ((_pb_retc & 4) && op == OP_Ret);

                int retc = (ip->pred_reg != 7) && (op == OP_Ret || op == OP_Exit)
                           && !(_pb_sbexit & 64);

                if (!(_pb_sbexit & 1)) finalExit = 0, retc = 1;
                if (finalExit) {
                    if (!retc) {

                        int _lastbb = !(_pb_sbexit & 8) || C->bbend >= C->nglob;
                        if (_lastbb)
                        for (int vsb = 1; vsb <= C->nv; vsb++)
                            if (C->v[vsb].pk != 0 &&
                                (!(_pb_sbexit & 4) || C->v[vsb].uses.n == 0))
                                { if (!(_pb_sbexit & 16)) pba_delete_vsb(C, vsb);
                                  if (!(_pb_sbexit & 32)) pba_release(C, vsb); }
                    }
                } else if (!(_pb_sbexit & 2)) {

                } else {
                    for (int vsb = 1; vsb <= C->nv; vsb++)
                        if (C->v[vsb].pk != 0) { pba_add_req(C, k, vsb); pba_release(C, vsb); }
                }
            }
        }

        u8 wrSet[256]; memset(wrSet, 0, sizeof wrSet);
        if (ip->needs_wsb) {
            for (int t = 0; t < ip->n_defs; t++) {
                int r = ip->defs[t];
                if (r < 0 || r >= PB_NTOK) continue;
                int vsb = pba_new_vsb(C, k, r, 2, ipPred);
                pal_push(&C->iwr[k], vsb);
                pba_protect(C, r, vsb, 2);
                if (r < 255) wrSet[r] = 1;
            }
        }

        if (ip->needs_rsb) {
            for (int t = ip->n_suses - 1; t >= 0; t--) {
                int r = ip->suses[t];
                if (r < 0 || r >= 255) continue;
                if (wrSet[r]) continue;
                int vsb = pba_new_vsb(C, k, r, 1, ipPred);
                pal_push(&C->ird[k], vsb);
                pba_protect(C, r, vsb, 1);
            }
        }

        if (C->knobs & 1) {
            for (int t = 0; t < ip->n_defs; t++) {
                int r = ip->defs[t];
                if (r < 300 || r > 306) continue;
                int pr = r - 300;
                int kt = pr + 1, kf = 15 - (pr + 1);
                for (int vsb = 1; vsb <= C->nv; vsb++)
                    if (C->v[vsb].pk != 0 &&
                        (C->v[vsb].predKind == kt || C->v[vsb].predKind == kf))
                        C->v[vsb].predKind = 0;
            }
        }
    }

    {
        int latest[PBA_OVQ_COUNT * 2];
        PBAList tmp; pal_init(&tmp);
        PBAList vs;  pal_init(&vs);
        for (int k = 0; k < n; k++) {
            pal_clear(&vs);
            for (int z = 0; z < C->ireq[k].n; z++) pal_push(&vs, C->ireq[k].v[z]);
            if (vs.n) {
                for (int z = 0; z < PBA_OVQ_COUNT * 2; z++) latest[z] = -1;
                for (int z = 0; z < vs.n; z++) {
                    int vsb = vs.v[z];
                    int sq = C->v[vsb].subq;
                    int vq = pba_vsb_sovq(C, vsb);
                    if (vq < 0 || sq > 1) continue;
                    if (!pal_find(&C->q[vq * 2 + sq], vsb)) continue;
                    if (latest[vq * 2 + sq] < C->v[vsb].issueOrder)
                        latest[vq * 2 + sq] = C->v[vsb].issueOrder;
                }
                pal_clear(&tmp);
                for (int vq = 0; vq < PBA_OVQ_COUNT; vq++) {
                    PBAList *qr = &C->q[vq * 2 + 0];
                    while (qr->n) {
                        int vsb = qr->v[0], io = C->v[vsb].issueOrder;
                        if (!(io < latest[vq*2+0] || io <= latest[vq*2+1])) break;
                        pal_remove_one(qr, vsb);
                        pal_push(&tmp, vsb);
                        pba_delete_vsb(C, vsb);
                    }
                    PBAList *qw = &C->q[vq * 2 + 1];
                    while (qw->n) {
                        int vsb = qw->v[0], io = C->v[vsb].issueOrder;
                        if (!(io < latest[vq*2+1])) break;
                        pal_remove_one(qw, vsb);
                        pal_push(&tmp, vsb);
                        pba_delete_vsb(C, vsb);
                    }
                }
                for (int z = 0; z < tmp.n; z++) pal_remove_all(&vs, tmp.v[z]);

                for (int z = 0; z < vs.n; z++) {
                    int vsb = vs.v[z];
                    int vq = pba_vsb_sovq(C, vsb);
                    if (vq < 0) continue;
                    int sq = C->v[vsb].subq;
                    if (sq > 1) continue;
                    pal_remove_one(&C->q[vq * 2 + sq], vsb);
                }
            }

            if (C->ird[k].n || C->iwr[k].n) {
                int vq = pba_sovq(pba_ip(C, k));
                if (vq >= 0) {
                    C->lastIssueOrder++;
                    for (int z = 0; z < C->ird[k].n; z++) {
                        int vsb = C->ird[k].v[z];
                        C->v[vsb].issueOrder = C->lastIssueOrder;
                        C->v[vsb].subq = 0;
                        pal_push(&C->q[vq * 2 + 0], vsb);
                    }
                    for (int z = 0; z < C->iwr[k].n; z++) {
                        int vsb = C->iwr[k].v[z];
                        C->v[vsb].issueOrder = C->lastIssueOrder;
                        C->v[vsb].subq = 1;
                        pal_push(&C->q[vq * 2 + 1], vsb);
                    }
                }
            }
        }
        pal_free(&tmp); pal_free(&vs);
    }
    pal_free(&inV); pal_free(&outV);
}

static int pba_psb_available(PBACtx *C, int psb) {
    if (C->psbNo[psb] != -1) return 0;
    if ((C->knobs & 8) && C->lvinUsed[psb]) return 0;
    return 1;
}
static int pba_psb_live(PBACtx *C, int psb) { return !pba_psb_available(C, psb); }

static void pba_release_psb(PBACtx *C, int psb) {
    C->psbNo[psb] = -1; C->psbHasInst[psb] = 0; C->psbWrProt[psb] = 0;
}
static void pba_set_req(PBACtx *C, int k, int psb) { C->req[pba_gi(C, k)] |= (u8)(1 << psb); }
static void pba_clr_req(PBACtx *C, int k, int psb) { C->req[pba_gi(C, k)] &= (u8)~(1 << psb); }
static int  pba_get_req(PBACtx *C, int k) { return C->req[pba_gi(C, k)]; }

static void pba_set_consume(PBACtx *C, int psb, int k) {
    if (k == PBA_DUMMY) { C->psbNo[psb] = PBA_DUMMY; C->psbHasInst[psb] = 0; return; }
    C->psbNo[psb] = k; C->psbHasInst[psb] = 1;
    pba_set_req(C, k, psb);
}
static void pba_unset_consume(PBACtx *C, int psb, int k) {
    if (C->psbHasInst[psb] && k != PBA_DUMMY) pba_clr_req(C, k, psb);
    pba_release_psb(C, psb);
}
static void pba_require_psb(PBACtx *C, int psb, int k) {
    if (C->psbNo[psb] == -1) { pba_set_consume(C, psb, k); return; }
    int old = C->psbNo[psb];
    if (old > k) { pba_unset_consume(C, psb, old); pba_set_consume(C, psb, k); }
}

static int pba_earliest_consumer(PBACtx *C, const PBAList *vsbs) {
    int best = PBA_DUMMY;
    for (int i = 0; i < vsbs->n; i++) {
        PBAVsb *V = &C->v[vsbs->v[i]];
        int cn = (V->uses.n > 0) ? V->uses.v[0] : PBA_DUMMY;
        if (best > cn) best = cn;
    }
    return best;
}

static int pba_psb_consume_no(PBACtx *C, int psb) {
    if (!pba_psb_live(C, psb)) return -1;
    return C->psbNo[psb];
}
static int pba_same_consume(PBACtx *C, const PBAList *vsbs, int isWrite) {
    int ec = pba_earliest_consumer(C, vsbs);
    for (int ii = C->firstSB; ii <= C->lastSB; ii++) {
        if (pba_psb_consume_no(C, ii) != ec) continue;
        if (ec == PBA_DUMMY) {
            if (C->DoCrossBlock && (isWrite || C->psbWrProt[ii])) continue;
        }
        return ii;
    }
    return -1;
}
static int pba_avail_psb(PBACtx *C, int startPsb) {
    for (int ii = startPsb; ii <= C->lastSB; ii++) if (pba_psb_available(C, ii)) return ii;
    return -1;
}
static int pba_lvin_psb(PBACtx *C, int startPsb) {
    int r = -1;
    for (int ii = startPsb; ii <= C->lastSB; ii++) {
        if (C->psbNo[ii] == -1 && C->lvinUsed[ii]) {
            r = ii;
            int wr = 0;
            for (int t = 0; t < PB_NTOK; t++) if (C->lvinWr[ii][t]) { wr = 1; break; }
            if (!wr) break;
        }
    }
    return r;
}
static void pba_clear_lvin(PBACtx *C, int psb) {
    C->lvinUsed[psb] = 0;
    for (int t = 0; t < PB_NTOK; t++) {
        if (C->lvinRd[psb][t]) { C->regLvInRd[t] &= ~(1 << psb); C->lvinRd[psb][t] = 0; }
        if (C->lvinWr[psb][t]) { C->regLvInWr[t] &= ~(1 << psb); C->lvinWr[psb][t] = 0; }
    }
}

static int pba_tepid(PBACtx *C, int k, int isRead) {
    const PBInst *ip = pba_ip(C, k);
    return pba_tav(C, k) + (isRead ? pb_read_sb_latency(ip) : pb_write_sb_latency(ip));
}
static int pba_inst_tav(PBACtx *C, int k) {
    if (k == PBA_DUMMY) return PBA_DUMMY;
    return pba_tav(C, k);
}
static int pba_stall_delta(PBACtx *C, int prod, int cons, int isWrite, int psb) {
    int psbTepid = C->psbTepid[psb];
    int psbTa = C->psbHasInst[psb] ? pba_inst_tav(C, C->psbNo[psb]) : PBA_DUMMY;
    int psbStall = psbTepid - psbTa; if (psbStall < 0) psbStall = 0;
    int vsbTepid = pba_tepid(C, prod, !isWrite);
    int maxT = vsbTepid > psbTepid ? vsbTepid : psbTepid;
    int ct = pba_inst_tav(C, cons);
    int minTa = ct < psbTa ? ct : psbTa;
    int newStall = maxT - minTa; if (newStall < 0) newStall = 0;
    return newStall - psbStall;
}
static void pba_assign_psb_to_vsb(PBACtx *C, int psb, PBAList *vsbs, int k, int isWrite);

static int pba_smallest_reassign(PBACtx *C, int psb, int *newPsb) {
    int smallest = PBA_DUMMY;
    for (int ii = C->firstSB; ii <= C->lastSB; ii++) {
        if (!pba_psb_live(C, ii) || ii == psb) continue;
        int nd = 0;
        for (int z = 0; z < C->psbProd[psb].n; z++) {
            int pk = C->psbProd[psb].v[z];
            int gi = pba_gi(C, pk);
            int isW = (C->wbar[gi] == psb);
            int d = pba_stall_delta(C, pk, C->psbHasInst[psb] ? C->psbNo[psb] : PBA_DUMMY, isW, ii);
            if (d > nd) nd = d;
        }
        if (smallest > nd) { smallest = nd; *newPsb = ii; if (!smallest) break; }
    }
    return smallest;
}
static void pba_reassign_psb(PBACtx *C, int psb, int newPsb) {
    PBAList prod; pal_init(&prod);
    for (int z = 0; z < C->psbProd[psb].n; z++) pal_push(&prod, C->psbProd[psb].v[z]);
    for (int z = 0; z < prod.n; z++) {
        int pk = prod.v[z], gi = pba_gi(C, pk);
        if (C->rbar[gi] == psb) pba_assign_psb_to_vsb(C, newPsb, &C->ird[pk], pk, 0);
        if (C->wbar[gi] == psb) pba_assign_psb_to_vsb(C, newPsb, &C->iwr[pk], pk, 1);
    }
    pal_free(&prod);
    pal_clear(&C->psbProd[psb]);
    if (C->psbHasInst[psb]) { pba_clr_req(C, C->psbNo[psb], psb); C->psbHasInst[psb] = 0; }
    C->psbNo[psb] = -1;
}
static int pba_smallest_stall_delta(PBACtx *C, int k, PBAList *vsbs, int isWrite, int startPsb) {
    int psb = -1, smallest = PBA_DUMMY;
    int cons = pba_earliest_consumer(C, vsbs);
    for (int ii = startPsb; ii <= C->lastSB; ii++) {
        if (!pba_psb_live(C, ii)) continue;
        int d = pba_stall_delta(C, k, cons, isWrite, ii);
        if (smallest > d) { smallest = d; psb = ii; if (!smallest) break; }
    }
    if (psb >= 0 && smallest > C->psbReassignStallLimit) {
        int np = -1;
        int ns = pba_smallest_reassign(C, psb, &np);
        if (ns < smallest && np != -1) pba_reassign_psb(C, psb, np);
    }
    return psb;
}

static int _pb_sb_at = -1;
static int _pb_sb_dbg = 0;

static int _pb_sb_passes = 16;
static int pba_heuristic(PBACtx *C, int k, PBAList *vsbs, int isWrite) {
    const PBInst *ip = pba_ip(C, k);
    if (_pb_sb_at >= 0 && pba_gi(C, k) == _pb_sb_at) {
        printf("  HEUR gi=%d k=%d %s wr=%d  vsbs={", pba_gi(C,k), k, isWrite?"WR":"RD", isWrite);
        for (int z = 0; z < vsbs->n; z++) {
            printf("v%d(reg=%d,uses=", vsbs->v[z], C->v[vsbs->v[z]].reg);
            for (int y = 0; y < C->v[vsbs->v[z]].uses.n; y++) printf("%d;", C->v[vsbs->v[z]].uses.v[y]);
            printf(") ");
        }
        printf("} ec=%d\n   psbNo=", pba_earliest_consumer(C, vsbs));
        for (int s = 0; s < 6; s++) printf("[%d]=%d(gi %d,wp=%d,tep=%d) ", s, C->psbNo[s],
            (C->psbNo[s]>=0 && C->psbNo[s]!=PBA_DUMMY)?pba_gi(C,C->psbNo[s]):-1,
            C->psbWrProt[s], C->psbTepid[s]);
        printf("\n   lvin=");
        for (int s = 0; s < 6; s++) printf("%d", C->lvinUsed[s]);
        printf("\n   tav[k]=%d tepid=%d consTav=", pba_tav(C,k), pba_tepid(C,k,!isWrite));
        { int ec = pba_earliest_consumer(C, vsbs);
          printf("%d\n   delta=", pba_inst_tav(C, ec));
          for (int s = C->firstSB; s <= C->lastSB; s++) {
              if (!pba_psb_live(C, s)) { printf("[%d]=free ", s); continue; }
              printf("[%d]=%d(psbTav=%d) ", s, pba_stall_delta(C, k, ec, isWrite, s),
                     C->psbHasInst[s] ? pba_inst_tav(C, C->psbNo[s]) : -1);
          } }
        printf("\n");
    }
    if (C->DoDepBar && isWrite && ip->high_cost_sb) return C->llsb;
    int psb = pba_same_consume(C, vsbs, isWrite);
    if (psb != -1) return psb;
    int firstPsb = C->firstSB;
    psb = pba_avail_psb(C, firstPsb);
    if (psb != -1) return psb;
    if ((C->knobs & 8) && C->DoCrossBlock) {
        psb = pba_lvin_psb(C, firstPsb);
        if (psb != -1) {

            if (_pb_lvinreq && isWrite) {
                int nwr = 0;
                for (int t = 0; t < PB_NTOK; t++) if (C->lvinWr[psb][t]) { nwr = 1; break; }
                if (_pb_lvinreq == 1 || (_pb_lvinreq == 2 && !nwr)) {
                    pba_set_req(C, k, psb);
                    pba_clear_lvin(C, psb);
                }
            }
#ifndef INKV_LIB
            if (_pb_lvin_log) {
                int nrd = 0, nwr = 0;
                for (int t = 0; t < PB_NTOK; t++) { nrd += C->lvinRd[psb][t]; nwr += C->lvinWr[psb][t]; }
                fprintf(stderr, "LVINPSB gi=%d %s psb=%d nrd=%d nwr=%d hc=%d ll=%d op=%s\n",
                        pba_gi(C, k), isWrite ? "WR" : "RD", psb, nrd, nwr,
                        ip->high_cost_sb, ip->is_longlat,
                        (ip->op >= 0 && ip->op < 178) ? SM50_NAME[ip->op] : "?");
            }
#endif
            return psb;
        }
    }
    if (C->knobs & 0x20) {
        psb = pba_smallest_stall_delta(C, k, vsbs, isWrite, firstPsb);
        if (psb != -1) return psb;
    }

    { int best = -1, bestc = -1;
      for (int ii = C->firstSB; ii <= C->lastSB; ii++) {
          if (!pba_psb_live(C, ii)) continue;
          if (C->psbNo[ii] > bestc) { bestc = C->psbNo[ii]; best = ii; }
      }
      return best != -1 ? best : C->firstSB; }
}

static void pba_assign_psb_to_vsb(PBACtx *C, int psb, PBAList *vsbs, int k, int isWrite) {
    int gi = pba_gi(C, k);
    if (isWrite) C->wbar[gi] = psb; else C->rbar[gi] = psb;
    pal_push(&C->psbProd[psb], k);
    int tp = pba_tepid(C, k, !isWrite);
    if (tp > C->psbTepid[psb]) C->psbTepid[psb] = tp;
    if (isWrite) C->psbWrProt[psb] = 1;
    if (C->DoDepBar && isWrite && psb == C->llsb) {

        const PBInst *ip = pba_ip(C, k);
        for (int t = 0; t < PB_NTOK; t++) {
            if (C->depCnt[t] > 0) C->depCnt[t]++;
            if (C->depOther[t] > 0) C->depOther[t]++;
        }
        for (int t = 0; t < ip->n_defs; t++) {
            int r = ip->defs[t];
            if (r < 0 || r >= PB_NTOK) continue;
            int oldCount = C->depCnt[r], oldPred = C->depPred[r];
            C->depPred[r] = (signed char)pba_pred_kind(ip);
            C->depCnt[r] = 1;
            if (oldCount > 0 && oldPred != C->depPred[r]) C->depOther[r] = oldCount;
        }
        if (C->dbBeforeIp >= 0) C->dbLLAfter++;
    }
    for (int i = 0; i < vsbs->n; i++) {
        PBAVsb *V = &C->v[vsbs->v[i]];
        if (V->uses.n == 0) pba_require_psb(C, psb, PBA_DUMMY);
        else for (int z = 0; z < V->uses.n; z++) pba_require_psb(C, psb, V->uses.v[z]);
    }
}

static int pba_depbar_cnt_gi(PBACtx *C, int gi, int reg) {
    int cnt = C->depCnt[reg];
    if (cnt > 0) {
        const PBInst *ip = &C->insts[gi];
        if (ip->is_pred && pba_is_compl(pba_pred_kind(ip), C->depPred[reg]))
            cnt = C->depOther[reg];
    }
    return cnt - 1;
}
static int pba_depbar_cnt(PBACtx *C, int k, int reg) { return pba_depbar_cnt_gi(C, pba_gi(C, k), reg); }
static void pba_require_llsb(PBACtx *C, int k) { pba_set_req(C, k, C->llsb); }
static int  pba_consumes_llsb(PBACtx *C, int k) { return (pba_get_req(C, k) >> C->llsb) & 1; }
static int  pba_consumes_llsb_gi(PBACtx *C, int gi) { return (C->req[gi] >> C->llsb) & 1; }

static void pba_require_if_consume_llsb_gi(PBACtx *C, int gi) {
    if (pba_consumes_llsb_gi(C, gi)) return;
    const PBInst *ip = &C->insts[gi];
    for (int t = 0; t < ip->n_defs; t++) {
        int r = ip->defs[t];
        if (r < 0 || r >= PB_NTOK) continue;
        if (pba_depbar_cnt_gi(C, gi, r) >= 0 && !ip->high_cost_sb) {
            C->req[gi] |= (u8)(1 << C->llsb); return; }
    }
    for (int t = 0; t < ip->n_suses; t++) {
        int r = ip->suses[t];
        if (r < 0 || r >= PB_NTOK) continue;
        if (pba_depbar_cnt_gi(C, gi, r) >= 0) { C->req[gi] |= (u8)(1 << C->llsb); return; }
    }
}
static void pba_require_if_consume_llsb(PBACtx *C, int k) { pba_require_if_consume_llsb_gi(C, pba_gi(C, k)); }

static int pba_find_smallest_depbar_cnt(PBACtx *C, int k) {
    const PBInst *ip = pba_ip(C, k);
    int best = -1, seen = 0;
    for (int t = 0; t < ip->n_defs; t++) {
        int r = ip->defs[t]; if (r < 0 || r >= PB_NTOK) continue;
        int c = pba_depbar_cnt(C, k, r);
        if (c != -1) { if (!seen || best > c) { best = c; seen = 1; } }
    }
    for (int t = 0; t < ip->n_suses; t++) {
        int r = ip->suses[t]; if (r < 0 || r >= PB_NTOK) continue;
        int c = pba_depbar_cnt(C, k, r);
        if (c != -1) { if (!seen || best > c) { best = c; seen = 1; } }
    }
    return seen ? best : -1;
}
static void pba_reduce_depbar_cnt(PBACtx *C, int cnt) {
    for (int t = 0; t < PB_NTOK; t++) {
        if (cnt == 0) { C->depCnt[t] = 0; C->depOther[t] = 0; C->depPred[t] = 0; continue; }
        if (C->depCnt[t] > cnt) C->depCnt[t] = 0;
        if (C->depOther[t] > cnt) C->depOther[t] = 0;
    }
}

static void pba_db_req_prev(PBACtx *C);
static void pba_db_init(PBACtx *C) { C->dbLeCnt = 0; C->dbLLAfter = 0; C->dbDist = 0; C->dbBeforeIp = -1; C->dbConsumer = -1; }
static void pba_db_set(PBACtx *C, int cnt, int k) { pba_db_init(C); C->dbLeCnt = cnt; C->dbBeforeIp = k; C->dbConsumer = k; }
static int  pba_db_profitable(PBACtx *C) { return C->dbDist >= 10; }

static int pba_db_next_real(PBACtx *C) {
    while (C->dbRealNext < C->bbend && C->insts[C->dbRealNext].op != OP_Depbar)
        C->dbRealNext++;
    return C->dbRealNext < C->bbend ? C->dbRealNext : -1;
}

static int pba_db_prod_or_cons_ll(PBACtx *C, int k) {
    int gi = pba_gi(C, k);
    if (C->wbar[gi] == C->llsb) return 1;
    if ((C->req[gi] >> C->llsb) & 1) return 1;
    return 0;
}

#define PBA_DB_PROFITABLE_DIST 10
static int pba_db_better_ip(PBACtx *C, int k) {
    int p = k;
    while (p >= 0 && !pba_db_prod_or_cons_ll(C, p)) {
        p--;
        if (p < 0) break;
        if (pba_tav(C, k) - pba_tav(C, p) > PBA_DB_PROFITABLE_DIST) break;
        if (pba_ip(C, p)->coupled != PBC_DECOUPLED) return p + 1;
    }
    return k;
}
static void pba_db_gen_prev(PBACtx *C) {
    int d   = pba_db_next_real(C);
    int lim = (C->dbBeforeIp >= 0) ? pba_gi(C, C->dbBeforeIp) : C->bbend;
    if (d < 0 || d >= lim) {

        _pb_dbreal_hits++;

        if (_inkv_dbrec_arm && C->dbBeforeIp >= 0 && C->dbLeCnt > 0) {
            int ins = pba_gi(C, pba_db_better_ip(C, C->dbBeforeIp));
            if (ins >= _inkv_dbrec_lo && ins <= _inkv_dbrec_hi) {
                if (_inkv_dbreq_n < INKV_DBREQ_MAX) {
                    _inkv_dbreq[_inkv_dbreq_n].pos = ins;
                    _inkv_dbreq[_inkv_dbreq_n].sb  = (u8)C->llsb;
                    _inkv_dbreq[_inkv_dbreq_n].cnt = (u8)(C->dbLeCnt > 63 ? 63 : C->dbLeCnt);
                    _inkv_dbreq_n++;
                } else _inkv_dbreq_over = 1;
            }
        }
        pba_db_req_prev(C);
        return;
    }
    C->dbRealNext = d + 1;
    if (C->nDbGen < 128) C->dbGenCons[C->nDbGen++] = C->dbConsumer;
    pba_db_init(C);
}
static void pba_db_req_prev(PBACtx *C) {
    if (C->dbBeforeIp >= 0) pba_require_llsb(C, C->dbBeforeIp);
    pba_db_init(C);
}
static void pba_db_merge(PBACtx *C, int cnt) {
    C->dbLeCnt = cnt - C->dbLLAfter;
    if (C->dbLeCnt == 0) pba_db_req_prev(C);
}
static void pba_db_insert_profitable(PBACtx *C, int cnt, int k) {
    if (C->dbBeforeIp < 0) {
        if (cnt == 0) pba_require_llsb(C, k);
        else pba_db_set(C, cnt, k);
        return;
    }
    if (cnt == 0) {
        if (C->dbLLAfter == 0 && !pba_db_profitable(C)) { pba_db_merge(C, cnt); C->dbConsumer = k; }
        else { pba_db_gen_prev(C); pba_require_llsb(C, k); }
        return;
    }
    if (cnt < C->dbLLAfter) { pba_db_gen_prev(C); pba_db_set(C, cnt, k); return; }
    if (!pba_db_profitable(C)) { pba_db_merge(C, cnt); C->dbConsumer = k; return; }
    pba_db_gen_prev(C); pba_db_set(C, cnt, k);
}

static void pba_release_required_psb(PBACtx *C, int k) {
    int r = pba_get_req(C, k);
    for (int ii = C->firstSB; ii < PBA_NSB; ii++) {
        if (!((r >> ii) & 1)) continue;
        pba_release_psb(C, ii);
        pal_clear(&C->psbProd[ii]);
        if (C->knobs & 8) pba_clear_lvin(C, ii);
    }
}
static int pba_require_if_consume_lvin_gi(PBACtx *C, int gi, int psb) {
    const PBInst *ip = &C->insts[gi];
    for (int t = 0; t < ip->n_defs; t++) {
        int r = ip->defs[t]; if (r < 0 || r >= PB_NTOK) continue;
        if ((C->regLvInRd[r] & (1 << psb)) || (C->regLvInWr[r] & (1 << psb))) {
            C->req[gi] |= (u8)(1 << psb); pba_clear_lvin(C, psb); return 1;
        }
    }
    for (int t = 0; t < ip->n_suses; t++) {
        int r = ip->suses[t]; if (r < 0 || r >= PB_NTOK) continue;
        if (C->regLvInWr[r] & (1 << psb)) {
            C->req[gi] |= (u8)(1 << psb); pba_clear_lvin(C, psb); return 1;
        }
    }
    return 0;
}
static int pba_require_if_consume_lvin(PBACtx *C, int k, int psb) {
    return pba_require_if_consume_lvin_gi(C, pba_gi(C, k), psb);
}

static void pba_process_lab(PBACtx *C, int bi, PBACfgBB *cfg) {
    if (!(C->knobs & 8)) {
        if (C->DoDepBar)
            for (int t = 0; t < PB_NTOK; t++) { C->depCnt[t] = 0; C->depOther[t] = 0; C->depPred[t] = 0; }
        return;
    }
    for (int t = 0; t < PB_NTOK; t++) { C->depCnt[t] = 0; C->depOther[t] = 0; C->depPred[t] = 0; }
    if (C->DoDepBar && (C->knobs & 4)) {
        for (int r = 0; r < PB_NTOK; r++) {
            if (!C->liveRegLlsb[(size_t)bi * PB_NTOK + r]) continue;
            int cnt = 0;
            for (int z = 0; z < cfg[bi].pred.n; z++) {
                int p = cfg[bi].pred.v[z];
                int d = C->lvOutDep[(size_t)p * PB_NTOK + r];
                if (cnt == 0) cnt = d;
                else if (d > 0 && d < cnt) cnt = d;
            }
            if (cnt > 0) {
                int selfLoop = (cfg[bi].loopHdr == bi && cfg[bi].loopRegion == bi);
                C->depCnt[r] = (cfg[bi].loopHdr == bi && !selfLoop) ? 1 : cnt;
            }
        }
    }
    for (int i = 0; i < PBA_NSB; i++) {
        C->lvinUsed[i] = 0;
        memset(C->lvinRd[i], 0, PB_NTOK); memset(C->lvinWr[i], 0, PB_NTOK);
    }
    memset(C->regLvInRd, 0, sizeof(C->regLvInRd));
    memset(C->regLvInWr, 0, sizeof(C->regLvInWr));
    for (int psb = C->firstSB; psb <= C->lastNonLLSb; psb++)
        for (int z = 0; z < cfg[bi].pred.n; z++) {
            int p = cfg[bi].pred.v[z];
            for (int r = 0; r < PB_NTOK; r++) {
                if (!C->liveRegPsb[(size_t)bi * PB_NTOK + r]) continue;
                if (C->lvOutRd[(size_t)p * PB_NTOK + r] & (1 << psb)) {
                    C->regLvInRd[r] |= 1 << psb; C->lvinUsed[psb] = 1; C->lvinRd[psb][r] = 1;
                }
                if (C->lvOutWr[(size_t)p * PB_NTOK + r] & (1 << psb)) {
                    C->regLvInWr[r] |= 1 << psb; C->lvinUsed[psb] = 1; C->lvinWr[psb][r] = 1;
                }
            }
        }
}

static void pba_assign_psb(PBACtx *C, int bi, int nbb, PBACfgBB *cfg) {
    int n = C->nloc;
    for (int i = 0; i < PBA_NSB; i++) {
        C->psbNo[i] = -1; C->psbHasInst[i] = 0; C->psbTepid[i] = 0;
        C->psbWrProt[i] = 0; pal_clear(&C->psbProd[i]);
    }
    pba_db_init(C);
    C->nDbGen = 0;
    C->dbRealNext = C->bbstart;

    for (int k = 0; k < n; k++) {
        const PBInst *ip = pba_ip(C, k);
        pba_release_required_psb(C, k);

        if (C->DoDepBar && (C->knobs & 4)) {
            C->dbDist = 0;
            if (C->dbBeforeIp >= 0) C->dbDist = pba_tav(C, k) - pba_tav(C, C->dbBeforeIp);
            pba_require_if_consume_llsb(C, k);
            if (pba_consumes_llsb(C, k)) {
                pba_clr_req(C, k, C->llsb);
                int cnt = pba_find_smallest_depbar_cnt(C, k);
                if (cnt == -1) cnt = 0;
                pba_db_insert_profitable(C, cnt, k);
                pba_reduce_depbar_cnt(C, cnt);
            }
        }
        if ((C->knobs & 8) && C->DoCrossBlock) {
            for (int ii = C->firstSB; ii <= C->lastNonLLSb; ii++) {
                if (pba_require_if_consume_lvin(C, k, ii)) {
                    if (C->psbHasInst[ii]) pba_unset_consume(C, ii, C->psbNo[ii]);
                    else if (C->psbNo[ii] != -1) pba_release_psb(C, ii);
                    pal_clear(&C->psbProd[ii]);
                }
            }
        }

        if (C->ird[k].n) {
            int psb = pba_heuristic(C, k, &C->ird[k], 0);
            pba_assign_psb_to_vsb(C, psb, &C->ird[k], k, 0);
        }
        if (C->iwr[k].n) {
            int psb = pba_heuristic(C, k, &C->iwr[k], 1);
            pba_assign_psb_to_vsb(C, psb, &C->iwr[k], k, 1);
        }
        if (C->knobs & 8) {
            int gi = pba_gi(C, k);
            if (C->wbar[gi] >= 0 && bi > C->blockIndexLastPsb[C->wbar[gi]])
                C->blockIndexLastPsb[C->wbar[gi]] = bi;
            if (C->rbar[gi] >= 0 && bi > C->blockIndexLastPsb[C->rbar[gi]])
                C->blockIndexLastPsb[C->rbar[gi]] = bi;
        }
        (void)ip;
    }
}

static int pba_can_track_cross_block(PBACtx *C, int bi, PBACfgBB *cfg) {
    if (cfg[bi].unknown) return 0;
    if (cfg[bi].succ.n == 0) return 0;

    for (int z = 0; z < cfg[bi].succ.n; z++) {
        int s = cfg[bi].succ.v[z];
        if (s <= bi) {
            if (!(bi == cfg[bi].loopRegion && s == cfg[bi].loopHdr && cfg[s].pred.n == 2))
                return 0;
        }
    }
    const PBInst *last = &C->insts[C->bbend - 1];
    if (last->op == OP_Cal || last->op == OP_Jcal) return 0;

    if (last->op == OP_Ret && (!(_pb_retc & 4) || last->is_pred)) return 0;
    return 1;
}
static int pba_live_psb_mask(PBACtx *C) {
    int m = 0;
    for (int ii = C->firstSB; ii <= C->lastNonLLSb; ii++) if (!pba_psb_available(C, ii)) m |= 1 << ii;
    return m;
}
static int pba_live_llsb_mask(PBACtx *C) {
    if (!C->DoDepBar || !(C->knobs & 4)) return 0;
    for (int t = 0; t < PB_NTOK; t++) if (C->depCnt[t] > 0) return 1 << C->llsb;
    return 0;
}
static int pba_psb_from_llnondepbar(PBACtx *C, int psb) { (void)C; (void)psb; return 0; }
static int pba_finish_psb_mask(PBACtx *C, int lastK, int liveMask) {
    int m = 0;
    for (int psb = 0; psb <= 5; psb++)
        if ((liveMask & (1 << psb)) && C->psbNo[psb] != -1 &&
            C->psbTepid[psb] <= pba_tav(C, lastK) && !pba_psb_from_llnondepbar(C, psb))
            m |= 1 << psb;
    return m;
}

static void pba_req_across_backedge(PBACtx *C, int bi, const PBBlock *bbs,
                                    PBACfgBB *cfg, int livePsbMask) {
    if (!livePsbMask) return;
    int hdr = cfg[bi].loopHdr;
    if (hdr < 0) return;
    int selfLoop = (cfg[bi].loopHdr == bi && cfg[bi].loopRegion == bi);

    pba_process_lab(C, hdr, cfg);

    char Removed[PBA_NSB];
    for (int ii = 0; ii < PBA_NSB; ii++)
        Removed[ii] = (char)(C->blockIndexLastPsb[ii] < hdr);

    for (int gi = bbs[hdr].start; gi < bbs[hdr].end; gi++) {
        const PBInst *ip = &C->insts[gi];
        int rdSb = C->rbar[gi], wrSb = C->wbar[gi];
        for (int ii = 0; ii < PBA_NSB; ii++) {
            if (!(livePsbMask & (1 << ii)) || Removed[ii]) continue;
            if (C->req[gi] & (1 << ii)) { Removed[ii] = 1; continue; }
            if (rdSb == ii || wrSb == ii) {
                C->req[gi] |= (u8)(1 << ii); Removed[ii] = 1; continue;
            }
            if (ip->op == OP_Depbar) {
                int dsb = pb_depbar_sb(ip->q), dcnt = pb_depbar_thr(ip->q);
                if (dcnt > 0 && dsb == ii && selfLoop) { Removed[ii] = 1; continue; }
                if (dsb == ii) { Removed[ii] = 1; continue; }
            }
            if (C->DoDepBar && (C->knobs & 4) && ii == C->llsb) {
                if (!selfLoop) {
                    pba_require_if_consume_llsb_gi(C, gi);
                    if (pba_consumes_llsb_gi(C, gi)) { Removed[ii] = 1; continue; }
                } else { Removed[ii] = 1; continue; }
            } else {
                if (pba_require_if_consume_lvin_gi(C, gi, ii)) { Removed[ii] = 1; continue; }
            }
        }
    }
    int remaining = 0;
    for (int ii = 0; ii < PBA_NSB; ii++)
        if ((livePsbMask & (1 << ii)) && !Removed[ii]) remaining |= 1 << ii;
    if (remaining && !selfLoop) {
        int gl = bbs[hdr].end - 1;
        const PBInst *lip = &C->insts[gl];

        if (!(((lip->op == OP_Exit) || ((_pb_retc & 4) && lip->op == OP_Ret)) &&
              (lip->pred_reg == 7 || (_pb_retc & 2))))
            C->req[gl] |= (u8)remaining;
    }
}

static void pba_require_at_last_ip(PBACtx *C, int lastK, int mask) {
    const PBInst *ip = pba_ip(C, lastK);

    if (((ip->op == OP_Exit) || ((_pb_retc & 4) && ip->op == OP_Ret)) &&
        (ip->pred_reg == 7 || (_pb_retc & 1))) return;
    for (int ii = 0; ii < PBA_NSB; ii++) if (mask & (1 << ii)) pba_set_req(C, lastK, ii);
}

static void pb_assign_adv_pass(const PBInst *insts, int n, const PBBlock *bbs, int nbb,
                               PBACfgBB *cfg, int has_ll, const int *tav, PBSBResult *out) {
    PBACtx Cs; PBACtx *C = &Cs;
    memset(C, 0, sizeof(*C));
    C->knobs = _pb_sb_knobs;
    C->insts = insts;
    C->tav = tav;
    C->wbar = out->wbar; C->rbar = out->rbar; C->req = out->wait;
    C->dbConsumerOf = _pb_dbcons;
    _pb_dbc_mismatch = 0;
    if (_pb_dbcons) for (int i = 0; i < n; i++) _pb_dbcons[i] = -1;
    for (int i = 0; i < n; i++) { out->wbar[i] = -1; out->rbar[i] = -1; out->wait[i] = 0; }

    C->DoDepBar = has_ll;
    C->LLsbDesignated = has_ll;
    C->DoCrossBlock = 1;
    C->DoAcrossBackedge = 1;
    C->DoReqCommit = (C->knobs & 0x200) ? 1 : 0;
    C->firstSB = 0;
    C->llsb = 5;
    C->lastNonLLSb = C->LLsbDesignated ? 4 : 5;
    C->lastSB = C->lastNonLLSb;
    C->firstLlsbPsb = 2;
    C->psbReassignStallLimit = 100;
    C->nglob = n;

    int maxbn = 1;
    for (int bi = 0; bi < nbb; bi++) if (bbs[bi].end - bbs[bi].start > maxbn) maxbn = bbs[bi].end - bbs[bi].start;
    C->ird = (PBAList *)calloc(maxbn, sizeof(PBAList));
    C->iwr = (PBAList *)calloc(maxbn, sizeof(PBAList));
    C->ireq = (PBAList *)calloc(maxbn, sizeof(PBAList));
    C->loc = (int *)calloc(maxbn, sizeof(int));
    for (int i = 0; i < maxbn; i++) { pal_init(&C->ird[i]); pal_init(&C->iwr[i]); pal_init(&C->ireq[i]); }
    for (int r = 0; r < PB_NTOK; r++) { pal_init(&C->rdOf[r]); pal_init(&C->wrOf[r]); }
    for (int i = 0; i < PBA_OVQ_COUNT * 2; i++) pal_init(&C->q[i]);
    for (int i = 0; i < PBA_NSB; i++) {
        pal_init(&C->psbProd[i]);
        C->lvinRd[i] = (u8 *)calloc(PB_NTOK, 1);
        C->lvinWr[i] = (u8 *)calloc(PB_NTOK, 1);
    }
    C->lvOutRd = (u8 *)calloc((size_t)nbb * PB_NTOK, 1);
    C->lvOutWr = (u8 *)calloc((size_t)nbb * PB_NTOK, 1);
    C->lvOutDep = (int *)calloc((size_t)nbb * PB_NTOK, sizeof(int));
    C->liveRegLlsb = (u8 *)calloc((size_t)nbb * PB_NTOK, 1);
    C->liveRegPsb  = (u8 *)calloc((size_t)nbb * PB_NTOK, 1);

    for (int bi = 0; bi < nbb; bi++) {
        int s = bbs[bi].start, e = bbs[bi].end;
        C->bbstart = s; C->bbend = e;
        C->nloc = 0;
        for (int gi = s; gi < e; gi++) {
            if ((C->knobs & 0x40) && insts[gi].op == OP_Depbar) continue;
            C->loc[C->nloc++] = gi;
        }
        if (C->nloc == 0) continue;

        pba_assign_vsb(C);

        pba_process_lab(C, bi, cfg);

        if (_pb_sb_dbg > 1) {
            int lv = 0; for (int p = 0; p < PBA_NSB; p++) if (C->lvinUsed[p]) lv |= 1 << p;
            printf("LAB  %d lvin=%02x", bi, lv);
            for (int p = 0; p < PBA_NSB; p++) if (C->lvinUsed[p]) {
                printf("  psb%d{rd:", p);
                for (int r = 0; r < PB_NTOK; r++) if (C->lvinRd[p][r]) printf(" %d", r);
                printf(" wr:");
                for (int r = 0; r < PB_NTOK; r++) if (C->lvinWr[p][r]) printf(" %d", r);
                printf("}");
            }
            printf("\n");
        }

        pba_assign_psb(C, bi, nbb, cfg);

        if (C->knobs & 0x10) {
            int lastK = C->nloc - 1;
            int liveNonLL = pba_live_psb_mask(C);
            int liveLL = pba_live_llsb_mask(C);
            int liveMask = liveNonLL | liveLL;
            int reqMask = 0;
            int canTrack = pba_can_track_cross_block(C, bi, cfg);
            if (_pb_sb_dbg > 1)
                printf("ENDBB %d live=%02x(nonLL %02x) canTrack=%d finish=%02x tavLast=%d psbTepid=%d,%d,%d,%d,%d\n",
                       bi, liveMask, liveNonLL, canTrack,
                       C->DoReqCommit ? pba_finish_psb_mask(C, lastK, liveNonLL) : 0,
                       pba_tav(C, lastK), C->psbTepid[0], C->psbTepid[1], C->psbTepid[2],
                       C->psbTepid[3], C->psbTepid[4]);
            if (C->DoCrossBlock) {
                int finishMask = 0;
                if (C->DoReqCommit) finishMask |= pba_finish_psb_mask(C, lastK, liveNonLL);
                if (canTrack) {

                    if (C->DoDepBar && (C->knobs & 4)) {
                        for (int r = 0; r < PB_NTOK; r++) if (C->depCnt[r] > 0) {
                            for (int z = 0; z < cfg[bi].succ.n; z++)
                                C->liveRegLlsb[(size_t)cfg[bi].succ.v[z] * PB_NTOK + r] = 1;
                            C->lvOutDep[(size_t)bi * PB_NTOK + r] = C->depCnt[r];
                        }
                    }
                    for (int psb = C->firstSB; psb <= C->lastNonLLSb; psb++) {
                        if (finishMask & (1 << psb)) continue;
                        if ((C->knobs & 8) && C->lvinUsed[psb]) {
                            for (int r = 0; r < PB_NTOK; r++) {
                                if (C->lvinRd[psb][r]) {
                                    C->lvOutRd[(size_t)bi * PB_NTOK + r] |= (u8)(1 << psb);
                                    for (int z = 0; z < cfg[bi].succ.n; z++)
                                        C->liveRegPsb[(size_t)cfg[bi].succ.v[z] * PB_NTOK + r] = 1;
                                }
                                if (C->lvinWr[psb][r]) {
                                    C->lvOutWr[(size_t)bi * PB_NTOK + r] |= (u8)(1 << psb);
                                    for (int z = 0; z < cfg[bi].succ.n; z++)
                                        C->liveRegPsb[(size_t)cfg[bi].succ.v[z] * PB_NTOK + r] = 1;
                                }
                            }
                        }
                        if (C->psbNo[psb] == -1) continue;
                        for (int z = 0; z < C->psbProd[psb].n; z++) {
                            int pk = C->psbProd[psb].v[z];
                            int gi = pba_gi(C, pk);
                            const PBInst *pip = &insts[gi];
                            if (C->rbar[gi] == psb) {
                                for (int t = 0; t < pip->n_suses; t++) {
                                    int r = pip->suses[t];
                                    if (r < 0 || r >= 255) continue;
                                    C->lvOutRd[(size_t)bi * PB_NTOK + r] |= (u8)(1 << psb);
                                    for (int y = 0; y < cfg[bi].succ.n; y++)
                                        C->liveRegPsb[(size_t)cfg[bi].succ.v[y] * PB_NTOK + r] = 1;
                                }
                            }
                            if (C->wbar[gi] == psb) {
                                for (int t = 0; t < pip->n_defs; t++) {
                                    int r = pip->defs[t];
                                    if (r < 0 || r >= PB_NTOK) continue;
                                    C->lvOutWr[(size_t)bi * PB_NTOK + r] |= (u8)(1 << psb);
                                    for (int y = 0; y < cfg[bi].succ.n; y++)
                                        C->liveRegPsb[(size_t)cfg[bi].succ.v[y] * PB_NTOK + r] = 1;
                                }
                            }
                        }
                    }
                    if (bi == cfg[bi].loopRegion && C->DoAcrossBackedge) {
                        if (C->knobs & 0x80)
                            pba_req_across_backedge(C, bi, bbs, cfg, liveMask & ~finishMask);

                    }
                    reqMask = finishMask;
                } else {
                    pba_require_at_last_ip(C, lastK, liveMask);
                    reqMask = 0;
                    liveMask = 0;
                }
            } else {
                reqMask = liveMask;
            }
            if (liveMask && reqMask && C->nloc > 0) {
                const PBInst *lip = pba_ip(C, lastK);

                int nonExitRet = (_pb_retc & 4) ? (lip->op == OP_Ret && lip->is_pred)
                                                : (lip->op == OP_Ret);
                int succLoopHdr = 0;
                for (int z = 0; z < cfg[bi].succ.n; z++)
                    if (cfg[cfg[bi].succ.v[z]].loopHdr == cfg[bi].succ.v[z]) { succLoopHdr = 1; break; }
                if (C->DoCrossBlock && !succLoopHdr && !nonExitRet) {
                    for (int z = 0; z < cfg[bi].succ.n; z++) {
                        int sb2 = cfg[bi].succ.v[z];
                        int fs = bbs[sb2].start;
                        if (fs < bbs[sb2].end)
                            for (int ii = 0; ii < PBA_NSB; ii++)
                                if (reqMask & (1 << ii)) out->wait[fs] |= (u8)(1 << ii);
                    }
                } else {
                    pba_require_at_last_ip(C, lastK, reqMask);
                }
            }
        }

        if (C->DoDepBar && (C->knobs & 4) && C->dbBeforeIp >= 0) {
            if (C->DoCrossBlock) pba_db_gen_prev(C);
            else if (pba_db_profitable(C)) pba_db_gen_prev(C);
            else pba_db_req_prev(C);
        }

        if (C->dbConsumerOf) {
            int g = 0;
            for (int gi = s; gi < e; gi++) {
                if (insts[gi].op != OP_Depbar) continue;
                if (_pb_dbc_ppoa && pb_is_ppoa_depbar(insts[gi].op, insts[gi].q)) {
                    C->dbConsumerOf[gi] = -1;
                    continue;
                }
                if (g < C->nDbGen) {
                    int ck = C->dbGenCons[g];
                    C->dbConsumerOf[gi] = (ck >= 0 && ck < C->nloc) ? C->loc[ck] : -1;
                } else { C->dbConsumerOf[gi] = -1; _pb_dbc_mismatch++; }
                g++;
            }
            if (g != C->nDbGen) _pb_dbc_mismatch++;
        }
    }

    for (int i = 0; i < maxbn; i++) { pal_free(&C->ird[i]); pal_free(&C->iwr[i]); pal_free(&C->ireq[i]); }
    free(C->ird); free(C->iwr); free(C->ireq); free(C->loc);
    for (int r = 0; r < PB_NTOK; r++) { pal_free(&C->rdOf[r]); pal_free(&C->wrOf[r]); }
    for (int i = 0; i < PBA_OVQ_COUNT * 2; i++) pal_free(&C->q[i]);
    for (int i = 0; i < PBA_NSB; i++) { pal_free(&C->psbProd[i]); free(C->lvinRd[i]); free(C->lvinWr[i]); }
    for (int i = 1; i <= C->nvmax; i++) pal_free(&C->v[i].uses);
    free(C->v);
    free(C->lvOutRd); free(C->lvOutWr); free(C->lvOutDep);
    free(C->liveRegLlsb); free(C->liveRegPsb);
}

static void pb_assign_adv(const PBInst *insts, int n, const PBBlock *bbs, int nbb,
                          int has_ll, PBSBResult *out) {
    free(_pb_dbcons);
    _pb_dbcons = (int *)malloc((n ? n : 1) * sizeof(int));
    for (int i = 0; i < n; i++) _pb_dbcons[i] = -1;
    PBACfgBB *cfg = (PBACfgBB *)calloc(nbb ? nbb : 1, sizeof(PBACfgBB));
    pba_build_cfg(insts, n, bbs, nbb, cfg);
    if (_pb_sb_dbg) {
        for (int bi = 0; bi < nbb; bi++) {
            printf("cfg bb%-3d [%d,%d) last=%s unk=%d hdr=%d rgn=%d succ={",
                   bi, bbs[bi].start, bbs[bi].end,
                   SM50_NAME[insts[bbs[bi].end-1].op], cfg[bi].unknown,
                   cfg[bi].loopHdr, cfg[bi].loopRegion);
            for (int z = 0; z < cfg[bi].succ.n; z++) printf("%d,", cfg[bi].succ.v[z]);
            printf("} pred={");
            for (int z = 0; z < cfg[bi].pred.n; z++) printf("%d,", cfg[bi].pred.v[z]);
            printf("}\n");
        }
    }

    pb_assign_adv_pass(insts, n, bbs, nbb, cfg, has_ll, NULL, out);
    if (!(_pb_sb_knobs & 0x400)) {
        for (int bi = 0; bi < nbb; bi++) { pal_free(&cfg[bi].succ); pal_free(&cfg[bi].pred); }
        free(cfg); return;
    }

    int *tav = (int *)calloc(n ? n : 1, sizeof(int));
    int *pw = (int *)malloc((n ? n : 1) * sizeof(int));
    int *pr = (int *)malloc((n ? n : 1) * sizeof(int));
    u8  *pq = (u8 *)malloc(n ? n : 1);
    for (int pass = 1; pass < _pb_sb_passes; pass++) {
        memcpy(pw, out->wbar, n * sizeof(int));
        memcpy(pr, out->rbar, n * sizeof(int));
        memcpy(pq, out->wait, n);
        for (int bi = 0; bi < nbb; bi++) {
            int s = bbs[bi].start, e = bbs[bi].end, bn = e - s;
            if (bn <= 0) continue;
            PBSBResult r;
            r.wbar = out->wbar + s; r.rbar = out->rbar + s; r.wait = out->wait + s;
            u8 *pf = (u8 *)calloc(bn, 1);

            int save_pm = _pb_pair_mode;
            if (_pb_tav_mode & 32) _pb_pair_mode = 1;
            pb_pair_flags(&insts[s], bn, &r, pf);
            _pb_pair_mode = save_pm;
            int save_gt = _pb_gt_base; _pb_gt_base = -1;
            _pb_blk_base = s;

            _pb_phaseA = (_pb_sb_knobs & 0x800) ? 1 : 0;
            pb_replay_tav(&insts[s], bn, &r, pf, tav + s, NULL, NULL);
            _pb_phaseA = 0;
            _pb_gt_base = save_gt;
            free(pf);
        }

        if ((_pb_sb_knobs & 0x100) && _pb_gt)
            for (int i = 0; i < n && i < _pb_gt_n; i++) tav[i] = _pb_gt[i].tav;

        if (_pb_sbd_use && _pb_sbd)
            for (int i = 0; i < n && i < _pb_sbd_n; i++) tav[i] = _pb_sbd[i].tav;
        pb_assign_adv_pass(insts, n, bbs, nbb, cfg, has_ll, tav, out);
        if (!memcmp(pw, out->wbar, n * sizeof(int)) &&
            !memcmp(pr, out->rbar, n * sizeof(int)) &&
            !memcmp(pq, out->wait, n))
            break;
    }
    free(tav); free(pw); free(pr); free(pq);
    if (_pb_sb_dbg) printf("depbar-consumer map mismatches: %d\n", _pb_dbc_mismatch);

    for (int bi = 0; bi < nbb; bi++) { pal_free(&cfg[bi].succ); pal_free(&cfg[bi].pred); }
    free(cfg);
}

typedef struct { int time; u8 coupled; int lat; u8 ccp; } PBCompInfo;

static void pb_exposed_avail(const PBInst *block, int n, const int *T,
                             const PBSBResult *res, const u8 *pair,
                             int *tav, int *dct_arr) {
    PBCompInfo *comp = (PBCompInfo *)calloc(PB_NTOK, sizeof(PBCompInfo));
    int sb_ll[6]; memset(sb_ll, 0, sizeof(sb_ll));
    int sb_comp[6]; memset(sb_comp, 0, sizeof(sb_comp));
    int sb_pend[6]; memset(sb_pend, 0, sizeof(sb_pend));
    int depbar_ct = 0, running_max = 0;

    for (int i = 0; i < n; i++) {
        const PBInst *ip = &block[i];
        int sb_bump = 0;
        if (res->wait[i]) {
            for (int s = 0; s < 6; s++) {
                if (!((res->wait[i] >> s) & 1)) continue;
                if (sb_ll[s]) { if (sb_comp[s] > depbar_ct) depbar_ct = sb_comp[s];
                                 if (sb_comp[s] > sb_bump) sb_bump = sb_comp[s]; }
                sb_ll[s] = 0; sb_comp[s] = 0; sb_pend[s] = 0;
            }
        }
        if (ip->op == OP_Depbar) {
            int sb = pb_depbar_sb(ip->q), thr = pb_depbar_thr(ip->q);
            int old = sb_pend[sb]; sb_pend[sb] = sb_pend[sb] < thr ? sb_pend[sb] : thr;
            if (sb_ll[sb] && old > thr) {
                if (sb_comp[sb] > depbar_ct) depbar_ct = sb_comp[sb];
                if (sb_comp[sb] > sb_bump) sb_bump = sb_comp[sb];
            }
        }
        dct_arr[i] = depbar_ct;
        int ta = T[i]; if (sb_bump > ta) ta = sb_bump;
        int is_dec = ip->coupled == PBC_DECOUPLED;
        int is_texu = ip->vq == PBVQ_TEX || ip->vq == PBVQ_XU;
        for (int k = 0; k < ip->n_uses; k++) {
            int r = ip->uses[k]; if (r >= PB_NTOK) continue;
            PBCompInfo *ci = &comp[r];
            if (ci->time == 0 && ci->coupled == 0 && ci->lat == 0) continue;
            int ct = ci->time;
            if (is_dec && ci->coupled != PBC_DECOUPLED && !ci->ccp) {
                int reduced;
                if (ci->coupled == PBC_COUPLED)
                    reduced = is_texu ? 2 : 4;
                else
                    reduced = is_texu ? 4 : 6;
                ct = ct - ci->lat + reduced;
            }
            if (ct > ta) ta = ct;
        }
        if (ta > running_max) running_max = ta;
        tav[i] = running_max;
        if (_pb_gt_inject & 1) {
            const PBGt *g = pb_gt_at(i);
            if (g) { tav[i] = g->tav; running_max = g->tav; }
        }
        if (!pair[i]) running_max++;
        int lat = pb_base_latency(ip);
        if (!lat) lat = 6;
        int writes_ccp = ip->defs_ccp;
        for (int k = 0; k < ip->n_defs; k++) {
            int r = ip->defs[k]; if (r >= PB_NTOK) continue;
            comp[r].time = tav[i] + lat;
            comp[r].coupled = ip->coupled;
            comp[r].lat = lat;
            comp[r].ccp = (u8)writes_ccp;
        }
        if (res->wbar[i] >= 0) {
            int sb = res->wbar[i];
            sb_ll[sb] = sb_ll[sb] || ip->is_longlat;
            sb_pend[sb]++;
            int wl = pb_base_latency(ip); if (!wl) wl = 6;
            int sc = tav[i] + wl; if (sc > sb_comp[sb]) sb_comp[sb] = sc;
        }
    }
    free(comp);
}

#define PB_OPX_DRAIN 0
#define PB_OPX_PAIR 16
#define PB_OPX_PIXBAR 28
#define PB_OPX_ODY6 29
#define PB_OPX_ODY8 30
#define PB_OPX_OFFDECK 31
#define PB_MAX_GRP 5
#define PB_SHORT_STALL 7

static int pb_is_flowctrl(int op) {
    return op==OP_Bra||op==OP_Brk||op==OP_Sync||op==OP_Cal||op==OP_Jcal||
           op==OP_Ret||op==OP_Sam||op==OP_Membar||op==OP_Cont||op==OP_Exit||
           op==OP_Brx||op==OP_Jmp||op==OP_Jmx;
}

static int pb_use_group(int is_dec_prop, int wait, int n_since) {
    if (wait > 11) return 1;
    if (is_dec_prop) return 0;
    return n_since >= PB_MAX_GRP;
}

static int pb_wait_or_pair(int is_dec_prop, int wait, int n_since) {
    if (wait == 0) return PB_OPX_PAIR;
    if (!pb_use_group(is_dec_prop, wait, n_since))
        return PB_OPX_PAIR + wait;
    if (wait < 15) return wait;
    return 15;
}

static int pb_min_issue(int op) {
    if (op == OP_Depbar) return 3;
    if (op == OP_Bar || op == OP_Kil) return 5;
    if (pb_is_flowctrl(op)) return 5;
    if (op == OP_Sam) return 2;
    return 0;
}

static void pb_max_wait_time(const PBInst *block, int n, const int *T, int *mwt) {
    mwt[0] = 0;
    for (int i = 0; i < n; i++) {
        mwt[i+1] = mwt[i];
        if (block[i].coupled != PBC_DECOUPLED) {
            int lat = pb_base_latency(&block[i]); if (!lat) lat = 6;
            if (block[i].defs_ccp) { lat += 7; if (lat > 15) lat = 15; }
            int v = T[i] + lat; if (v > mwt[i+1]) mwt[i+1] = v;
        } else {
            int v = T[i] + PB_SB_RAW_DELAY; if (v > mwt[i+1]) mwt[i+1] = v;
        }
    }
}

static u32 *pb_opex_encode(const PBInst *block, int n, const PBSBResult *res,
                           const int *T, u8 *pair, const u8 *is_pad, int *wtav_out) {
    int *tav = (int *)calloc(n, sizeof(int));
    int *dct = (int *)calloc(n, sizeof(int));
    int *mwt_arr = (int *)calloc(n + 1, sizeof(int));

    if (_pb_gt_inject & 32) {
        for (int i = 0; i < n; i++) {
            const PBGt *g = pb_gt_at(i);
            if (g && g->has_v2) {
                ((PBSBResult *)res)->wait[i] = (u8)g->reqsb;
                ((PBSBResult *)res)->wbar[i] = g->wsb;
                ((PBSBResult *)res)->rbar[i] = g->rsb;
            }
        }
    }
    pb_exposed_avail(block, n, T, res, pair, tav, dct);

    u8 *pairM = pair;
    if ((_pb_tav_mode & 32) && _pb_pair_mode == 0) {
        pairM = (u8 *)calloc(n, 1);
        _pb_pair_mode = 1;
        pb_pair_flags(block, n, res, pairM);
        _pb_pair_mode = 0;
    }

    int ne = n;
    if (is_pad) { for (int i = 0; i < n; i++) if (is_pad[i]) { ne = i; break; } }
    int *opex_new = (int *)calloc(n > 0 ? n : 1, sizeof(int));
    PBOpexReq OReq; memset(&OReq, 0, sizeof OReq);
    OReq.ne = (_pb_opex_mode & 3) ? ne : 0;
    OReq.opex = opex_new;
    OReq.wtav_out = wtav_out;
    if (_pb_dbg_wtav) {
        OReq.s_wtav = _pb_dbg_wtav; OReq.s_opex = _pb_dbg_opex0;
        OReq.s_nsg  = _pb_dbg_nsg;  OReq.s_mccpi= _pb_dbg_mccpi;
        OReq.s_wt   = _pb_dbg_wt;   OReq.s_mccp = _pb_dbg_mccp;
        OReq.s_mwt  = _pb_dbg_mwt2; OReq.s_nbod = _pb_dbg_nbod;
        OReq.s_reqll = _pb_dbg_reqll; OReq.s_reqpred = _pb_dbg_reqpred;
    }
    if (_pb_reqll_p) { OReq.in_reqll = _pb_reqll_p; OReq.in_reqpred = _pb_reqpred_p; }
    if (_pb_tav_mode) pb_replay_tav(block, n, res, pairM, tav,
                                    (_pb_tav_mode & 2) ? dct : NULL, &OReq);

    if (_pb_texph) {
        PBInst *mblock = (PBInst *)block;
        int priorTex = -1;
        for (int i = 0; i < n; i++) {
            if (!pb_is_tex_batch_op(block[i].op)) continue;
            mblock[i].tex_phase = 2;
            if (priorTex >= 0 && tav[priorTex] + 50 > tav[i]) mblock[priorTex].tex_phase = 1;
            priorTex = i;
        }
    }
    if (pairM != pair) free(pairM);
    pb_max_wait_time(block, n, T, mwt_arr);
    if (_pb_gt_inject & 2)
        for (int i = 0; i < n; i++) { const PBGt *g = pb_gt_at(i); if (g) dct[i] = g->dct; }
    if (_pb_gt_inject & 4)
        for (int i = 0; i < n; i++) { const PBGt *g = pb_gt_at(i); if (g) mwt_arr[i+1] = g->mwt; }

    u32 *out = (u32 *)calloc(n, sizeof(u32));
    int cc_until = -1, n_since = 0, since_offdeck = 0;
    int prior_od_idx = -1;
    int pod_stall = 0, pod_dec = 0, pod_ns = 0, pod_w2 = 0;

    u8 *req_ll = (u8 *)calloc(n, 1);
    u8 *req_pred_sb = (u8 *)calloc(n, 1);
    { int llsb[6]={0}, llp[6]={0}, predsb[6]={0};
      for (int i = 0; i < n; i++) {
          for (int s=0;s<6;s++) {
              if ((res->wait[i]>>s)&1) {
                  if (llsb[s]) req_ll[i]=1;
                  if (predsb[s]) req_pred_sb[i]=1;
                  llsb[s]=0; predsb[s]=0;
              }
          }
          if (block[i].op == OP_Depbar) {
              int sb=pb_depbar_sb(block[i].q);
              if (llp[sb]) req_ll[i]=1;
          }
          if (res->wbar[i]>=0) {
              if (block[i].is_longlat) { llsb[res->wbar[i]]=1; llp[res->wbar[i]]=1; }
              else llp[res->wbar[i]]=0;
              if (block[i].is_pred) predsb[res->wbar[i]]=1;
          }
      }
    }

    if (_pb_opex_mode & 1) {

        for (int i = 0; i < n; i++) {
            if (is_pad && is_pad[i]) { out[i] = 0; continue; }
            int opex = opex_new[i];
            if (_pb_dbg_tav) {
                _pb_dbg_tav[i]=tav[i]; _pb_dbg_dct[i]=dct[i]; _pb_dbg_T[i]=T[i];
                _pb_dbg_stall[i]=opex & 0xF; _pb_dbg_opex[i]=opex;
                _pb_dbg_mwt[i]=mwt_arr[i+1]; _pb_dbg_ns[i]=0;
            }
            int st = opex & 0xF, yld = (opex >> 4) & 1;
            int wb = res->wbar[i] >= 0 ? res->wbar[i] : 7;
            int rb = res->rbar[i] >= 0 ? res->rbar[i] : 7;
            out[i] = (u32)((st&0xF)|((yld&1)<<4)|((wb&7)<<5)|((rb&7)<<8)|
                           ((res->wait[i]&0x3F)<<11));
        }
        free(tav); free(dct); free(mwt_arr); free(req_ll); free(req_pred_sb);
        free(opex_new);
        return out;
    }

    for (int i = 0; i < n; i++) {
        const PBInst *ip = &block[i];
        if (is_pad && is_pad[i]) { out[i] = 0; continue; }
        if (_pb_gt_inject & 8) { const PBGt *g = pb_gt_at(i); if (g) n_since = g->nsg; }
        if (_pb_dbg_tav) {
            _pb_dbg_tav[i]=tav[i]; _pb_dbg_dct[i]=dct[i]; _pb_dbg_mwt[i]=mwt_arr[i+1];
            _pb_dbg_ns[i]=n_since; _pb_dbg_T[i]=T[i];
        }
        int is_dec = ip->coupled == PBC_DECOUPLED || res->rbar[i] >= 0;
        int is_dec_prop = ip->coupled == PBC_DECOUPLED;
        int stall;
        if (_pb_tav_mode & 8) {

            if (i == n - 1) { stall = mwt_arr[i] - tav[i]; if (stall < 0) stall = 0; }
            else stall = tav[i+1] - tav[i];
        } else if (i == n - 1) { stall = mwt_arr[i] - T[i]; if (stall < 0) stall = 0; }
        else stall = T[i+1] - T[i];
        int mi = pb_min_issue(ip->op);
        if (mi > stall) stall = mi;
        if (stall < 0) stall = 0; if (stall > 15) stall = 15;

        int my_tav = tav[i]; if (dct[i] > my_tav) my_tav = dct[i];
        int cc_stall = cc_until > my_tav ? cc_until - my_tav : 0;
        int cc_busy = cc_until > my_tav;
        int thr;
        if (since_offdeck >= 48) thr = 3;
        else if (since_offdeck >= 32) thr = 3;
        else if (since_offdeck >= 12) thr = 5;
        else thr = PB_SHORT_STALL;

        int is_flow = pb_is_flowctrl(ip->op);
        int next_exit = (i+1 < n) && (block[i+1].op == OP_Exit || block[i+1].op == OP_Ret);
        int opex;

        if ((ip->op == OP_Exit || ip->op == OP_Ret || ip->op == OP_Bar) && !ip->is_pred) {
            opex = PB_OPX_OFFDECK;
        } else if (ip->op == OP_Bra && n == 1) {
            opex = PB_OPX_OFFDECK;
        } else if (is_flow || next_exit) {
            if (next_exit && pair[i] && stall == 0)
                opex = pb_wait_or_pair(is_dec_prop, 0, n_since);
            else {
                int fc_wait = mwt_arr[i] - T[i]; if (fc_wait < 0) fc_wait = 0;
                int wait = fc_wait; if (mi > wait) wait = mi; if (wait < 1) wait = 1;
                if (wait > 15) wait = 15;
                int fc_cc_ok = !cc_busy || cc_stall <= 7;
                if (is_flow && wait <= 8 && fc_cc_ok)
                    opex = wait <= 6 ? PB_OPX_ODY6 : PB_OPX_ODY8;
                else
                    opex = pb_wait_or_pair(is_dec_prop, wait, n_since);
            }
        } else {
            int exposed = stall;
            if (i+1<n && tav[i+1]-my_tav > exposed) exposed = tav[i+1]-my_tav;
            if (i+1<n && ip->coupled == PBC_DECOUPLED) {
                int has_dd = 0;
                for (int a=0; a<ip->n_defs && !has_dd; a++) {
                    int r=ip->defs[a]; if(r>=255) continue;
                    for (int b=0; b<block[i+1].n_uses && !has_dd; b++)
                        if (block[i+1].uses[b]==r) has_dd=1;
                }
                if (has_dd) { int dl=pb_base_latency(ip); if(!dl) dl=6; if(dl>exposed) exposed=dl; }
            }
            int next_pred = (i+1<n) && (block[i+1].is_pred || req_pred_sb[i+1]);
            int next_ll = (i+1<n) && req_ll[i+1];

            if (next_ll) {
                since_offdeck = 0;
                int ll_wait = stall; if (cc_stall > ll_wait) ll_wait = cc_stall;
                cc_until -= cc_stall;
                opex = pb_wait_or_pair(is_dec_prop, ll_wait, n_since);
            } else if (exposed > cc_stall && !next_pred) {
                int wait2 = exposed - cc_stall;
                if (wait2 <= thr)
                    opex = pb_wait_or_pair(is_dec_prop, stall, n_since);
                else if (wait2 <= 15 && stall <= 6) opex = PB_OPX_ODY6;
                else if (wait2 < 15 && stall <= 8) opex = PB_OPX_ODY8;
                else if (wait2 >= 15) opex = PB_OPX_OFFDECK;
                else opex = pb_wait_or_pair(is_dec_prop, stall, n_since);
            } else {
                opex = pb_wait_or_pair(is_dec_prop, stall, n_since);
            }
        }

        if ((opex==PB_OPX_ODY6||opex==PB_OPX_ODY8||opex==PB_OPX_OFFDECK) && i > 0 &&
            !(is_pad && is_pad[i-1])) {
            int cwy_cc = cc_until > my_tav ? cc_until - my_tav : 0;
            if (cwy_cc > 0 && !ip->defs_ccp) {
                u32 prev = out[i-1];
                int p_opx = prev & 0x1F;
                if (p_opx != PB_OPX_PIXBAR && p_opx != PB_OPX_ODY6 &&
                    p_opx != PB_OPX_ODY8 && p_opx != PB_OPX_OFFDECK) {
                    int p_my = tav[i-1]; if (dct[i-1]>p_my) p_my=dct[i-1];
                    int td = my_tav - p_my;
                    int p_st = prev & 0xF;
                    int ns2 = td + cwy_cc; if (ns2 < p_st) ns2 = p_st; if (ns2 < 0) ns2 = 0; if (ns2 > 15) ns2 = 15;
                    if (ns2 > p_st) {
                        int is_prev_group = (1 <= (p_opx&0x1F) && (p_opx&0x1F) <= 15);
                        int ng = is_prev_group || ns2 > 11;
                        int ny = ng ? 0 : 1;
                        int wb_p = (prev>>5)&7, rb_p=(prev>>8)&7, wt_p=(prev>>11)&0x3F;
                        out[i-1] = (u32)((ns2&0xF)|((ny&1)<<4)|((wb_p&7)<<5)|((rb_p&7)<<8)|((wt_p&0x3F)<<11));
                        cc_until -= cwy_cc;
                    }
                }
            }
        }

        if (opex==PB_OPX_ODY6||opex==PB_OPX_ODY8||opex==PB_OPX_OFFDECK) {
            if (prior_od_idx >= 0 && since_offdeck <= 6 && prior_od_idx != i) {
                u32 prev_c = out[prior_od_idx];
                int p_opx = prev_c & 0x1F;
                if (p_opx==PB_OPX_ODY6||p_opx==PB_OPX_ODY8||p_opx==PB_OPX_OFFDECK) {
                    if (pod_w2 <= PB_SHORT_STALL) {
                        int new_opex = pb_wait_or_pair(pod_dec, pod_stall, pod_ns);
                        int ns2 = new_opex & 0xF, ny = (new_opex>>4)&1;
                        int wb_p=(prev_c>>5)&7, rb_p=(prev_c>>8)&7, wt_p=(prev_c>>11)&0x3F;
                        out[prior_od_idx] = (u32)((ns2&0xF)|((ny&1)<<4)|((wb_p&7)<<5)|((rb_p&7)<<8)|((wt_p&0x3F)<<11));
                    }
                }
            }
        }

        if (opex==PB_OPX_DRAIN||opex==PB_OPX_PIXBAR||opex==PB_OPX_ODY6||
            opex==PB_OPX_ODY8||opex==PB_OPX_OFFDECK) {
            if (opex==PB_OPX_ODY6||opex==PB_OPX_ODY8||opex==PB_OPX_OFFDECK) {
                prior_od_idx = i;
                int _exposed = stall;
                if (i+1<n && tav[i+1]-my_tav>_exposed) _exposed=tav[i+1]-my_tav;
                int _od_w2 = (!is_flow && !next_exit && ip->op!=OP_Exit &&
                              ip->op!=OP_Ret && ip->op!=OP_Bar) ? _exposed-cc_stall : 999;
                pod_stall=stall; pod_dec=is_dec_prop; pod_ns=n_since; pod_w2=_od_w2;
            }
            since_offdeck = 0;
        }
        if (opex != PB_OPX_PAIR && since_offdeck < (1<<30)) since_offdeck++;
        if (opex >= 17 && opex <= 27) n_since++;
        else if (opex >= 1 && opex <= 11) n_since = 0;

        if (_pb_dbg_tav) { _pb_dbg_stall[i]=stall; _pb_dbg_opex[i]=opex; }
        int st = opex & 0xF, yld = (opex >> 4) & 1;
        int wb = res->wbar[i] >= 0 ? res->wbar[i] : 7;
        int rb = res->rbar[i] >= 0 ? res->rbar[i] : 7;
        out[i] = (u32)((st&0xF)|((yld&1)<<4)|((wb&7)<<5)|((rb&7)<<8)|((res->wait[i]&0x3F)<<11));

        for (int k = 0; k < ip->n_defs; k++) {
            int d = ip->defs[k];
            if (d == PB_CC || (d >= 300 && d <= 306)) {
                int lat2 = pb_base_latency(ip); if (!lat2) lat2 = 6;
                lat2 += 7; if (lat2 > 15) lat2 = 15;
                int v = tav[i] + lat2;
                if (v > cc_until) cc_until = v;
            }
        }
    }

    free(tav); free(dct); free(mwt_arr); free(req_ll); free(req_pred_sb); free(opex_new);
    return out;
}

static int pb_is_tex_batch_op(int op) {
    return op==OP_Tex||op==OP_Texs||op==OP_Tld||op==OP_Tlds||op==OP_Tld4||
           op==OP_Tld4s||op==OP_Tmml||op==OP_Txq||op==OP_Txd||op==OP_Txa||
           op==OP_TexB||op==OP_TldB||op==OP_Tld4B||op==OP_TxdB||op==OP_TxqB||
           op==OP_TmmlB||op==OP_TexsF16||op==OP_TldsF16||op==OP_Tld4sF16;
}

static void pb_apply_offdeck(u32 *out, int idx, const PBSBResult *res) {
    u32 c = out[idx];
    int wb=(c>>5)&7, rb=(c>>8)&7, wt=(c>>11)&0x3F;
    out[idx] = (u32)(15|(1<<4)|((wb&7)<<5)|((rb&7)<<8)|((wt&0x3F)<<11));
}

static void pb_ppoa_opex(const PBInst *block, int n, u32 *out) {
    for (int d = 1; d < n; d++) {
        if (!pb_is_ppoa_depbar(block[d].op, block[d].q)) continue;
        const PBInst *p = &block[d-1];
        if (p->coupled == PBC_DECOUPLED || !p->defs_ccp) continue;
        u32 keep_p = out[d-1], keep_d = out[d];
        int newp = PB_OPX_DRAIN + pbo_ccorp_lat(p);
        out[d-1] = (keep_p & ~0x1Fu) | (u32)(newp & 0x1F);
        out[d]   = (keep_d & ~0x1Fu) | (u32)PB_OPX_OFFDECK;
    }
}

static void pb_tex_batch_offdeck(const PBInst *block, int n, const PBSBResult *res,
                                 u32 *out, const int *T, const u8 *is_pad) {

    u8 *batch_end = (u8 *)calloc(n, 1);
    int has_be = 0;
    for (int k = 0; k < n; k++) {
        if (is_pad && is_pad[k]) continue;
        if (pb_is_tex_batch_op(block[k].op) && block[k].tex_phase == 2) {
            batch_end[k] = 1; has_be = 1;
        }
    }
    if (!has_be) { free(batch_end); return; }

    int ll_active[6]; memset(ll_active, 0, sizeof(ll_active));
    for (int i = 0; i < n; i++) {
        if (res->wait[i]) for (int s=0;s<6;s++) if ((res->wait[i]>>s)&1) ll_active[s]=0;
        if (res->wbar[i]>=0 && block[i].is_longlat) ll_active[res->wbar[i]]=1;
        if (!batch_end[i]) continue;
        int cur_opex = out[i] & 0x1F;
        if (cur_opex==PB_OPX_ODY6||cur_opex==PB_OPX_ODY8||cur_opex==PB_OPX_OFFDECK||cur_opex==PB_OPX_DRAIN) {
            pb_apply_offdeck(out, i, res); continue;
        }
        int place_at = i, num_inst = 0;
        int ll_scan[6]; memcpy(ll_scan, ll_active, sizeof(ll_scan));
        int ccp_time = 0;
        int outstanding_ccp = 0;
        for (int j = i+1; j < n; j++) {
            if (is_pad && is_pad[j]) break;

            if (_pb_odord) { if (outstanding_ccp) { num_inst = 7; break; } }
            const PBInst *jip = &block[j];
            if (jip->coupled != PBC_DECOUPLED && jip->defs_ccp) {
                int jl = pb_base_latency(jip); if(!jl) jl=6; jl+=7; if(jl>15) jl=15;
                int v=T[j]+jl; if(v>ccp_time) ccp_time=v;
            }
            if (_pb_odord) outstanding_ccp = (ccp_time > T[j]);
            else if (ccp_time > T[j]) { num_inst = 7; break; }
            int rll = 0;
            if (res->wait[j]) for (int s=0;s<6;s++) if ((res->wait[j]>>s)&1 && ll_scan[s]) { rll=1; break; }
            if (!rll && jip->op==OP_Depbar) { for (int s=0;s<6;s++) if (ll_scan[s]) { rll=1; break; } }
            if (rll) { place_at = -1; break; }
            num_inst++;
            if (num_inst > 6) break;

            if (j + 1 < n && pb_is_ppoa_depbar(block[j+1].op, block[j+1].q)) {
                num_inst++; place_at = j; break;
            }
            int j_opex = out[j] & 0x1F;
            if (j_opex==PB_OPX_ODY6||j_opex==PB_OPX_ODY8||j_opex==PB_OPX_OFFDECK||j_opex==PB_OPX_DRAIN) {
                num_inst++; place_at=j; break;
            }
            if (res->wait[j]) { num_inst++; place_at=j-1>i?j-1:i; break; }
        }
        if (place_at < 0) continue;
        if (num_inst <= 6 && place_at != i) pb_apply_offdeck(out, place_at, res);
        else pb_apply_offdeck(out, i, res);
    }
    free(batch_end);
}

#define PB_NUM_COLL 2
#define PB_INV -1

static void pb_lane_regs(const PBInst *ip, int *out) {
    out[0] = out[1] = out[2] = PB_INV;
    if (ip->coupled == PBC_DECOUPLED) return;
    int nm = ip->op;

    int t0=0,t1=0,t2=0;
    if (nm==OP_Fadd||nm==OP_Fadd32i||nm==OP_Dadd||nm==OP_Fswzadd) { t0=1; t2=2; }
    else if (nm==OP_Fmul||nm==OP_Fmul32i||nm==OP_Imul||nm==OP_Imul32i) { t0=1; t1=2; }
    else if (nm==OP_Ffma||nm==OP_Ffma32i) { t0=1; t1=2; t2=3; }
    else if (nm==OP_Fmnmx||nm==OP_Imnmx||nm==OP_Dmnmx) { t0=1; t1=2; }
    else if (nm==OP_Mov||nm==OP_F2f||nm==OP_F2i||nm==OP_I2f||nm==OP_I2i||nm==OP_Rro) { t1=1; }
    else if (nm==OP_Iadd||nm==OP_Iadd32i) { t0=1; t1=2; }
    else if (nm==OP_Lop||nm==OP_Lop32i||nm==OP_Shl||nm==OP_Shr) { t0=1; t1=2; }
    else if (nm==OP_Shf) { t0=1; t1=3; t2=2; }
    else if (nm==OP_Bfe) { t0=1; t1=2; }
    else if (nm==OP_Bfi) { t0=1; t1=2; t2=3; }
    else if (nm==OP_Lop3||nm==OP_Prmt) { t0=1; t1=2; t2=3; }
    else if (nm==OP_Isetp||nm==OP_Fsetp||nm==OP_Dsetp) { t0=2; t1=3; }
    else if (nm==OP_Iset||nm==OP_Fset) { t0=1; t1=2; }
    else if (nm==OP_Sel) { t0=1; t1=2; }
    else if (nm==OP_Icmp||nm==OP_Fcmp) { t0=2; t1=3; t2=1; }
    else if (nm==OP_Xmad) { t0=2; t1=3; t2=4; }
    else if (nm==OP_Iadd3) { t0=3; t1=4; t2=5; }
    else if (nm==OP_Lea||nm==OP_LeaHi) { t0=1; t1=2; }
    else if (nm==OP_Iscadd||nm==OP_Iscadd32i) { t0=1; t1=2; }
    else return;

    int goffs[8], ngf = gpr_fields(ip->q, goffs);

    int opds[8]; memset(opds, 0xFF, sizeof(opds));
    if (ngf > 1) opds[1] = (ip->q >> goffs[1]) & 0xFF;
    if (ngf > 2) opds[2] = (ip->q >> goffs[2]) & 0xFF;
    if (ngf > 3) opds[3] = (ip->q >> goffs[3]) & 0xFF;

    if (nm==OP_Isetp||nm==OP_Fsetp||nm==OP_Dsetp) {
        opds[2] = _ra(ip->q); opds[3] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
    }

    if (nm==OP_Icmp||nm==OP_Fcmp) {
        opds[1] = _rc(ip->q); opds[2] = _ra(ip->q);
        opds[3] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
    }

    if (nm==OP_Xmad) {
        opds[2] = _ra(ip->q); opds[3] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
        opds[4] = _rc(ip->q);
    }

    if (nm==OP_Iadd3) {
        opds[3] = _ra(ip->q); opds[4] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
        opds[5] = _rc(ip->q);
    }

    if (nm==OP_Lop3||nm==OP_Prmt||nm==OP_Bfi||nm==OP_Shf) {
        opds[1] = _ra(ip->q);
        opds[2] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
        opds[3] = _rc(ip->q);
    }

    if (nm==OP_Ffma) {

        opds[1] = _ra(ip->q);
        if (((ip->q >> 61) & 7) == 1) {
            opds[2] = 255; opds[3] = _rc(ip->q);
        } else if (!((ip->q >> 60) & 1)) {
            opds[2] = 255; opds[3] = _rc(ip->q);
        } else if (!((ip->q >> 59) & 1)) {
            opds[2] = _rc(ip->q); opds[3] = 255;
        } else {
            opds[2] = _rb(ip->q); opds[3] = _rc(ip->q);
        }
    }

    if (nm==OP_Ffma32i||nm==OP_Imad32i) {
        opds[1] = _ra(ip->q);
        opds[2] = 255;
        opds[3] = _rc(ip->q);
    }

    if (nm==OP_Fadd||nm==OP_Fmul||
        nm==OP_Fmnmx||nm==OP_Imnmx||nm==OP_Dmnmx||nm==OP_Iadd||
        nm==OP_Lop||nm==OP_Shl||nm==OP_Shr||nm==OP_Bfe||
        nm==OP_Iset||nm==OP_Fset||nm==OP_Sel||nm==OP_Lea||nm==OP_LeaHi||
        nm==OP_Iscadd||nm==OP_Imul||
        nm==OP_Dadd||nm==OP_Fswzadd) {
        opds[1] = _ra(ip->q);
        opds[2] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
    }

    if (nm==OP_Fadd32i||nm==OP_Fmul32i||nm==OP_Iadd32i||nm==OP_Lop32i||
        nm==OP_Iscadd32i||nm==OP_Imul32i) {
        opds[1] = _ra(ip->q);
        opds[2] = 255;
    }

    if (nm==OP_Mov) { opds[1] = nm_is(ip->q, OP_Mov) ? _rb(ip->q) : _ra(ip->q); }
    if (nm==OP_F2f||nm==OP_F2i||nm==OP_I2f||nm==OP_I2i||nm==OP_Rro) {
        opds[1] = srcb_form(ip->q)==FORM_REG ? _rb(ip->q) : 255;
    }

    #define LR(lane, opd_idx) do { \
        if ((opd_idx) && opds[opd_idx] != 255 && opds[opd_idx] < 255) out[lane] = opds[opd_idx]; \
    } while(0)
    LR(0, t0); LR(1, t1); LR(2, t2);
    #undef LR

    for (int lane = 0; lane < 3; lane++) {
        if (out[lane] == PB_INV) continue;
        int found = 0;
        for (int k = 0; k < ip->n_uses; k++)
            if (ip->uses[k] == out[lane]) { found = 1; break; }
        if (!found) out[lane] = PB_INV;
    }
}

static int pb_stops_reuse(const PBInst *ip, int opex, int prohibit) {

    if (prohibit) return 1;
    if (ip->op == OP_Exit || ip->op == OP_Ret) return 1;
    if ((opex >= 1 && opex <= 15) || opex == 0 || opex >= 28) return 1;
    return 0;
}

static void pb_compute_reuse(const PBInst *block, int n, const u32 *ctrl, const int *tissue, u8 *rmask,
                             const u8 *prohibit) {
    int *rreg_avail = (int *)calloc(256, sizeof(int));
    memset(rmask, 0, n);

    int (*lane_r)[3]   = (int(*)[3])malloc((n ? n : 1) * 3 * sizeof(int));
    int (*next_use)[3] = (int(*)[3])malloc((n ? n : 1) * 3 * sizeof(int));
    u8  (*reuse_set)[3] = (u8(*)[3])malloc((n ? n : 1) * 3);
    int (*mr_val)[256]  = (int(*)[256])malloc(3 * 256 * sizeof(int));
    unsigned (*mr_st)[256] = (unsigned(*)[256])malloc(3 * 256 * sizeof(unsigned));
    unsigned mr_gen = 0;
    if (!rreg_avail || !lane_r || !next_use || !reuse_set || !mr_val || !mr_st) {
        free(rreg_avail); free(lane_r); free(next_use);
        free(reuse_set); free(mr_val); free(mr_st);
        return;
    }
    memset(mr_st, 0, 3 * 256 * sizeof(unsigned));
    #define MR_GET(l_, r_) (mr_st[l_][r_] == mr_gen ? mr_val[l_][r_] : -1)
    #define MR_SET(l_, r_, v_) do { mr_st[l_][r_] = mr_gen; mr_val[l_][r_] = (v_); } while (0)
    int i = 0;
    while (i < n) {

        int j = i;
        while (j < n) {
            int opex = ctrl[j] & 0x1F;
            if (pb_stops_reuse(&block[j], opex, prohibit ? prohibit[j] : 0)) break;
            j++;
        }
        if (j >= n) j = n - 1;
        int glen = j - i + 1;

        mr_gen++;
        for (int ki = 0; ki < glen; ki++) {
            int k = i + ki;
            pb_lane_regs(&block[k], lane_r[ki]);
            next_use[ki][0] = next_use[ki][1] = next_use[ki][2] = PB_INV;
            int cf = block[k].coupled != PBC_DECOUPLED;
            int wta = tissue ? tissue[k] : 0;
            if (cf) {
                for (int lane = 0; lane < 3; lane++) {
                    int r = lane_r[ki][lane];
                    if (r == PB_INV) continue;
                    if (tissue && rreg_avail[r] > wta) continue;
                    int prev = MR_GET(lane, r);
                    if (prev >= 0) next_use[prev - i][lane] = k;
                    MR_SET(lane, r, k);
                }
            }

            int op_lat = cf ? (_pb_reuselat ? block[k].lat_full : 0) : 1;
            if (cf && block[k].coupled != PBC_COUPLED && !_pb_reuselat)
                op_lat = block[k].latency;
            for (int d = 0; d < block[k].n_defs; d++) {
                int r = block[k].defs[d]; if (r >= 255) continue;
                int v = wta + op_lat; if (v > rreg_avail[r]) rreg_avail[r] = v;
                for (int lane = 0; lane < 3; lane++) MR_SET(lane, r, -1);
            }
        }

        int coll[3][2][3];
        memset(coll, 0xFF, sizeof(coll));
        memset(reuse_set, 0, (size_t)glen * 3);

        for (int ki = 0; ki < glen; ki++) {
            int k = i + ki;
            if (block[k].coupled == PBC_DECOUPLED) continue;
            for (int lane = 0; lane < 3; lane++) {
                int r = lane_r[ki][lane];
                if (r == PB_INV) continue;
                int my_nui = next_use[ki][lane];
                int slot = -1;
                for (int s = 0; s < PB_NUM_COLL; s++)
                    if (coll[lane][s][0] == r) { slot = s; break; }
                if (slot >= 0) {
                    if (my_nui == PB_INV) { coll[lane][slot][0] = PB_INV; continue; }
                } else if (my_nui == PB_INV) { continue; }
                else {
                    int all_full = (coll[lane][0][0] != PB_INV && coll[lane][1][0] != PB_INV);
                    if (all_full) {
                        int far_s = coll[lane][0][1] >= coll[lane][1][1] ? 0 : 1;
                        if (coll[lane][far_s][1] < my_nui) continue;
                        int evk = coll[lane][far_s][2];
                        if (evk >= i && evk <= j) reuse_set[evk - i][lane] = 0;
                        slot = far_s;
                    } else {
                        slot = coll[lane][0][0] == PB_INV ? 0 : 1;
                    }
                }
                coll[lane][slot][0] = r; coll[lane][slot][1] = my_nui; coll[lane][slot][2] = k;
                reuse_set[ki][lane] = 1;
            }
        }
        for (int ki = 0; ki < glen; ki++) {
            int k = i + ki;

            if (block[k].tex_phase) { rmask[k] = block[k].tex_phase; continue; }
            int mask = 0;
            for (int lane = 0; lane < 3; lane++)
                if (reuse_set[ki][lane]) mask |= (1 << lane);
            rmask[k] = (u8)mask;
        }
        i = j + 1;
    }
    #undef MR_GET
    #undef MR_SET
    free(rreg_avail); free(lane_r); free(next_use);
    free(reuse_set); free(mr_val); free(mr_st);
}

static u32 *pb_schedule_program(const u8 *bc, u32 constOff, int *n_out) {
    int n;
    PBInst *insts = pb_build(bc, constOff, &n);
    *n_out = n;
    if (n == 0) { free(insts); return (u32 *)calloc(1, sizeof(u32)); }

    u8 *pad = (u8 *)calloc(n, 1);
    for (int i = n - 1; i >= 0; i--) {
        if (insts[i].q == 0 || insts[i].op == OP_Nop) pad[i] = 1; else break;
    }
    int pad_start = n;
    for (int i = 0; i < n; i++) { if (pad[i]) { pad_start = i; break; } }
    int real_bundles = (pad_start + 2) / 3;
    int total_bundles = (n + 2) / 3;
    int pad_bundles = total_bundles - real_bundles;
    int last_real_slot = pad_start > 0 ? (pad_start - 1) % 3 : 2;
    int last_bundle_has_pad = last_real_slot < 2;
    int extra = (pad_bundles == 1 || last_bundle_has_pad) ? 1 : 0;
    int n_written = real_bundles + extra;
    u32 EMPTY_CTRL = 0x7e0;

    int has_ll = pb_has_lldepbar(insts, n);
    int nbb;
    PBBlock *bbs = pb_basic_blocks(insts, n, &nbb);

    u32 *result = (u32 *)calloc(n, sizeof(u32));

    PBSBResult sball = pb_sb_alloc(n);
    pb_assign_all(insts, n, bbs, nbb, has_ll, &sball);

    u8 *ppoa_succ = (u8 *)calloc(n ? n : 1, 1);
    for (int i = 0; i + 1 < n; i++)
        if (pb_is_ppoa_depbar(insts[i].op, insts[i].q)) {
            if (_pb_ppoareq) ppoa_succ[i + 1] = (u8)pb_depbar_req(insts[i].q);
            else sball.wait[i + 1] &= (u8)~pb_depbar_req(insts[i].q);
        }

    u8 *reqll_all = (u8 *)calloc(n, 1), *reqpred_all = (u8 *)calloc(n, 1);
    pbo_calc_req_flags(insts, n, &sball, reqll_all, reqpred_all);

    u8 *prohib = (u8 *)calloc(n, 1);
    if (_pb_prohreuse)
        for (int bi = 0; bi < nbb; bi++)
            pb_calc_prohibit_reuse(insts + bbs[bi].start,
                                   bbs[bi].end - bbs[bi].start,
                                   prohib + bbs[bi].start);

    for (int bi = 0; bi < nbb; bi++) {
        int s = bbs[bi].start, e = bbs[bi].end;
        int bn = e - s;
        PBInst *block = &insts[s];
        _pb_reqll_p = _pb_reqglob ? reqll_all + s : NULL;
        _pb_reqpred_p = _pb_reqglob ? reqpred_all + s : NULL;
        _pb_gt_base = _pb_gt ? s : -1;
        _pb_blk_base = s;
        if (_pb_dbgp_tav) {
            _pb_dbg_tav=_pb_dbgp_tav+s; _pb_dbg_dct=_pb_dbgp_dct+s;
            _pb_dbg_mwt=_pb_dbgp_mwt+s; _pb_dbg_ns=_pb_dbgp_ns+s;
            _pb_dbg_stall=_pb_dbgp_stall+s; _pb_dbg_opex=_pb_dbgp_opex+s;
            _pb_dbg_T=_pb_dbgp_T+s;
            _pb_dbg_wtav=_pb_dbgp_wtav+s; _pb_dbg_opex0=_pb_dbgp_opex0+s;
            _pb_dbg_nsg=_pb_dbgp_nsg+s;   _pb_dbg_mccpi=_pb_dbgp_mccpi+s;
            _pb_dbg_wt=_pb_dbgp_wt+s;     _pb_dbg_mccp=_pb_dbgp_mccp+s;
            _pb_dbg_mwt2=_pb_dbgp_mwt2+s; _pb_dbg_nbod=_pb_dbgp_nbod+s;
            _pb_dbg_reqll=_pb_dbgp_reqll+s; _pb_dbg_reqpred=_pb_dbgp_reqpred+s;
            for (int k=0;k<bn;k++) _pb_dbgp_bb[s+k]=bi;
        }

        PBSBResult sbres;
        sbres.wbar = sball.wbar + s; sbres.rbar = sball.rbar + s; sbres.wait = sball.wait + s;

        u8 *pair_f = (u8 *)calloc(bn, 1);
        pb_pair_flags(block, bn, &sbres, pair_f);

        int *Tvals = (int *)calloc(bn, sizeof(int));
        int *od = (int *)calloc(bn, sizeof(int));
        pb_forward_times(block, bn, &sbres, pair_f, Tvals, od);

        int *wtavb = (int *)calloc(bn, sizeof(int));
        u32 *ctrl = pb_opex_encode(block, bn, &sbres, Tvals, pair_f, pad + s, wtavb);
        pb_tex_batch_offdeck(block, bn, &sbres, ctrl, Tvals, pad + s);
        pb_ppoa_opex(block, bn, ctrl);

        u8 *rmask = (u8 *)calloc(bn, 1);
        pb_compute_reuse(block, bn, ctrl, (_pb_opex_mode & 4) ? wtavb : Tvals, rmask,
                         _pb_prohreuse ? prohib + s : NULL);

        for (int k = 0; k < bn; k++) {
            int gi = s + k;
            if (pad[gi]) {

                if (_pb_padrule) result[gi] = insts[gi].q ? EMPTY_CTRL : 0;
                else { int bundle_idx = gi / 3;
                       result[gi] = bundle_idx < n_written ? EMPTY_CTRL : 0; }
            } else {
                u32 w = ctrl[k] | (((u32)rmask[k] & 0xF) << 17);

                if (ppoa_succ[gi]) w &= ~(((u32)ppoa_succ[gi] & 0x3F) << 11);
                result[gi] = w;
            }
        }

        free(pair_f); free(Tvals); free(od); free(ctrl); free(rmask); free(wtavb);
    }
    _pb_reqll_p = _pb_reqpred_p = NULL;
    free(reqll_all); free(reqpred_all); free(prohib);

    pb_sb_free(&sball);
    free(ppoa_succ);
    free(pad); free(bbs); free(insts);
    free(_pb_dbcons); _pb_dbcons = NULL;
    return result;
}

#ifndef INKV_LIB

#define PBV_INF 0x7FFFFFFF
#define PBV_RAW 0
#define PBV_WAW 1
#define PBV_WAR 2
static const char *const pbv_kind_name[3] = { "RAW", "WAW", "WAR" };

static int pbv_edge_reg(const PBInst *p, const PBInst *c, int type) {
    short ru[PB_MAX_USES]; int nru;
    int i, j;
    if (type == PBD_FLOW) {
        nru = pb_real_uses(c, ru);
        for (i = 0; i < p->n_defs; i++)
            for (j = 0; j < nru; j++) if (p->defs[i] == ru[j]) return p->defs[i];
    } else if (type == PBD_OUTPUT) {
        for (i = 0; i < p->n_defs; i++)
            for (j = 0; j < c->n_defs; j++) if (p->defs[i] == c->defs[j]) return p->defs[i];
    } else {

        nru = pb_real_uses(p, ru);
        for (i = 0; i < nru; i++)
            for (j = 0; j < c->n_defs; j++) if (ru[i] == c->defs[j]) return ru[i];
    }
    return -1;
}

static void pbv_reg_name(int r, char *out, size_t cap) {
    if (r < 0)          snprintf(out, cap, "?");
    else if (r == PB_CC) snprintf(out, cap, "CC");
    else if (r >= 300)  snprintf(out, cap, "P%d", r - 300);
    else if (r == 255)  snprintf(out, cap, "RZ");
    else                snprintf(out, cap, "R%d", r);
}

static int pb_validate_stream(const u8 *bc, u32 constOff, int verbose,
                              int lo, int hi, const char *tag) {
    int n;
    PBInst *insts = pb_build(bc, constOff, &n);
    if (n == 0) { free(insts); return 0; }

    u32 *ctrl = (u32 *)calloc((size_t)n, sizeof(u32));
    { int idx = 0; u32 off;
      for (off = INSTR_START; off + 32 <= constOff && idx < n; off += 32) {
          u64 c64; memcpy(&c64, bc + off, 8);
          { int s; for (s = 0; s < 3 && idx < n; s++, idx++)
              ctrl[idx] = (u32)((c64 >> (21 * s)) & 0x1FFFFFu); }
      } }

    int pad_start = n;
    { int i; for (i = n - 1; i >= 0; i--) {
          if (insts[i].q == 0 || insts[i].op == OP_Nop) pad_start = i; else break; } }

    int nbb; PBBlock *bbs = pb_basic_blocks(insts, n, &nbb);
    int nviol = 0, nchecked = 0, ncov_time = 0, ncov_sb = 0, nopen = 0;
    int by_kind[3]; by_kind[0] = by_kind[1] = by_kind[2] = 0;
    int shown = 0;
    int bi;

    for (bi = 0; bi < nbb; bi++) {
        int s = bbs[bi].start, e = bbs[bi].end, bn = e - s;
        const PBInst *block = &insts[s];
        if (bn <= 0) continue;
        PBDepList *dep = (PBDepList *)calloc((size_t)bn, sizeof(PBDepList));
        int *cyc  = (int *)calloc((size_t)bn, sizeof(int));
        int *covW = (int *)malloc(sizeof(int) * (size_t)bn);
        int *covR = (int *)malloc(sizeof(int) * (size_t)bn);
        u8  *ewait = (u8 *)calloc((size_t)bn, 1);
        int *qidx = (int *)malloc(sizeof(int) * (size_t)(bn + 1));
        int *qkind = (int *)malloc(sizeof(int) * (size_t)(bn + 1));
        int k, b;
        if (!dep || !cyc || !covW || !covR || !ewait || !qidx || !qkind) {
            free(dep); free(cyc); free(covW); free(covR); free(ewait);
            free(qidx); free(qkind); continue;
        }
        pb_calc_deps(block, bn, dep);

        for (k = 0; k < bn; k++) {
            u32 c = ctrl[s + k];
            int w = (int)((c >> 11) & 0x3F);
            if (block[k].op == OP_Depbar) w |= pb_depbar_req(block[k].q);
            ewait[k] = (u8)w;
            if (k + 1 < bn) cyc[k + 1] = cyc[k] + pb_opexWait[c & 0x1F];
        }
        for (k = 0; k < bn; k++) { covW[k] = -1; covR[k] = -1; }

        for (b = 0; b < 6; b++) {
            int qn = 0;
            for (k = 0; k < bn; k++) {
                u32 c = ctrl[s + k];
                int wb, rb;
                if ((ewait[k] >> b) & 1) {
                    int t; for (t = 0; t < qn; t++)
                        { if (qkind[t]) covR[qidx[t]] = k; else covW[qidx[t]] = k; }
                    qn = 0;
                } else if (block[k].op == OP_Depbar && pb_depbar_le(block[k].q) &&
                           pb_depbar_sb(block[k].q) == b) {
                    int thr = pb_depbar_thr(block[k].q);
                    int drop = qn - thr, t;
                    if (drop > 0) {
                        for (t = 0; t < drop; t++)
                            { if (qkind[t]) covR[qidx[t]] = k; else covW[qidx[t]] = k; }
                        for (t = drop; t < qn; t++)
                            { qidx[t - drop] = qidx[t]; qkind[t - drop] = qkind[t]; }
                        qn -= drop;
                    }
                }
                wb = (int)((c >> 5) & 7);
                rb = (int)((c >> 8) & 7);
                if (wb == b && qn <= bn) { qidx[qn] = k; qkind[qn] = 0; qn++; }
                if (rb == b && qn <= bn) { qidx[qn] = k; qkind[qn] = 1; qn++; }
            }
        }

        {
            int minW[9], minR[9], v;
            for (v = 0; v < 9; v++) { minW[v] = PBV_INF; minR[v] = PBV_INF; }
            for (k = bn - 1; k >= 0; k--) {
                u32 c = ctrl[s + k];
                int wb = (int)((c >> 5) & 7), rb = (int)((c >> 8) & 7);
                int wcov = (wb != 7 && covW[k] >= 0) ? covW[k] : PBV_INF;
                int rcov = (rb != 7 && covR[k] >= 0) ? covR[k] : PBV_INF;
                int ew = wcov, er = (rcov < wcov) ? rcov : wcov;
                v = block[k].vq;
                if (v >= PBVQ_ORDERED_FIRST && v <= PBVQ_ORDERED_LAST) {
                    if (minW[v] < ew) ew = minW[v];
                    if (minR[v] < er) er = minR[v];
                    minW[v] = ew; minR[v] = er;
                }
                covW[k] = (ew == PBV_INF) ? -1 : ew;
                covR[k] = (er == PBV_INF) ? -1 : er;
            }
        }

        for (k = 0; k < bn; k++) {
            int gi = s + k, d;
            if (gi >= pad_start) break;
            for (d = 0; d < dep[k].n; d++) {
                int to = dep[k].d[d].to, ty = dep[k].d[d].type;
                int req, avail, bar, cov, kind, reg;
                char rn[8];
                if (to <= k || to >= bn) continue;
                if (s + to >= pad_start) continue;
                req = pb_dep_latency(&block[k], &block[to], ty);
                if (req <= 0) continue;
                nchecked++;
                avail = cyc[to] - cyc[k];
                if (avail >= req) { ncov_time++; continue; }
                if (ty == PBD_ANTI) {
                    bar = (int)((ctrl[gi] >> 8) & 7);
                    cov = covR[k]; kind = PBV_WAR;
                } else {
                    bar = (int)((ctrl[gi] >> 5) & 7);
                    cov = covW[k]; kind = (ty == PBD_FLOW) ? PBV_RAW : PBV_WAW;
                }
                if (cov >= 0 && cov <= to) { ncov_sb++; continue; }
                nviol++; by_kind[kind]++;
                reg = pbv_edge_reg(&block[k], &block[to], ty);
                pbv_reg_name(reg, rn, sizeof rn);
                if (s + to < lo || s + to > hi) continue;
                if (verbose || shown < 200) {
                    shown++;
                    printf("  VIOLATION slot=%-5d %s %-4s prod=%-5d(%s) "
                           "avail=%-4d req=%-4d bar=%s drain=%s  bb=%d\n",
                           s + to, pbv_kind_name[kind], rn, gi,
                           (block[k].op >= 0 && block[k].op < 178) ? SM50_NAME[block[k].op] : "?",
                           avail, req,
                           bar == 7 ? "none" : (bar == 0 ? "0" : bar == 1 ? "1" :
                             bar == 2 ? "2" : bar == 3 ? "3" : bar == 4 ? "4" : "5"),
                           cov < 0 ? "never" : "late", bi);
                }
            }
        }

        for (k = 0; k < bn; k++) {
            u32 c = ctrl[s + k];
            if (s + k >= pad_start) break;
            if (((c >> 5) & 7) != 7 && covW[k] < 0) nopen++;
            if (((c >> 8) & 7) != 7 && covR[k] < 0) nopen++;
        }

        for (k = 0; k < bn; k++) pbd_free(&dep[k]);
        free(dep); free(cyc); free(covW); free(covR); free(ewait);
        free(qidx); free(qkind);
    }

    printf("%s: %d hazards checked, %d covered by cycles, %d by scoreboard, "
           "%d UNCOVERED (RAW %d / WAW %d / WAR %d), %d barrier(s) open at "
           "block end\n",
           tag ? tag : "validate", nchecked, ncov_time, ncov_sb, nviol,
           by_kind[PBV_RAW], by_kind[PBV_WAW], by_kind[PBV_WAR], nopen);
    free(ctrl); free(bbs); free(insts);
    return nviol;
}

#endif
static int _pa_ovr = 1;
static int _pa_depfwd = 0;
static int _pa_npd = 1;
static int _pa_antip = 1;
static int _pa_syncpush = 1;
static int _pa_ccp = 1;

static int _pa_ktt = 0;
static int _pa_esc = 1;
static int _pa_anti = 0;
static int _pa_texclamp = 1;
static int _pa_noguard = 0;
static int _pa_suses = 1;
static int _pa_pin_ssy = 0;

static void pa_add_sync_push_deps(const PBInst *blk, int n, PBDepList *dep);
#ifndef INKV_LIB

#endif
typedef struct { unsigned char *base; size_t cap, off; } PAArena;

static int pa_arena_init(PAArena *a, size_t cap) {
    a->base = (unsigned char *)malloc(cap ? cap : 1);
    a->cap = a->base ? cap : 0; a->off = 0;
    return a->base != NULL;
}
static void pa_arena_free(PAArena *a) { free(a->base); a->base = NULL; a->cap = a->off = 0; }
static void pa_arena_reset(PAArena *a) { a->off = 0; }
static void *pa_alloc(PAArena *a, size_t n) {

    size_t o = (a->off + 15u) & ~(size_t)15u;
    if (o + n > a->cap) return NULL;
    a->off = o + n;
    return a->base + o;
}
static void *pa_calloc(PAArena *a, size_t n) {
    void *p = pa_alloc(a, n);
    if (p) memset(p, 0, n);
    return p;
}

#define PA_DELAY_TO_PAIR   8
#define PA_BIG             9999999
#define PA_TEX_BATCH_MAX   50

static int pa_is_flow_ctl(int op) {
    switch (op) {
    case OP_Bra: case OP_Brx: case OP_Brk: case OP_Cont:
    case OP_Pexit:
    case OP_Jmp: case OP_Jmx: case OP_Cal: case OP_Jcal: case OP_Ret:
    case OP_Exit: case OP_Plongjmp: case OP_Bpt: case OP_Rtt:
    case OP_Sync:
        return 1;

    case OP_Ssy: case OP_Pbk: case OP_Pcnt: case OP_Pret:
        return _pa_pin_ssy;
    default: return 0;
    }
}

static int pa_min_next_issue(const PBInst *ip) {
    if (ip->op == OP_Depbar) return 3;
    if (ip->op == OP_Bar || ip->op == OP_Kil) return 5;
    if (ip->op == OP_Sam) return 2;
    if (pa_is_flow_ctl(ip->op)) return 5;
    return 0;
}

static int pa_inst_gets_offdeck(const PBInst *ip) {
    int mw = 0, nop = 0;
    return pbo_special_opex(ip, &mw, &nop) != -1;
}

typedef struct {
    int distance;
    int tav;
    int refRem;
    int refRem0;
    int closestTex;
    int closestDepTex;
    int closestRead;
    int closestKil;
    int texDepIndex;
    int resToUse;
    int anext, aprev;
    u8  inAvail;
    u8  pinned;
    u8  isTex;
    u8  texPhase;
} PASI;

typedef struct {

    int time;
    int resTimeFree[PB_MAX_RES];
    int dispTimeFree[PB_MAX_DISP];
    int nextTexTime, lastTexTime;
    int numInBundle, ipInBundle;

    int lastTexSchedTime, nextTexDistance;
    int nextTexLimitOrderNo, nextReadLimitOrderNo, nextKilLimitOrderNo;
    int maxTexIndexCommitted, numTexRemaining;
    int texLimit0, readLimit0, kilLimit0;
    int ipPriorAvail, ipPriorTex, priorTexTime, ipLastSched;
    int availHead, availSize;

    const PBInst *blk; PBDepList *dep; PASI *si; int n;

    int dbg, dbgFrom, dbgTo, step; const int *postPos;
    const int *force;
} PAB;

typedef struct {
    int  it;
    int  latency, stallPreDepBar, adjStallDistance, afterNextTex;
    int  overrideValue, maxRegBankUse, extraBankConflict;
    u8   BreaksBatch, ToBePaired, IsKill, CriticalKilDep, IsOffDeck, DefCcOrPReg, GoodForStall;
} PASel;

static void pa_avail_push_front(PAB *B, int i) {
    PASI *s = B->si;
    s[i].refRem = -1;
    s[i].aprev = -1;
    s[i].anext = B->availHead;
    if (B->availHead >= 0) s[B->availHead].aprev = i;
    B->availHead = i;
    s[i].inAvail = 1;
    B->availSize++;
}
static void pa_avail_remove(PAB *B, int i) {
    PASI *s = B->si;
    if (s[i].aprev >= 0) s[s[i].aprev].anext = s[i].anext;
    else                 B->availHead = s[i].anext;
    if (s[i].anext >= 0) s[s[i].anext].aprev = s[i].aprev;
    s[i].anext = s[i].aprev = -1;
    s[i].inAvail = 0;
    B->availSize--;
}

static int pa_can_pair(PAB *B, int a, int b, int hasDep) {
    const PBInst *fa = &B->blk[a], *fb = &B->blk[b];
    if (fa->coupled == PBC_DECOUPLED || fa->singleton) return 0;
    if (fb->coupled != PBC_DECOUPLED || fb->singleton) return 0;
    if (pb_has_uniform_ref(fa->q) &&
        (pb_has_uniform_ref(fb->q) || pb_is_tex_batch_op(fb->op))) return 0;

    if (hasDep) {
        int k;
        for (k = 0; k < B->dep[a].n; k++) {
            if (B->dep[a].d[k].to != b) continue;
            if (B->dep[a].d[k].type == PBD_FLOW) return 0;
            if (fa->coupled == PBC_REDIRECTED) return 0;
        }
    }
    if (fa->defs_ccp && pa_inst_gets_offdeck(fb)) return 0;
    return 1;
}

static int pa_ready_time(PAB *B, int i, int excludeBundled) {
    PBMach m; int excl = -1, rt;
    memset(&m, 0, sizeof(m));
    m.time = B->time;
    m.lastTexTime = B->lastTexTime;
    memcpy(m.resTimeFree, B->resTimeFree, sizeof(m.resTimeFree));
    memcpy(m.dispTimeFree, B->dispTimeFree, sizeof(m.dispTimeFree));
    if (excludeBundled && B->ipInBundle >= 0) excl = B->si[B->ipInBundle].resToUse;
    rt = pb_ready_time(&m, &B->blk[i], B->si[i].tav, excl, &B->si[i].resToUse);
    return rt;
}

static void pa_update_machine_resources(PAB *B, int i) {
    const PBInst *ip = &B->blk[i];
    if (pb_is_tex_batch_op(ip->op)) {
        if (B->time < B->nextTexTime) B->time = B->nextTexTime;
        B->nextTexTime = B->time + 1;
        B->lastTexTime = B->time;
    }
    if ((ip->res & PB_MODELED_RES) != 0 && B->si[i].resToUse >= 0) {
        int r = B->si[i].resToUse;
        B->resTimeFree[r] = B->time + pb_res_busy[r];
        B->dispTimeFree[pb_res_disp[r]] = B->time + 1;
    }
}

static void pa_issue_bundle(PAB *B) {
    B->time += 1;
    B->numInBundle = 0;
    B->ipInBundle = -1;
}

static void pa_schedule_instruction(PAB *B, int i) {
    int minNext;
    B->si[i].tav = B->time;
    pa_update_machine_resources(B, i);
    minNext = pa_min_next_issue(&B->blk[i]);
    if (minNext != 0) B->time += (minNext - 1);
    B->numInBundle++;
    if (B->numInBundle == 2) pa_issue_bundle(B);
    else                     B->ipInBundle = i;
}

static void pa_calc_info_for_block(PAB *B) {
    int n = B->n, i, k;
    int maxTime = 0, maxTexTime = 0;
    int closestTexOrderNo = PA_BIG, closestReadOrderNo = PA_BIG, closestKilOrderNo = PA_BIG;
    int ipTex = -1, texIndex = B->numTexRemaining;
    PASI *s = B->si;
    B->nextTexDistance = 0;
    B->maxTexIndexCommitted = 0;
    for (i = n - 1; i >= 0; i--) {
        const PBInst *ip = &B->blk[i];
        int time = 0;
        if (B->dep[i].n == 0) time = pb_lat_flow(ip, NULL);
        if (ip->op == OP_Kil && maxTime > time) time = maxTime;

        if (_pa_ktt && ipTex >= 0 && !s[i].isTex) {
            int i2;
            B->nextTexDistance = s[ipTex].closestDepTex;
            for (i2 = ipTex; i2 >= 0; i2--) {
                if (!s[i2].isTex) break;
                s[i2].closestDepTex = B->nextTexDistance;
                B->nextTexDistance = maxTexTime;
                s[i2].distance = maxTexTime++;
            }
            ipTex = -1;
        }
        for (k = 0; k < B->dep[i].n; k++) {
            int to = B->dep[i].d[k].to, ty = B->dep[i].d[k].type, tt;
            if (ty == PBD_FLOW)        tt = s[to].distance + pb_lat_flow(ip, &B->blk[to]);
            else if (ty == PBD_OUTPUT) tt = s[to].distance + pb_lat_output(ip, &B->blk[to]);
            else if (_pa_anti)         tt = s[to].distance + pb_lat_anti(ip, &B->blk[to]);
            else                       tt = s[to].distance + 1;

            if (_pa_ktt && _pa_texclamp && s[to].isTex && tt <= B->nextTexDistance)
                tt = B->nextTexDistance + (_pa_texclamp == 2 ? 0 : 1);
            if (tt > time) time = tt;

            if (s[i].isTex && texIndex > s[to].texDepIndex) s[to].texDepIndex = texIndex;
        }
        s[i].closestTex    = closestTexOrderNo;
        s[i].closestDepTex = B->nextTexDistance;
        s[i].closestRead   = closestReadOrderNo;
        s[i].closestKil    = closestKilOrderNo;
        if (s[i].isTex) {

            if (_pa_npd && !_pa_ktt && time < B->nextTexDistance + 1)
                time = B->nextTexDistance + 1;
            if (maxTime > time) time = maxTime;
            closestTexOrderNo = i + 1;
            B->nextTexDistance = time;
            texIndex--;
        }

        if (ip->op == OP_Kil) closestKilOrderNo = i + 1;
        s[i].distance = time;
        if (time > maxTime) maxTime = time;
        if (_pa_ktt && s[i].isTex) {
            if (ipTex < 0) { ipTex = i; maxTexTime = time; }
            else if (time > maxTexTime) maxTexTime = time;
        }
    }
    B->nextTexLimitOrderNo  = closestTexOrderNo;
    B->nextReadLimitOrderNo = closestReadOrderNo;
    B->nextKilLimitOrderNo  = closestKilOrderNo;
    B->texLimit0  = closestTexOrderNo;
    B->readLimit0 = closestReadOrderNo;
    B->kilLimit0  = closestKilOrderNo;
}

static int pa_pick_best(PAB *B, int *pToBePaired) {
    PASel best, cur, pairSecond, offDeck, forced;
    int DepOnPrior = 1;
    int nextReadOrderNo = PA_BIG, nextKilOrderNo = PA_BIG;
    int it, itPrior;
    PASI *s = B->si;

    memset(&pairSecond, 0, sizeof(pairSecond)); pairSecond.it = -1;
    memset(&best, 0, sizeof(best));             best.it = -1;
    memset(&forced, 0, sizeof(forced));         forced.it = -1;
    int dbg = B->dbg && B->step >= B->dbgFrom && B->step <= B->dbgTo;
    if (dbg && B->postPos) {
        int w = -1, q;
        for (q = 0; q < B->n; q++) if (B->postPos[q] == B->step) { w = q; break; }
        if (w >= 0)
            printf("  ORACLE wants pre%d %s  (avail=%d refRem=%d pinned=%d)\n", w,
                   SM50_NAME[B->blk[w].op], B->si[w].inAvail, B->si[w].refRem, B->si[w].pinned);
        if (w >= 0 && !B->si[w].inAvail) {
            int p2, k2;
            for (p2 = 0; p2 < B->n; p2++)
                for (k2 = 0; k2 < B->dep[p2].n; k2++)
                    if (B->dep[p2].d[k2].to == w && B->si[p2].refRem >= 0)
                        printf("     blocked by pre%d %s type=%d (refRem=%d)\n", p2,
                               SM50_NAME[B->blk[p2].op], B->dep[p2].d[k2].type, B->si[p2].refRem);
        }
    }
    if (dbg)
        printf("  --- pick step %d: time=%d inBundle=%d numIn=%d priorAvail=%d "
               "nextTexDist=%d texLimit=%d lastTexSched=%d availN=%d\n",
               B->step, B->time, B->ipInBundle, B->numInBundle, B->ipPriorAvail,
               B->nextTexDistance, B->nextTexLimitOrderNo, B->lastTexSchedTime, B->availSize);
    for (;;) {
        best.it = -1; best.latency = 9999;
        memset(&offDeck, 0, sizeof(offDeck)); offDeck.it = -1;
        for (it = B->availHead; it >= 0; it = s[it].anext) {
            const PBInst *ip = &B->blk[it];

            int timeAvailable = 0, Better = 0;
            if (it == B->ipPriorAvail) DepOnPrior = 0;
            if (nextReadOrderNo > s[it].closestRead) nextReadOrderNo = s[it].closestRead;
            if (nextKilOrderNo  > s[it].closestKil)  nextKilOrderNo  = s[it].closestKil;
            memset(&cur, 0, sizeof(cur));
            cur.it = it;
            cur.DefCcOrPReg = (u8)(ip->defs_ccp != 0);
            cur.IsOffDeck   = (u8)pa_inst_gets_offdeck(ip);
            cur.overrideValue = 0;
            cur.ToBePaired  = 0;
            cur.extraBankConflict = 0;
            if (B->ipInBundle >= 0 && pa_can_pair(B, B->ipInBundle, it, DepOnPrior)) {

                timeAvailable = pa_ready_time(B, it, 1);
                if (timeAvailable <= B->time + PA_DELAY_TO_PAIR) cur.ToBePaired = 1;
            }
            if (!cur.ToBePaired) {
                timeAvailable = pa_ready_time(B, it, 0);
                if (B->ipInBundle >= 0 && timeAvailable <= B->time + 1)
                    timeAvailable = B->time + 1;
            }
            cur.latency = timeAvailable - B->time;
            if (cur.latency < 0) cur.latency = 0;
            if (pairSecond.it >= 0) {
                int d = cur.latency - pairSecond.latency; if (d < 0) d = -d;
                if (it == pairSecond.it || d > PA_DELAY_TO_PAIR ||
                    !pa_can_pair(B, it, pairSecond.it, 0))
                    continue;
            }
            cur.IsKill = (u8)(ip->op == OP_Kil);
            cur.CriticalKilDep = 0;
            cur.maxRegBankUse = 0;

            if (_pa_ktt) {
                cur.afterNextTex = (s[it].distance < B->nextTexDistance) * 2
                                 + (s[it].distance == B->nextTexDistance);
            } else {
                cur.afterNextTex = ((it + 1) > B->nextTexLimitOrderNo) * 2;

                if (!_pa_npd && (it + 1) == B->nextTexLimitOrderNo &&
                    s[it].distance <= B->nextTexDistance + 18) cur.afterNextTex++;
            }
            cur.BreaksBatch = 0;
            if (B->time <= B->lastTexSchedTime + 1) {
                if (s[it].isTex) {
                    if (s[it].distance != B->nextTexDistance ||
                        B->time + cur.latency > B->lastTexSchedTime + 1)
                        cur.BreaksBatch = 1;
                } else {
                    if (B->time + cur.latency + 1 > B->lastTexSchedTime + 1)
                        cur.BreaksBatch = 1;
                }
            }
            cur.stallPreDepBar = cur.latency;
            cur.adjStallDistance = s[it].distance - cur.latency;
            cur.GoodForStall = (u8)(_pa_esc && s[it].texDepIndex <= B->maxTexIndexCommitted &&
                                    (it + 1) <= B->nextReadLimitOrderNo &&
                                    (it + 1) <= B->nextKilLimitOrderNo &&
                                    s[it].closestTex <= B->nextTexLimitOrderNo);

            if (B->force && B->step >= 0 && B->force[B->step] == it) forced = cur;
            if (dbg)
                printf("    cand pre%-4d %-9s post%-4d lat=%-4d dist=%-5d adj=%-6d "
                       "aft=%d brk=%d pair=%d gfs=%d spd=%-4d od=%d ccp=%d\n",
                       it, SM50_NAME[ip->op], B->postPos ? B->postPos[it] : -1,
                       cur.latency, s[it].distance, cur.adjStallDistance,
                       cur.afterNextTex, cur.BreaksBatch, cur.ToBePaired,
                       cur.GoodForStall, cur.stallPreDepBar, cur.IsOffDeck, cur.DefCcOrPReg);
            if (best.it < 0) {
                Better = 1;
            } else if (cur.overrideValue != best.overrideValue) {
                if (cur.overrideValue < best.overrideValue) Better = 1;
            } else if (cur.BreaksBatch != best.BreaksBatch) {
                Better = best.BreaksBatch;
            } else if (cur.afterNextTex != best.afterNextTex) {
                if (cur.afterNextTex < best.afterNextTex) Better = 1;
            } else if (cur.CriticalKilDep != best.CriticalKilDep) {
                Better = cur.CriticalKilDep;
            } else if (cur.ToBePaired != best.ToBePaired) {
                Better = cur.ToBePaired;
            } else if (cur.ToBePaired && cur.latency != best.latency) {

                if (cur.latency < best.latency) Better = 1;
            } else if (cur.stallPreDepBar < best.stallPreDepBar && cur.GoodForStall) {
                Better = 1;
            } else if (best.stallPreDepBar < cur.stallPreDepBar && best.GoodForStall) {

            } else if (cur.adjStallDistance != best.adjStallDistance) {
                if (cur.adjStallDistance > best.adjStallDistance) Better = 1;
            } else if (cur.latency != best.latency) {
                if (cur.latency < best.latency) Better = 1;
            } else if (cur.IsKill != best.IsKill) {
                Better = cur.IsKill;
            } else if (cur.maxRegBankUse != best.maxRegBankUse) {
                if (cur.maxRegBankUse > best.maxRegBankUse) Better = 1;
            } else {
                if (it < best.it) Better = 1;
            }
            if (cur.IsOffDeck) offDeck = cur;
            if (Better) best = cur;
        }
        if (B->force && B->step >= 0 && B->force[B->step] >= 0 &&
            forced.it == B->force[B->step] && best.it != forced.it) {

            best = forced;
            break;
        }
        if (best.it < 0) { best = pairSecond; break; }

        if (_pa_ovr && best.DefCcOrPReg && offDeck.it >= 0 && B->availSize < 9) best = offDeck;
        if (B->ipInBundle < 0 && pairSecond.it < 0 &&
            !s[best.it].isTex && B->blk[best.it].coupled == PBC_DECOUPLED)
        {

            pairSecond = best;
            continue;
        }
        break;
    }

    s[best.it].tav = pa_ready_time(B, best.it, best.ToBePaired);

    if (s[best.it].isTex) {
        B->numTexRemaining--;
        B->lastTexSchedTime = B->time + best.latency;
        if (B->nextTexLimitOrderNo < s[best.it].closestTex) {
            B->nextTexLimitOrderNo = s[best.it].closestTex;
            B->nextTexDistance     = s[best.it].closestDepTex;
        }
        s[best.it].texPhase = 2;
        if (_pa_ktt) {
            if (B->ipLastSched >= 0 && s[B->ipLastSched].isTex)
                s[B->ipLastSched].texPhase = 1;
        } else if (B->ipPriorTex >= 0 &&
                   B->priorTexTime + PA_TEX_BATCH_MAX > B->lastTexSchedTime) {
            s[B->ipPriorTex].texPhase = 1;
        }
        B->ipPriorTex = best.it;
        B->priorTexTime = B->lastTexSchedTime;
    }
    if (s[best.it].texDepIndex > B->maxTexIndexCommitted)
        B->maxTexIndexCommitted = s[best.it].texDepIndex;
    if (best.it + 1 == B->nextReadLimitOrderNo) B->nextReadLimitOrderNo = nextReadOrderNo;
    if (best.it + 1 == B->nextKilLimitOrderNo)  B->nextKilLimitOrderNo  = nextKilOrderNo;

    if (s[best.it].tav > B->time + PA_DELAY_TO_PAIR) best.ToBePaired = 0;
    if (best.ToBePaired && (B->ipInBundle < 0 || !pa_can_pair(B, B->ipInBundle, best.it, 0)))
        best.ToBePaired = 0;

    if (!best.ToBePaired) {
        if (B->numInBundle > 0) { pa_issue_bundle(B); pa_ready_time(B, best.it, 0); }
    } else {
        int ta = s[best.it].tav;
        if (ta > B->time) {
            int f = B->ipInBundle, k;
            s[f].tav = ta;
            pa_update_machine_resources(B, f);
            for (k = 0; k < B->dep[f].n; k++) {
                int to = B->dep[f].d[k].to;
                int t  = s[f].tav + pb_dep_latency(&B->blk[f], &B->blk[to], B->dep[f].d[k].type);
                if (t > s[to].tav) s[to].tav = t;
            }
        }

    }
    if (dbg)
        printf("  === picked pre%d (post %d) paired=%d tav=%d\n", best.it,
               B->postPos ? B->postPos[best.it] : -1, best.ToBePaired, s[best.it].tav);
    itPrior = B->availHead;
    if (best.it == itPrior) itPrior = s[itPrior].anext;
    B->ipPriorAvail = itPrior;
    *pToBePaired = best.ToBePaired;
    return best.it;
}

static int pa_is_sync_push(int op) {
    return op == OP_Ssy || op == OP_Pbk || op == OP_Pcnt || op == OP_Pret;
}
static void pa_add_sync_push_deps(const PBInst *blk, int n, PBDepList *dep) {
    int i, last = -1;
    for (i = 0; i < n; i++) {
        if (!pa_is_sync_push(blk[i].op)) continue;
        if (last >= 0) pbd_add(&dep[last], i, PBD_ANTI);
        last = i;
    }
    if (last >= 0 && last != n - 1) pbd_add(&dep[last], n - 1, PBD_ANTI);
}

static int pa_has_reg_flow_dep(const PBInst *a, const PBInst *b) {
    int i, j;
    for (i = 0; i < a->n_defs; i++) {
        int r = a->defs[i];
        if (r == 255) continue;
        for (j = 0; j < b->n_defs; j++) if (b->defs[j] == r) return 1;
        for (j = 0; j < b->n_uses; j++) if (b->uses[j] == r) return 1;
    }
    return 0;
}

static void pa_finish_block_sched_inst(PAB *B, int i, int forceIssue) {
    PASI *s = B->si;
    s[i].tav = pa_ready_time(B, i, 0);
    if (B->ipInBundle >= 0) {
        if (pa_can_pair(B, B->ipInBundle, i, 0) &&
            !pa_has_reg_flow_dep(&B->blk[B->ipInBundle], &B->blk[i]))
        {
            if (s[i].tav > B->time) B->time = s[i].tav;
            s[B->ipInBundle].tav = B->time;
        } else {
            pa_issue_bundle(B);
        }
    }
    if (s[i].tav > B->time) B->time = s[i].tav;
    pa_schedule_instruction(B, i);
    if (forceIssue && B->numInBundle > 0) pa_issue_bundle(B);
}

static int pa_schedule_block(PAB *B, int *out) {
    int i, k, kk, nout = 0;
    PASI *s = B->si;

    for (i = 0; i < B->n; i++) s[i].refRem = 0;
    for (i = 0; i < B->n; i++)
        for (k = 0; k < B->dep[i].n; k++) s[B->dep[i].d[k].to].refRem++;

    { int seen = 0;
      for (i = 0; i < B->n; i++) {
          if (pa_is_flow_ctl(B->blk[i].op)) seen = 1;
          s[i].pinned = (u8)seen;
          if (seen) s[i].refRem++;
      } }

    for (i = 0; i < B->n; i++) s[i].refRem0 = s[i].refRem ? s[i].refRem : -1;
    pa_calc_info_for_block(B);

    B->availHead = -1; B->availSize = 0;
    B->ipPriorAvail = -1;
    for (i = 0; i < B->n; i++)
        if (s[i].refRem == 0) pa_avail_push_front(B, i);
    B->ipLastSched = -1;
    while (B->availHead >= 0) {
        int paired = 0;
        int bi;
        B->step = nout;
        bi = pa_pick_best(B, &paired);
        if (bi < 0) break;
        if (s[bi].tav > B->time) B->time = s[bi].tav;

        pa_avail_remove(B, bi);
        for (kk = 0; kk < B->dep[bi].n; kk++) {
            int k = _pa_depfwd ? kk : (B->dep[bi].n - 1 - kk);
            int to = B->dep[bi].d[k].to;
            int t  = B->time + pb_dep_latency(&B->blk[bi], &B->blk[to], B->dep[bi].d[k].type);
            if (t > s[to].tav) s[to].tav = t;
            s[to].refRem--;
            if (s[to].refRem == 0) pa_avail_push_front(B, to);
        }
        out[nout++] = bi;
        pa_schedule_instruction(B, bi);
        B->ipLastSched = bi;
    }
    for (i = 0; i < B->n; i++)
        if (s[i].pinned) { pa_finish_block_sched_inst(B, i, 1); out[nout++] = i; }
    return nout;
}

#ifndef INKV_LIB

#include <time.h>

#endif
