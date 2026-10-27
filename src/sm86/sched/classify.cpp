
#include "classify.h"

#include <cstring>

namespace ub {
namespace sm86 {
namespace sched {

namespace {

enum {
    LAT_FMA = 4, LAT_ALU = 4, LAT_UDP = 1, LAT_HMMA16 = 4, LAT_HMMA32 = 4, LAT_IMMA = 4,
    LAT_LSU = 24, LAT_LDS = 40, LAT_CBU = 6, LAT_XU64 = 16, LAT_IPA = 32, LAT_TEX = 300,
    LAT_ADU = 24, LAT_SCD = 4, LAT_TTU = 1000, LAT_A_FMA64 = 6, LAT_A_FP16 = 4, LAT_A_REDUX = 25,
    LAT_A_HFMA2MMA = 6, LAT_A_CLMAD = 8, LAT_A_IMMA88 = 11, LAT_A_HMMA1688 = 14,
    LAT_A_HMMA16816 = 22, LAT_A_DMMA = 18, LAT_A_GMMA = 20, LAT_SUQUERY = 200
};

inline uint32_t rb(int r) { return 1u << r; }

int g_by_isa_op[256];
bool g_init = false;
int I_IMAD, I_CS2R, I_F2F, I_F2I, I_I2F, I_FRND, I_BMOV, I_OUT, I_HADD2, I_UMOV, I_TTUMACROFUSE, I_CALL, I_PLOP3, I_MOV, I_BRA,
    I_EXIT, I_BREAK, I_RET, I_BRX, I_BRXU;

void init_map() {
    int n = nops();
    for (int o = 0; o < 256; o++) g_by_isa_op[o] = -1;
    for (int o = 1; o < n && o < 256; o++) {
        const char *nm = op_name(o);
        for (int s = 0; s < SOP_COUNT; s++) {
            if (strcmp(sop_name_tab[s], nm) == 0 && hw_attr_tab[s].valid) {
                g_by_isa_op[o] = s;
                break;
            }
        }
    }
    I_IMAD = op_id("IMAD"); I_CS2R = op_id("CS2R"); I_F2F = op_id("F2F"); I_F2I = op_id("F2I");
    I_I2F = op_id("I2F"); I_FRND = op_id("FRND"); I_BMOV = op_id("BMOV"); I_OUT = op_id("OUT");
    I_HADD2 = op_id("HADD2"); I_UMOV = op_id("UMOV"); I_TTUMACROFUSE = op_id("TTUMACROFUSE");
    I_CALL = op_id("CALL"); I_PLOP3 = op_id("PLOP3"); I_MOV = op_id("MOV"); I_BRA = op_id("BRA");
    I_EXIT = op_id("EXIT"); I_BREAK = op_id("BREAK"); I_RET = op_id("RET"); I_BRX = op_id("BRX");
    I_BRXU = op_id("BRXU");
    g_init = true;
}

int val(const Inst &i, const char *name, int64_t dflt) {
    int v = val_index(i.cls, name);
    return v < 0 ? (int)dflt : (int)get(i, v);
}

bool any_wide_gpr(const Operand *o, int n) {
    for (int k = 0; k < n; k++)
        if (o[k].kind == O_GPR && o[k].nregs == 2) return true;
    return false;
}

void unit_latency(SchedClass *c) {
    uint32_t r = c->res;
    bool fp16_alu = c->sop == SOP_SM70_HSET2 || c->sop == SOP_SM70_HSETP2 || c->sop == SOP_SM82_HMNMX2;
    bool fp16_fma = c->sop == SOP_SM70_HADD2_F32;

    if (r & rb(RES_FMA64LITE)) { c->unit = UV_REDIRECTED_FMA64; c->latency = LAT_A_FMA64; return; }
    if ((r & rb(RES_FP16C)) || fp16_alu || fp16_fma) { c->unit = UV_COUPLED_FP16; c->latency = LAT_A_FP16; return; }
    if (r & rb(RES_IMMA16816)) {
        bool i88 = c->sop == SOP_SM82_IMMA_88 || c->sop == SOP_SM82_IMMA_SP_88 || c->sop == SOP_SM82_BMMA_88128;
        c->latency = i88 ? LAT_A_IMMA88 : LAT_A_HMMA1688;
        c->unit = UT_REDIRECTED_HMMA_1688;
        return;
    }
    if (r & (rb(RES_HMMA1688) | rb(RES_HMMASP1688) | rb(RES_IMMASP16832))) {
        c->unit = UT_REDIRECTED_HMMA_1688; c->latency = LAT_A_HMMA1688; return;
    }
    if (r & (rb(RES_HMMA16816) | rb(RES_IMMA16832))) {
        c->unit = UT_REDIRECTED_HMMA_16816; c->latency = LAT_A_HMMA16816; return;
    }
    if (r & rb(RES_DMMA)) { c->unit = UA_REDIRECTED_DMMA; c->latency = LAT_A_DMMA; return; }
    if (r & rb(RES_REDUX)) { c->unit = UV_DECOUPLED_SM; c->latency = LAT_A_REDUX; return; }
    if (r & rb(RES_HFMA2MMA)) { c->unit = UA_COUPLED_HFMA2_MMA; c->latency = LAT_A_HFMA2MMA; return; }
    if (r & rb(RES_CLMAD)) { c->unit = UA_REDIRECTED_CLMAD; c->latency = LAT_A_CLMAD; return; }
    if (r & rb(RES_2XFMA)) { c->unit = UV_COUPLED_FMA; c->latency = LAT_FMA; return; }
    if (r & rb(RES_GMMA)) { c->unit = UA_DECOUPLED_GMMA; c->latency = LAT_A_GMMA; return; }

    if (r & rb(RES_TTU)) { c->unit = UT_DECOUPLED_TTU; c->latency = LAT_TTU; return; }
    if (r & rb(RES_UDP)) { c->unit = UT_COUPLED_UDP; c->latency = LAT_UDP; return; }
    if (r & rb(RES_HMMA1688)) { c->unit = UT_REDIRECTED_HMMA_1688; c->latency = LAT_A_HMMA1688; return; }
    if (r & rb(RES_HMMA16816)) { c->unit = UT_REDIRECTED_HMMA_16816; c->latency = LAT_A_HMMA16816; return; }

    if (r & rb(RES_FMA)) { c->unit = UV_COUPLED_FMA; c->latency = LAT_FMA; return; }
    if (r & rb(RES_ALU)) { c->unit = UV_COUPLED_ALU; c->latency = LAT_ALU; return; }
    if (r & rb(RES_HMMA16)) { c->unit = UV_REDIRECTED_HMMA16; c->latency = LAT_HMMA16; return; }
    if (r & rb(RES_HMMA32)) { c->unit = UV_REDIRECTED_HMMA32; c->latency = LAT_HMMA32; return; }
    if (r & rb(RES_IMMA)) { c->unit = UV_REDIRECTED_IMMA; c->latency = LAT_IMMA; return; }
    if (r & rb(RES_LSU)) { c->unit = UV_DECOUPLED_MEM; c->latency = LAT_LSU; return; }
    if (r & rb(RES_CBU)) { c->unit = UV_DECOUPLED_CBU; c->latency = LAT_CBU; return; }
    if (r & rb(RES_XU64)) { c->unit = UV_DECOUPLED_SM; c->latency = LAT_XU64; return; }
    if (r & rb(RES_IPA)) { c->unit = UV_DECOUPLED_MEM; c->latency = LAT_IPA; return; }
    if (r & rb(RES_TEX)) { c->unit = UV_DECOUPLED_SM; c->latency = LAT_TEX; return; }
    if (r & rb(RES_ADU)) { c->unit = UV_DECOUPLED_SM; c->latency = LAT_ADU; return; }
    if (r & rb(RES_SCHEDULE_DISPATCH)) { c->unit = UV_COUPLED_SCD; c->latency = LAT_SCD; return; }
    c->unit = UV_COUPLED_FMA;
    c->latency = LAT_FMA;
}

bool coupled_pred_bypass(int unit, int sop) {
    if (unit == UA_COUPLED_HFMA2_MMA) return false;
    if (sop == SOP_SM73_VOTEU || sop == SOP_SM73_ULDC) return false;
    if (unit == UV_COUPLED_SCD || unit == UV_COUPLED_FP16 || sop == SOP_SM70_CSMTEST ||
        sop == SOP_SM70_VOTE || sop == SOP_SM70_PMTRIG)
        return false;
    return true;
}

bool is_texture(int sop) {
    switch (sop) {
    case SOP_SM70_TEX: case SOP_SM70_TLD: case SOP_SM70_TLD4: case SOP_SM70_TMML:
    case SOP_SM70_TXD: case SOP_SM70_TXQ: case SOP_SM73_FOOTPRINT:
        return true;
    default:
        return false;
    }
}

bool is_surface(int sop) {
    return sop == SOP_SM70_SULD || sop == SOP_SM70_SUST || sop == SOP_SM70_SUATOM ||
           sop == SOP_SM70_SURED || sop == SOP_SM86_SUQUERY;
}

}

int sass_op(const Inst &i) {
    if (!g_init) init_map();
    if (i.cls < 0 || i.op <= 0 || i.op >= 256) return SOP_SM70_LAST;
    Operand o[MAX_OPNDS];
    int n;
    int op = i.op;
    if (op == I_IMAD) return val(i, "wide", 0) != 0 ? SOP_SM70_IMAD_WIDE : SOP_SM70_IMAD;
    if (op == I_CS2R) return val(i, "sz", 1) == 0 ? SOP_SM70_CS2R_32 : SOP_SM70_CS2R_64;
    if (op == I_F2F || op == I_F2I || op == I_I2F || op == I_FRND) {
        n = operands(i, o, MAX_OPNDS);
        bool x = any_wide_gpr(o, n);
        if (op == I_F2F) return x ? SOP_SM70_F2F_X : SOP_SM70_F2F;
        if (op == I_F2I) return x ? SOP_SM70_F2I_X : SOP_SM70_F2I;
        if (op == I_I2F) return x ? SOP_SM70_I2F_X : SOP_SM70_I2F;
        return x ? SOP_SM70_FRND_X : SOP_SM70_FRND;
    }
    if (op == I_BMOV) {
        n = operands(i, o, MAX_OPNDS);
        for (int k = 0; k < n; k++) {
            if (o[k].kind != O_GPR) continue;
            if (o[k].role == R_DEF) return SOP_SM70_BMOV_R;
            if (o[k].role == R_USE) return SOP_SM70_BMOV_B;
        }
        return SOP_SM70_BMOV;
    }
    if (op == I_OUT) return val(i, "type", 1) == 0 ? SOP_SM70_OUT_FINAL : SOP_SM70_OUT;
    if (op == I_HADD2) return val(i, "ofmt", 0) == 1 ? SOP_SM70_HADD2_F32 : SOP_SM70_HADD2;
    if (op == I_UMOV) {
        n = operands(i, o, MAX_OPNDS);
        for (int k = 0; k < n; k++)
            if (o[k].kind == O_IMM || o[k].kind == O_FIMM) return SOP_SM73_ULDC;
        return SOP_SM73_UMOV;
    }
    if (op == I_TTUMACROFUSE) return SOP_SM73_TTUMACRO;

    if (op == I_CALL) {
        bool u, ng;
        return guard(i, &u, &ng) != 7 || ng ? SOP_SM70_BRA : SOP_SM70_CALL;
    }

    if (op == I_PLOP3) {
        n = operands(i, o, MAX_OPNDS);
        for (int k = 0; k < n; k++)
            if (o[k].kind == O_PRED && o[k].role == R_USE && (o[k].reg != 7 || (o[k].flags & F_NOT)))
                return SOP_SM70_PLOP3;
        for (int k = 0; k < n; k++)
            if (o[k].kind == O_UPRED && o[k].role == R_USE) return SOP_SM70_MOV;
        return SOP_SM70_PLOP3;
    }
    int s = g_by_isa_op[i.op];
    return s < 0 ? SOP_SM70_LAST : s;
}

bool classify(const Inst &i, int shader_type, SchedClass *c) {
    (void)shader_type;
    memset(c, 0, sizeof *c);
    c->sop = (int16_t)sass_op(i);
    if (c->sop == SOP_SM70_LAST || !hw_attr_tab[c->sop].valid) {
        c->res = ~0u;
        c->latency = -32768;
        c->flags = GF_DECOUPLED | GF_IS_LONG_LATENCY;
        return false;
    }
    const HwAttr &a = hw_attr_tab[c->sop];
    c->res = a.res;
    c->pipe = a.pipe;
    c->vq = a.vq;
    c->sbk = a.sb;
    unit_latency(c);
    if (c->sop == SOP_SM86_SUQUERY) c->latency = LAT_SUQUERY;
    if (c->sop == SOP_SM70_LDS || c->sop == SOP_SM73_LDSM) c->latency = LAT_LDS;

    uint32_t f = GF_IS_COLLECTOR_CACHE_VALID;
    bool tex = is_texture(c->sop);
    if (tex) f |= GF_IS_TEX_BATCH;
    if (tex || c->vq == VQ_TEX) f |= GF_IS_LONG_LATENCY;
    if (c->sbk & SBK_RD) f |= GF_NEEDS_READ_SB;
    if (c->sbk & SBK_WR) f |= GF_NEEDS_WRITE_SB;
    switch (c->pipe) {
    case PIPE_COUPLED:
        f |= GF_COUPLED;
        if (!coupled_pred_bypass(c->unit, c->sop)) f |= GF_NO_PRED_BYPASS;
        break;
    case PIPE_DECOUPLED: f |= GF_DECOUPLED | GF_NO_PRED_BYPASS; break;
    case PIPE_REDIRECTED: f |= GF_REDIRECTED | GF_NO_PRED_BYPASS; break;
    case PIPE_HYBRID: f |= GF_HYBRID | GF_NO_PRED_BYPASS; break;
    default: break;
    }
    if (c->vq == VQ_TEX && (f & GF_IS_LONG_LATENCY)) f |= GF_USE_HIGH_COST_SB;

    RSet86 def, use;
    def_use(i, &def, &use);
    for (int p = 0; p < 7; p++)
        if (def.has(key_p(p))) { f |= GF_DEF_CC_OR_PREG; break; }

    bool uni = false, neg = false;
    int g = guard(i, &uni, &neg);
    bool pred = g != 7 || neg;

    if (i.op == I_BRA || i.op == I_EXIT || i.op == I_BREAK || i.op == I_RET || i.op == I_BRX ||
        i.op == I_BRXU || i.op == I_CALL)
        pred = val(i, "Pp", 7) != 7 || val(i, "Pp@not", 0) != 0;

    if (c->sop == SOP_SM70_MOV) {
        int m = val(i, "PixMaskU04", 15);
        if (m != 15 && m != 1) pred = true;
    }
    if (pred) f |= GF_IS_PREDICATED;

    bool rd = false, wr = false;
    switch (c->sop) {
    case SOP_SM70_LDG: case SOP_SM70_LDL: case SOP_SM70_LD: rd = true; break;
    case SOP_SM70_STG: case SOP_SM70_STL: case SOP_SM70_ST: wr = true; break;
    case SOP_SM70_ATOMG: case SOP_SM70_ATOM: case SOP_SM70_RED: rd = wr = true; break;
    case SOP_SM70_SULD: rd = true; break;
    case SOP_SM70_SUST: wr = true; break;
    case SOP_SM70_SUATOM: case SOP_SM70_SURED: rd = wr = true; break;
    default: break;
    }
    if (rd) f |= GF_IS_LONG_LAT_MEM_READ;
    if (wr) f |= GF_IS_LONG_LAT_MEM_WRITE;

    if (c->sop == SOP_SM70_LDC || is_surface(c->sop)) {
        f |= GF_HAS_UNIFORM_REF;
    } else {
        Operand o[MAX_OPNDS];
        int n = operands(i, o, MAX_OPNDS);
        for (int k = 0; k < n; k++)
            if (o[k].kind == O_CBUF || o[k].kind == O_UCBUF) { f |= GF_HAS_UNIFORM_REF; break; }
    }
    c->flags = f;
    return true;
}

}
}
}
