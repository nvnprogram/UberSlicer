
#include "machine.h"

#include <algorithm>
#include <climits>

namespace ub {
namespace sm86 {
namespace sched {

LatCfg g_lat;
thread_local long long g_latency_worst_calls = 0;

bool bar_defer_blocking(const SInst &s) {
    int v = val_index(s.in.cls, "defer_blocking");
    return v >= 0 && get(s.in, v) != 0;
}

namespace {

const int UNIT_NONE = 0xff;
const int READ_SB_BASE_LATENCY = 8;
const int IMAD_WIDE_DISPATCH_STALL = 2;

enum {
    A_FMA64_RAW = 4, A_FP16_TO_COUPLED_RAW = 1, A_FP16_TO_REDIRECTED_RAW = 2, A_HMMA1688_RAW = 2,
    A_HMMA16816_RAW = 2, A_DMMA_RAW = 7, A_DMMA_TO_DECOUPLED_RAW = 5, A_DMMA_TO_DECOUPLED_MEM_RAW = 6,
    A_COUPLED_TO_IMMA_DMMA_RAW = 2, A_COUPLED_TO_DECOUPLED_MEM_RAW = 1, A_ALU_FMA_RAW = 1,
    A_SCD_RAW = 2, A_NOBYPASS_P_RAW = 9, A_FMA64_NOBYPASS_P_RAW = 8, A_UDP_TO_BRA_RAW = 8,
    A_VOTEU_TO_BRA_RAW = 1, A_COUPLED_TO_NON_COUPLED_WAR = 2, A_HMMA16816_TO_COUPLED_WAR = 7,
    A_FMA64_TO_IMAD_WAW = 5, A_FP16_FMA64_TO_NON_COUPLED_WAW = 1, A_FP16_TO_COUPLED_WAW = 1,
    A_FP16_TO_NON_COUPLED_P_WAW = 2, A_FMA64_TO_COUPLED_WAW = 3, A_FMA64_TO_COUPLED_P_WAW = 2,
    A_IMMA88_TO_COUPLED_WAW = 8, A_IMMA88_TO_MMA_WAW = 4, A_IMMA88_TO_DECOUPLED_WAW = 7,
    A_HMMA1688_TO_COUPLED_WAW = 11, A_HMMA1688_TO_MMA_WAW = 8, A_HMMA1688_TO_DECOUPLED_WAW = 10,
    A_HMMA16816_TO_COUPLED_WAW = 19, A_HMMA16816_TO_MMA_WAW = 16, A_HMMA16816_TO_DECOUPLED_WAW = 18,
    A_DMMA_TO_COUPLED_WAW = 20, A_DMMA_TO_HMMA1688_WAW = 17, A_DMMA_TO_MMA_WAW = 16,
    A_DMMA_TO_DECOUPLED_WAW = 19, A_UDP_TO_DECOUPLED_SM_WAW = 4, A_CLMAD_TO_FMA64_WAW = 4,
    A_COUPLED_TO_NON_COUPLED_WAW = 2, A_COUPLED_TO_COUPLED_WAW = 1
};

inline int unit(const SInst &s) { return s.sc.unit; }
inline int sop(const SInst &s) { return s.sc.sop; }
inline bool coupled(const SInst &s) { return (s.flags & GF_COUPLED) != 0; }
inline bool decoupled(const SInst &s) { return (s.flags & GF_DECOUPLED) != 0; }
inline bool redirected(const SInst &s) { return (s.flags & GF_REDIRECTED) != 0; }
inline bool no_pred_bypass(const SInst &s) { return (s.flags & GF_NO_PRED_BYPASS) != 0; }
inline bool def_cc_or_preg(const SInst &s) { return (s.flags & GF_DEF_CC_OR_PREG) != 0; }

inline bool has(int mask, int cls) { return (mask & (1 << cls)) != 0; }

bool unit_is_fp16(int u) { return u == UV_COUPLED_FP16 || u == UA_COUPLED_HFMA2_MMA; }
bool unit_is_mma(int u) {
    return u == UA_REDIRECTED_DMMA || u == UT_REDIRECTED_HMMA_1688 || u == UT_REDIRECTED_HMMA_16816 ||
           u == UV_REDIRECTED_HMMA16 || u == UV_REDIRECTED_HMMA32 || u == UV_REDIRECTED_IMMA;
}
bool is_imma88(int op) {
    return op == SOP_SM82_IMMA_88 || op == SOP_SM82_IMMA_SP_88 || op == SOP_SM82_BMMA_88128;
}

bool fp16_map_to_alu(int op) { return op == SOP_SM70_HSET2 || op == SOP_SM70_HSETP2 || op == SOP_SM82_HMNMX2; }
bool is_hadd2_f32(const SInst &s) { return sop(s) == SOP_SM70_HADD2_F32; }
bool is_udp_move(int op) { return op == SOP_SM73_VOTEU || op == SOP_SM73_ULDC || op == SOP_SM73_UMOV; }

bool is_pred_cls(int c) { return c == RC_P || c == RC_UP; }

bool guard_pred_dependent(const SInst &from, const SInst &to) {
    if (to.pred < 0) return false;
    for (int k = 0; k < from.nregs && from.regs[k].def; k++) {
        const SReg &r = from.regs[k];
        if (is_pred_cls(r.cls) && r.cls == to.pred_cls && r.no == to.pred) return true;
    }
    return false;
}

bool non_guard_pred_dependent(const SInst &from, const SInst &to) {
    for (int k = 0; k < from.nregs && from.regs[k].def; k++) {
        const SReg &d = from.regs[k];
        if (!is_pred_cls(d.cls)) continue;
        for (int j = to.nregs - 1; j >= 0 && !to.regs[j].def; j--) {
            const SReg &u = to.regs[j];
            if (u.attr & SR_GUARD) continue;
            if (u.cls == d.cls && u.no == d.no) return true;
        }
    }
    return false;
}

bool dep_predicate_is_subset(const SInst &from, const SInst &to) {
    if (from.pred < 0) return true;
    if (to.pred < 0) return false;
    if (from.pred_cond != to.pred_cond) return false;
    if (from.pred_cls == to.pred_cls && from.pred != to.pred) return false;
    return true;
}

bool bindless_opd_dependent(const SInst &from, const SInst &to) {
    for (int k = 0; k < to.nregs; k++) {
        const SReg &u = to.regs[k];
        if (!(u.attr & SR_BINDLESS) || !(u.attr & SR_BASE)) continue;
        for (int j = 0; j < from.nregs && from.regs[j].def; j++) {
            const SReg &d = from.regs[j];
            if (!(d.attr & SR_BASE)) continue;
            if (d.no == u.no || (d.no ^ 1) == u.no) return true;
        }
    }
    return false;
}

bool has_u_def_only(const SInst &s) {
    bool any = false;
    for (int k = 0; k < s.nregs && s.regs[k].def; k++) {
        if (s.regs[k].cls != RC_UR && s.regs[k].cls != RC_UP) return false;
        any = true;
    }
    return any;
}

int max_penalty_sm70(const SInst &f) {
    bool p = def_cc_or_preg(f);
    switch (unit(f)) {
    case UV_COUPLED_ALU: case UV_COUPLED_SCD: case UV_COUPLED_FMA: return p ? 8 : 4;
    case UV_COUPLED_FP16: return p ? 8 : 2;
    case UV_REDIRECTED_FMA64: return p ? 7 : 1;
    case UV_REDIRECTED_HMMA16: return 9;
    case UV_REDIRECTED_HMMA32: return 6;
    case UV_REDIRECTED_IMMA: return 11;
    default: return 0;
    }
}

int max_penalty_turing(const SInst &f) {
    switch (unit(f)) {
    case UT_COUPLED_UDP:
        if (is_udp_move(sop(f))) return 4;
        return def_cc_or_preg(f) ? 10 : 11;
    case UT_DECOUPLED_TTU: return 0;
    case UV_REDIRECTED_IMMA: return 6;
    default: return max_penalty_sm70(f);
    }
}

int max_penalty(const SInst &f) {
    bool p = def_cc_or_preg(f);
    int u = unit(f), lat = -1;
    switch (u) {
    case UV_COUPLED_SCD: case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_FP16:
        if (p) return A_NOBYPASS_P_RAW;
        lat = A_COUPLED_TO_IMMA_DMMA_RAW;
        break;
    case UA_COUPLED_HFMA2_MMA: case UV_REDIRECTED_FMA64:
        if (p) return A_FMA64_NOBYPASS_P_RAW;
        lat = A_FMA64_RAW;
        break;
    case UA_REDIRECTED_CLMAD: lat = A_FMA64_RAW; break;
    case UT_REDIRECTED_HMMA_1688: lat = A_HMMA1688_RAW; break;
    case UT_REDIRECTED_HMMA_16816: lat = A_HMMA16816_RAW; break;
    case UA_REDIRECTED_DMMA: lat = A_DMMA_RAW; break;
    case UA_DECOUPLED_GMMA: lat = 0; break;
    default: break;
    }
    if (lat == -1) lat = max_penalty_turing(f);
    if (!decoupled(f) && u != UT_COUPLED_UDP && u != UT_REDIRECTED_HMMA_16816 &&
        (u != UT_REDIRECTED_HMMA_1688 || is_imma88(sop(f))))
        lat++;
    return lat;
}

int hazard_sm70(const SInst &fi, const SInst &ti, int mask, bool checkBypass) {
    int from = unit(fi), to = unit(ti);
    bool bypass = checkBypass && (!no_pred_bypass(ti) || (from == to && (redirected(ti) || unit_is_fp16(to))));
    bool P = has(mask, RC_P), R = has(mask, RC_R);
    if (!P && !R) return 0;
    int rLat = 0, pLat = 0;
    switch (from) {
    case UV_COUPLED_ALU: case UV_COUPLED_SCD: case UV_COUPLED_FMA:
        if (P && !bypass) pLat = 8;
        switch (to) {
        case UV_COUPLED_ALU: case UV_COUPLED_SCD: case UV_COUPLED_FMA:
            rLat = from == to ? 0 : from == UV_COUPLED_SCD ? 2 : 1;
            break;
        case UV_DECOUPLED_CBU: case UV_DECOUPLED_SM: case UV_REDIRECTED_FMA64: case UV_COUPLED_FP16:
        case UV_REDIRECTED_HMMA16: case UV_REDIRECTED_HMMA32:
            rLat = 2;
            break;
        case UV_DECOUPLED_MEM: case UV_REDIRECTED_IMMA:
            rLat = 4;
            break;
        default:
            if (P) pLat = 8;
            else rLat = 1;
            break;
        }
        break;
    case UV_COUPLED_FP16:
        if (P && !bypass) pLat = 8;
        rLat = to == UV_COUPLED_FP16 ? 0 : 2;
        break;
    case UV_DECOUPLED_SM: case UV_DECOUPLED_MEM: case UV_DECOUPLED_CBU:
        rLat = 0;
        break;
    case UV_REDIRECTED_FMA64:
        if (P && !bypass) pLat = 7;
        rLat = to == UV_REDIRECTED_FMA64 ? 0 : 1;
        break;
    case UV_REDIRECTED_HMMA16: rLat = 9; break;
    case UV_REDIRECTED_HMMA32: rLat = 6; break;
    case UV_REDIRECTED_IMMA: rLat = 11; break;
    default: rLat = 8; break;
    }
    return std::max(rLat, pLat);
}

int hazard_turing(const SInst &fi, const SInst &ti, int mask, bool checkBypass) {
    bool UP = has(mask, RC_UP), UR = has(mask, RC_UR), P = has(mask, RC_P), R = has(mask, RC_R);
    if (!UP && !UR && !P && !R) return 0;
    int from = unit(fi), to = unit(ti), fop = sop(fi), top = sop(ti);
    bool bypass = checkBypass && (!no_pred_bypass(ti) || (from == to && redirected(ti)));
    if (P && top == SOP_SM73_VOTEU) {
        switch (from) {
        case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_SCD: return 8;
        case UV_REDIRECTED_FMA64: return 7;
        case UV_COUPLED_FP16: return 8;
        default: return 1;
        }
    }
    if (R && from == UV_REDIRECTED_IMMA) return 6;
    int lat = -1;
    if (!UP && !UR) {
        switch (from) {
        case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_SCD: case UV_COUPLED_FP16: {
            int rLat = -1;
            if ((to == UT_REDIRECTED_HMMA_1688 || to == UT_REDIRECTED_HMMA_16816) && R) rLat = 2;
            lat = rLat;
            break;
        }
        case UT_DECOUPLED_TTU: case UT_REDIRECTED_HMMA_1688: case UT_REDIRECTED_HMMA_16816:
            lat = 0;
            break;
        default:
            break;
        }
        if (lat == -1) lat = hazard_sm70(fi, ti, mask, checkBypass);
    }
    int upLat = -1;
    if (UP) {
        if (from == UT_COUPLED_UDP) {
            if (fop == SOP_SM73_VOTEU) {
                upLat = bypass ? 0 : 4;
            } else if (!bypass) {
                upLat = 10;
            } else {
                switch (to) {
                case UT_COUPLED_UDP: upLat = 3; break;
                case UV_COUPLED_SCD: case UV_COUPLED_FMA: case UV_COUPLED_ALU: upLat = 5; break;
                default: upLat = 10; break;
                }
            }
        } else {
            upLat = 9;
        }
    }
    lat = std::max(lat, upLat);
    int urLat = -1;
    if (UR) {
        switch (from) {
        case UT_COUPLED_UDP:
            if (is_udp_move(fop)) {
                urLat = (to == UT_COUPLED_UDP && top == SOP_SM73_ULDC) ? 4 : 1;
            } else {
                switch (to) {
                case UT_COUPLED_UDP:
                    urLat = top == SOP_SM73_ULDC ? 11 : top == SOP_SM73_UMOV ? 6 : 3;
                    break;
                case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_SCD:
                    urLat = 5;
                    break;
                default:
                    urLat = 8;
                    break;
                }
            }
            break;
        case UV_DECOUPLED_SM: case UV_DECOUPLED_MEM:
            urLat = 0;
            break;
        default:
            urLat = 4;
            break;
        }
    }
    return std::max(lat, urLat);
}

int hazard(const SInst &fi, const SInst &ti, int mask, bool checkBypass) {
    bool UP = has(mask, RC_UP), UR = has(mask, RC_UR), R = has(mask, RC_R), P = has(mask, RC_P);
    int from = unit(fi), to = unit(ti), fop = sop(fi), top = sop(ti);
    bool bypass = checkBypass && (!no_pred_bypass(ti) || (from == to && (redirected(ti) || unit_is_fp16(to))));
    int rLat = -1, pLat = -1, lat = -1;
    if (R || P) {
        switch (from) {
        case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_SCD:
            if (P) pLat = !bypass ? A_NOBYPASS_P_RAW : from == to ? 0 : A_ALU_FMA_RAW;
            if (R) {
                switch (to) {
                case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_SCD: case UV_COUPLED_FP16:
                    rLat = from == to ? 0 : from == UV_COUPLED_SCD ? A_SCD_RAW : A_ALU_FMA_RAW;
                    break;
                case UA_COUPLED_HFMA2_MMA: case UV_REDIRECTED_FMA64: case UA_REDIRECTED_CLMAD:
                    rLat = A_SCD_RAW;
                    break;
                case UV_DECOUPLED_CBU: case UV_DECOUPLED_SM:
                    rLat = 0;
                    break;
                case UV_DECOUPLED_MEM:
                    rLat = A_COUPLED_TO_DECOUPLED_MEM_RAW;
                    break;
                default:
                    rLat = unit_is_mma(to) ? A_COUPLED_TO_IMMA_DMMA_RAW : A_ALU_FMA_RAW;
                    break;
                }
            }
            lat = std::max(rLat, pLat);
            break;
        case UV_COUPLED_FP16:
            if (R) {
                if (to == UA_COUPLED_HFMA2_MMA) rLat = A_FP16_TO_REDIRECTED_RAW;
                else if (from == to || to == UV_DECOUPLED_SM || to == UV_DECOUPLED_CBU) rLat = 0;
                else if (coupled(ti)) rLat = A_FP16_TO_COUPLED_RAW;
                else if (to == UV_DECOUPLED_MEM) rLat = A_COUPLED_TO_DECOUPLED_MEM_RAW;
                else rLat = A_FP16_TO_REDIRECTED_RAW;
            }
            if (P) pLat = !bypass ? A_NOBYPASS_P_RAW : A_FP16_TO_COUPLED_RAW;
            lat = std::max(rLat, pLat);
            break;
        case UA_COUPLED_HFMA2_MMA: case UV_REDIRECTED_FMA64: case UA_REDIRECTED_CLMAD:
            if (P && from != UA_REDIRECTED_CLMAD) {
                if (bypass || (to != from && (to == UA_COUPLED_HFMA2_MMA || to == UV_REDIRECTED_FMA64)))
                    pLat = 0;
                else
                    pLat = A_FMA64_NOBYPASS_P_RAW;
            }
            if (R) {
                if (to == from || to == UV_DECOUPLED_SM || to == UV_DECOUPLED_CBU ||
                    (from == UA_COUPLED_HFMA2_MMA && to == UV_REDIRECTED_FMA64))
                    rLat = 0;
                else if (to == UV_DECOUPLED_MEM)
                    rLat = A_COUPLED_TO_DECOUPLED_MEM_RAW;
                else
                    rLat = A_FMA64_RAW;
            }
            lat = std::max(rLat, pLat);
            break;
        case UT_REDIRECTED_HMMA_1688: case UT_REDIRECTED_HMMA_16816:
            if (to == UV_DECOUPLED_SM || to == UV_DECOUPLED_CBU) lat = 0;
            else if (to == UV_DECOUPLED_MEM) lat = A_COUPLED_TO_DECOUPLED_MEM_RAW;
            else lat = from == UT_REDIRECTED_HMMA_1688 ? A_HMMA1688_RAW : A_HMMA16816_RAW;
            break;
        case UA_REDIRECTED_DMMA:
            if (to == UV_DECOUPLED_SM || to == UV_DECOUPLED_CBU) lat = A_DMMA_TO_DECOUPLED_RAW;
            else if (to == UV_DECOUPLED_MEM) lat = A_DMMA_TO_DECOUPLED_MEM_RAW;
            else lat = A_DMMA_RAW;
            break;
        case UV_DECOUPLED_SM: case UV_DECOUPLED_MEM: case UV_DECOUPLED_CBU: case UT_DECOUPLED_TTU:
        case UA_DECOUPLED_GMMA:
            lat = 0;
            break;
        default:
            break;
        }
    }
    int upLat = -1;
    if (UP && (top == SOP_SM70_BRA || top == SOP_SM70_JMP) && from == UT_COUPLED_UDP)
        upLat = fop == SOP_SM73_VOTEU ? A_VOTEU_TO_BRA_RAW : A_UDP_TO_BRA_RAW;
    lat = std::max(lat, upLat);
    int urLat = -1;
    if (UR && to == UA_REDIRECTED_CLMAD && from == UT_COUPLED_UDP)
        urLat = is_udp_move(fop) ? A_VOTEU_TO_BRA_RAW : A_UDP_TO_BRA_RAW;
    lat = std::max(lat, urLat);
    if (lat == -1) lat = hazard_turing(fi, ti, mask, checkBypass);
    if (R && !UR && !UP && !decoupled(fi) && unit_is_mma(to) && from != UT_REDIRECTED_HMMA_1688 &&
        from != UT_REDIRECTED_HMMA_16816)
        lat++;
    return lat;
}

int adjust_sm70(const SInst &f, const SInst &t, int mask, int lat) {
    (void)mask;
    if (sop(f) == SOP_SM70_IMAD_WIDE && coupled(t)) {
        lat += sop(t) == SOP_SM70_IMAD_WIDE ? 4 : 2;
        return lat - IMAD_WIDE_DISPATCH_STALL;
    }
    if (sop(f) == SOP_SM70_R2P && unit(t) == UV_COUPLED_ALU) return std::max(lat, 5);
    return lat;
}

int adjust_turing(const SInst &f, const SInst &t, int mask, int lat) {
    bool UP = has(mask, RC_UP), UR = has(mask, RC_UR);
    int nl = lat;
    if (!UP && !UR) nl = adjust_sm70(f, t, mask, lat);
    if (UP || UR) {
        if (sop(t) == SOP_SM73_ULDC) nl = std::max(nl, lat);
        else if (bindless_opd_dependent(f, t)) nl = std::max(nl, lat + (is_udp_move(sop(f)) ? 3 : 6));
    }
    return nl;
}

int adjust(const SInst &f, const SInst &t, int mask, int lat) {
    int nl = adjust_turing(f, t, mask, lat);
    if (unit(f) == UT_COUPLED_UDP && unit(t) == UV_DECOUPLED_CBU && mask == (1 << RC_UR))
        nl = std::max(nl, lat + 1);
    if (unit(f) == UV_COUPLED_FP16 && unit(f) == unit(t) &&
        (fp16_map_to_alu(sop(f)) != fp16_map_to_alu(sop(t)) || is_hadd2_f32(f) || is_hadd2_f32(t)) &&
        mask == (1 << RC_R))
        nl++;
    if (is_imma88(sop(f)) && unit_is_mma(unit(t)) && mask == (1 << RC_R)) nl++;
    return nl;
}

int output_decoupled(const SInst &f, const SInst &t, int mask) {
    if (same_ordered_vq(f, t)) return 1;
    return latency(f, &t, mask);
}

int output_turing(const SInst &f, const SInst &t, int mask) {
    bool UP = has(mask, RC_UP), UR = has(mask, RC_UR), P = has(mask, RC_P), R = has(mask, RC_R);
    int fu = unit(f), tu = unit(t);
    bool W = g_lat.wawTransitivity;
    bool toWide = sop(t) == SOP_SM70_IMAD_WIDE;
    int lat = -1, rLat = -1;
    if (R) {
        switch (fu) {
        case UV_REDIRECTED_IMMA:
            switch (tu) {
            case UV_COUPLED_ALU: case UV_COUPLED_FMA: rLat = toWide && W ? 8 : W ? 6 : 5; break;
            case UV_COUPLED_SCD: rLat = 5; break;
            case UV_COUPLED_FP16: rLat = W ? 4 : 3; break;
            case UV_REDIRECTED_IMMA: rLat = 1; break;
            case UV_REDIRECTED_HMMA16: case UV_REDIRECTED_HMMA32: rLat = W ? 6 : 2; break;
            default: rLat = 2; break;
            }
            break;
        case UT_REDIRECTED_HMMA_16816:
            switch (tu) {
            case UV_COUPLED_ALU: case UV_COUPLED_FMA: rLat = toWide && W ? 20 : W ? 18 : 17; break;
            case UV_COUPLED_SCD: rLat = 17; break;
            case UV_COUPLED_FP16: rLat = W ? 16 : 15; break;
            case UV_REDIRECTED_HMMA16: case UV_REDIRECTED_HMMA32: rLat = W ? 18 : 16; break;
            case UV_REDIRECTED_IMMA: rLat = W ? 18 : 14; break;
            case UT_REDIRECTED_HMMA_1688: rLat = 16; break;
            case UT_REDIRECTED_HMMA_16816: rLat = 1; break;
            default: rLat = 14; break;
            }
            break;
        case UT_REDIRECTED_HMMA_1688:
            switch (tu) {
            case UV_COUPLED_ALU: case UV_COUPLED_FMA: rLat = toWide && W ? 12 : W ? 10 : 9; break;
            case UV_COUPLED_SCD: rLat = 9; break;
            case UV_COUPLED_FP16: rLat = W ? 8 : 7; break;
            case UV_REDIRECTED_HMMA16: case UV_REDIRECTED_HMMA32: case UV_REDIRECTED_IMMA:
                rLat = W ? 10 : 6;
                break;
            case UT_REDIRECTED_HMMA_1688: rLat = 1; break;
            default: rLat = 6; break;
            }
            break;
        default:
            rLat = decoupled(f) ? output_decoupled(f, t, mask) : latency(f, &t, mask);
            break;
        }
    }
    lat = std::max(lat, rLat);
    int pLat = -1;
    if (P) pLat = decoupled(f) ? output_decoupled(f, t, mask) : latency(f, &t, mask);
    lat = std::max(lat, pLat);
    int urLat = -1;
    if (UR) {
        switch (fu) {
        case UT_COUPLED_UDP:
            if (is_udp_move(sop(f))) {
                urLat = tu == UV_DECOUPLED_MEM ? 4 : 1;
            } else if (tu == UT_COUPLED_UDP) {
                urLat = is_udp_move(sop(t)) ? 7 : 1;
            } else if (tu == UV_DECOUPLED_MEM) {
                urLat = W ? 10 : 4;
            } else {
                urLat = 1;
            }
            break;
        case UV_DECOUPLED_MEM: urLat = 2; break;
        default: urLat = 1; break;
        }
    }
    lat = std::max(lat, urLat);
    int upLat = -1;
    if (UP) upLat = (sop(t) == SOP_SM73_VOTEU && sop(f) != SOP_SM73_VOTEU) ? 7 : 1;
    lat = std::max(lat, upLat);
    return std::max(lat, 1);
}

int anti_hazard_sm70(const SInst &f, const SInst &t) {
    int fu = unit(f), tu = unit(t);
    if (tu == UV_COUPLED_ALU || tu == UV_COUPLED_FMA) return 0;
    if (fu == UV_COUPLED_SCD) return 0;
    switch (fu) {
    case UV_REDIRECTED_FMA64: case UV_COUPLED_FP16: case UV_REDIRECTED_HMMA16: case UV_REDIRECTED_HMMA32:
    case UV_REDIRECTED_IMMA:
        return fu == tu ? 0 : 2;
    case UV_COUPLED_ALU: case UV_COUPLED_FMA:
        return 2;
    default:
        return 0;
    }
}

int anti_hazard_turing(const SInst &f, const SInst &t, int mask) {
    int lat = -1;
    bool UP = has(mask, RC_UP), UR = has(mask, RC_UR), P = has(mask, RC_P);
    int fu = unit(f), tu = unit(t);
    if (!UP && !UR) {
        switch (fu) {
        case UT_DECOUPLED_TTU: lat = 0; break;
        case UT_REDIRECTED_HMMA_16816: case UT_REDIRECTED_HMMA_1688: {
            bool big = fu == UT_REDIRECTED_HMMA_16816;
            if (P) lat = 0;
            else if (coupled(t) && !unit_is_fp16(tu)) lat = big ? 13 : 5;
            else if (fu == tu) lat = 0;
            else lat = big ? 14 : 6;
            break;
        }
        case UT_COUPLED_UDP:
            switch (tu) {
            case UV_REDIRECTED_FMA64: case UV_COUPLED_FP16: case UV_DECOUPLED_CBU: case UV_DECOUPLED_MEM:
            case UV_DECOUPLED_SM: case UT_DECOUPLED_TTU:
                lat = 2;
                break;
            default:
                lat = 0;
                break;
            }
            break;
        default:
            break;
        }
    }
    if (lat == -1) lat = anti_hazard_sm70(f, t);
    return lat;
}

int anti_hazard(const SInst &f, const SInst &t, int mask) {
    int lat = -1;
    int fu = unit(f), tu = unit(t);
    bool R = has(mask, RC_R), P = has(mask, RC_P);
    if (R || P) {
        switch (fu) {
        case UV_COUPLED_ALU: case UV_COUPLED_SCD: case UV_COUPLED_FMA:
            if (unit_is_mma(tu) || decoupled(t)) {
                if (R) lat = A_COUPLED_TO_NON_COUPLED_WAR;
                if (P) lat = std::max(lat, 0);
                break;
            }
            switch (tu) {
            case UV_COUPLED_FP16: case UA_COUPLED_HFMA2_MMA: case UV_REDIRECTED_FMA64: lat = 0; break;
            case UA_REDIRECTED_CLMAD: lat = A_COUPLED_TO_NON_COUPLED_WAR; break;
            default: break;
            }
            break;
        case UV_COUPLED_FP16: case UA_COUPLED_HFMA2_MMA:
            if (R && (tu == UA_REDIRECTED_CLMAD || unit_is_mma(tu) || decoupled(t))) {
                lat = A_COUPLED_TO_NON_COUPLED_WAR;
                break;
            }
            lat = 0;
            break;
        case UV_REDIRECTED_FMA64: case UA_REDIRECTED_CLMAD: case UT_REDIRECTED_HMMA_1688:
        case UA_REDIRECTED_DMMA:
            lat = 0;
            break;
        case UT_REDIRECTED_HMMA_16816:
            lat = R && (coupled(t) || tu == UV_DECOUPLED_CBU) ? A_HMMA16816_TO_COUPLED_WAR : 0;
            break;
        case UA_DECOUPLED_GMMA:
            lat = 0;
            break;
        default:
            break;
        }
    }
    if (lat == -1) lat = anti_hazard_turing(f, t, mask);
    return lat;
}

int anti_adjust(const SInst &f, const SInst &t, int mask, int lat) {
    bool UP = has(mask, RC_UP), UR = has(mask, RC_UR), R = has(mask, RC_R), P = has(mask, RC_P);
    if (UP || UR) {
        if (!UR && UP && sop(t) == SOP_SM73_VOTEU && sop(f) != SOP_SM73_ULDC) return 2;
        if (UR && !UP && has_u_def_only(f) && sop(f) != SOP_SM73_UMOV && sop(f) != SOP_SM73_ULDC &&
            (sop(t) == SOP_SM73_VOTEU || sop(t) == SOP_SM73_UMOV || sop(t) == SOP_SM73_ULDC))
            return 3;
        return 0;
    }
    if (unit(f) == UV_COUPLED_ALU && no_pred_bypass(f)) return 0;
    if (!R && P && f.pred >= 0 && !non_guard_pred_dependent(t, f)) return 0;
    return lat;
}

int anti_sb_latency(const SInst &f, const SInst &t) {
    if (!has_sb_reg_anti_dep(f, t)) return 0;
    if (same_ordered_vq(f, t)) return 0;
    if (coupled(f)) return 0;
    return read_sb_latency(f);
}

}

const SInst &eb_inst() {
    static SInst eb;
    static bool init = false;
    if (!init) {
        eb = SInst();
        eb.sc.sop = SOP_SM70_LAST;
        eb.sc.unit = UNIT_NONE;
        eb.pred = -1;
        eb.rdSB = eb.wrSB = -1;
        init = true;
    }
    return eb;
}

bool same_ordered_vq(const SInst &a, const SInst &b) {
    return a.sc.vq == b.sc.vq && a.sc.vq >= VQ_ORDERED_FIRST && a.sc.vq <= VQ_ORDERED_LAST;
}

bool has_sb_reg_anti_dep(const SInst &from, const SInst &to) {
    for (int i = 0; i < from.nregs; i++) {
        const SReg &u = from.regs[i];
        if (u.def || u.cls != RC_R) continue;
        for (int j = 0; j < to.nregs && to.regs[j].def; j++)
            if (to.regs[j].cls == u.cls && to.regs[j].no == u.no) return true;
    }
    return false;
}

int latency(const SInst &from, const SInst *to, int mask) {
    if (from.flags & GF_IS_TEX_BATCH) return g_lat.texDefaultLatency;
    if (from.flags & GF_IS_LONG_LAT_MEM_READ) return g_lat.readDefaultLatency;
    int lat = from.sc.latency;
    if (!to) {
        g_latency_worst_calls++;
        return lat + max_penalty(from);
    }
    bool bypass = dep_predicate_is_subset(from, *to) && !guard_pred_dependent(from, *to);
    lat += hazard(from, *to, mask, bypass);
    return adjust(from, *to, mask, lat);
}

int output_dep_latency(const SInst &f, const SInst &t, int mask) {
    bool UR = has(mask, RC_UR), P = has(mask, RC_P), R = has(mask, RC_R);
    int fu = unit(f), tu = unit(t);
    bool W = g_lat.wawTransitivity;
    bool toWide = sop(t) == SOP_SM70_IMAD_WIDE, fromWide = sop(f) == SOP_SM70_IMAD_WIDE;
    bool toF32 = is_hadd2_f32(t);
    int rLat = -1, pLat = -1;
    if (R || P) {
        switch (fu) {
        case UV_COUPLED_SCD: case UV_COUPLED_ALU: case UV_COUPLED_FMA:
            if (toWide) {
                if (P) pLat = A_COUPLED_TO_COUPLED_WAW;
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW +
                              (W ? (fu == UV_COUPLED_ALU ? 2 : fu == UV_COUPLED_SCD ? 3 : 1) : 0);
            } else if (fromWide && tu == UV_COUPLED_FMA) {
                rLat = A_COUPLED_TO_COUPLED_WAW + (W ? 1 : 0);
            } else if (fu == UV_COUPLED_SCD && (tu == UV_COUPLED_ALU || tu == UV_COUPLED_FMA)) {
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW + (W ? 1 : 0);
            } else if (tu == UV_COUPLED_FP16) {
                if (P) pLat = A_COUPLED_TO_NON_COUPLED_WAW + (W ? 6 : 0);
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW + (fu == UV_COUPLED_SCD && !toF32 && W ? 1 : 0);
            } else if (tu == UA_COUPLED_HFMA2_MMA || tu == UV_REDIRECTED_FMA64) {
                if (P) pLat = A_COUPLED_TO_NON_COUPLED_WAW + (W ? 5 : 0);
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW;
            } else if (tu == UA_REDIRECTED_CLMAD || unit_is_mma(tu)) {
                rLat = A_COUPLED_TO_NON_COUPLED_WAW;
            } else if (decoupled(t)) {
                if (P) pLat = A_COUPLED_TO_NON_COUPLED_WAW + (W ? 10 : 0);
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW + (W ? 5 : 0);
            } else {
                if (P) pLat = A_COUPLED_TO_COUPLED_WAW;
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW;
            }
            break;
        case UV_COUPLED_FP16:
            if (coupled(t) && !unit_is_fp16(tu)) {
                if (P) pLat = A_FP16_TO_COUPLED_WAW;
                if (R) rLat = A_FP16_TO_COUPLED_WAW + (toWide && W ? 2 : 0);
            } else if (tu == UV_COUPLED_FP16) {
                if (P) pLat = A_COUPLED_TO_COUPLED_WAW;
                if (R) rLat = A_COUPLED_TO_COUPLED_WAW;
            } else if (tu == UA_COUPLED_HFMA2_MMA || tu == UV_REDIRECTED_FMA64) {
                if (P) pLat = A_COUPLED_TO_NON_COUPLED_WAW + (W ? 5 : 0);
                if (R) rLat = A_FP16_FMA64_TO_NON_COUPLED_WAW;
            } else if (tu == UA_REDIRECTED_CLMAD || unit_is_mma(tu)) {
                rLat = A_COUPLED_TO_NON_COUPLED_WAW;
            } else {
                if (P) pLat = A_FP16_TO_NON_COUPLED_P_WAW + (W ? 10 : 0);
                if (R) rLat = A_FP16_FMA64_TO_NON_COUPLED_WAW + (W ? 5 : 0);
            }
            break;
        case UA_COUPLED_HFMA2_MMA: case UV_REDIRECTED_FMA64:
            if (coupled(t) && !unit_is_fp16(tu)) {
                if (P) pLat = A_FMA64_TO_COUPLED_P_WAW;
                if (R) {
                    if (toWide) rLat = A_FMA64_TO_IMAD_WAW + (W ? 3 : 0);
                    else if (tu == UV_COUPLED_SCD) rLat = A_FMA64_TO_COUPLED_WAW + (W ? 1 : 0);
                    else rLat = A_FMA64_TO_COUPLED_WAW + (W ? 3 : 0);
                }
            } else if (tu == UV_COUPLED_FP16) {
                if (P) pLat = A_FMA64_TO_COUPLED_P_WAW + (W ? 7 : 0);
                if (R) rLat = A_FMA64_TO_COUPLED_WAW + (W ? (toF32 ? 2 : 3) : 0);
            } else if (tu == UA_COUPLED_HFMA2_MMA) {
                if (P) pLat = A_FP16_FMA64_TO_NON_COUPLED_WAW;
                if (R) rLat = tu == fu ? A_COUPLED_TO_NON_COUPLED_WAW : A_FMA64_TO_COUPLED_WAW + (W ? 1 : 0);
            } else if (tu == UV_REDIRECTED_FMA64 || tu == UA_REDIRECTED_CLMAD) {
                if (P) pLat = A_FP16_FMA64_TO_NON_COUPLED_WAW;
                if (R) rLat = A_COUPLED_TO_NON_COUPLED_WAW;
            } else if (unit_is_mma(tu)) {
                rLat = A_COUPLED_TO_NON_COUPLED_WAW;
            } else {
                if (P) pLat = A_FP16_FMA64_TO_NON_COUPLED_WAW + (W ? 12 : 0);
                if (R) rLat = A_FP16_FMA64_TO_NON_COUPLED_WAW + (W ? 9 : 0);
            }
            break;
        case UA_REDIRECTED_CLMAD:
            if (tu == UV_COUPLED_FP16) rLat = A_FMA64_TO_IMAD_WAW + (W ? (toF32 ? 2 : 3) : 0);
            else if (tu == UA_COUPLED_HFMA2_MMA) rLat = A_FMA64_TO_IMAD_WAW + (W ? 1 : 0);
            else if (coupled(t))
                rLat = A_FMA64_TO_IMAD_WAW + (W ? (toWide ? 5 : tu == UV_COUPLED_SCD ? 1 : 3) : 0);
            else if (tu == UV_REDIRECTED_FMA64) rLat = A_CLMAD_TO_FMA64_WAW + (W ? 2 : 0);
            else if (tu == UA_REDIRECTED_CLMAD || unit_is_mma(tu)) rLat = A_COUPLED_TO_NON_COUPLED_WAW;
            else rLat = A_FP16_FMA64_TO_NON_COUPLED_WAW + (W ? 11 : 0);
            break;
        case UT_REDIRECTED_HMMA_1688: {
            bool i88 = is_imma88(sop(f));
            int cpl = i88 ? A_IMMA88_TO_COUPLED_WAW : A_HMMA1688_TO_COUPLED_WAW;
            int dcp = i88 ? A_IMMA88_TO_DECOUPLED_WAW : A_HMMA1688_TO_DECOUPLED_WAW;
            switch (tu) {
            case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_FP16:
                rLat = cpl + (toF32 ? 0 : toWide ? (W ? 3 : 0) : (W ? 1 : 0));
                break;
            case UV_COUPLED_SCD: case UA_COUPLED_HFMA2_MMA: rLat = cpl; break;
            case UV_REDIRECTED_FMA64: case UA_REDIRECTED_CLMAD: rLat = dcp; break;
            default:
                if (unit_is_mma(tu))
                    rLat = i88 ? A_IMMA88_TO_MMA_WAW
                               : A_HMMA1688_TO_MMA_WAW - (tu == UA_REDIRECTED_DMMA ? 1 : 0);
                else
                    rLat = dcp + (W ? (i88 ? 6 : 5) : 0);
                break;
            }
            break;
        }
        case UT_REDIRECTED_HMMA_16816:
            switch (tu) {
            case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_FP16:
                rLat = A_HMMA16816_TO_COUPLED_WAW + (toF32 ? 0 : toWide ? (W ? 3 : 0) : (W ? 1 : 0));
                break;
            case UV_COUPLED_SCD: case UA_COUPLED_HFMA2_MMA: rLat = A_HMMA16816_TO_COUPLED_WAW; break;
            case UV_REDIRECTED_FMA64: case UA_REDIRECTED_CLMAD: rLat = A_HMMA16816_TO_DECOUPLED_WAW; break;
            default:
                if (unit_is_mma(tu))
                    rLat = A_HMMA16816_TO_MMA_WAW - (tu == UA_REDIRECTED_DMMA ? 1 : 0);
                else
                    rLat = A_HMMA16816_TO_DECOUPLED_WAW + (W ? 5 : 0);
                break;
            }
            break;
        case UA_REDIRECTED_DMMA:
            switch (tu) {
            case UV_COUPLED_ALU: case UV_COUPLED_FMA: case UV_COUPLED_FP16:
                rLat = A_DMMA_TO_COUPLED_WAW + (toF32 ? 0 : toWide ? (W ? 3 : 0) : (W ? 1 : 0));
                break;
            case UV_COUPLED_SCD: case UA_COUPLED_HFMA2_MMA: rLat = A_DMMA_TO_COUPLED_WAW; break;
            case UV_REDIRECTED_FMA64: case UA_REDIRECTED_CLMAD: rLat = A_DMMA_TO_DECOUPLED_WAW; break;
            default:
                if (unit_is_mma(tu))
                    rLat = tu == UT_REDIRECTED_HMMA_1688 ? A_DMMA_TO_HMMA1688_WAW : A_DMMA_TO_MMA_WAW;
                else
                    rLat = A_DMMA_TO_DECOUPLED_WAW + (W ? 6 : 0);
                break;
            }
            break;
        default:
            break;
        }
    }
    int lat = std::max(pLat, rLat);
    int urLat = -1;
    if (UR) {
        if (fu == UT_COUPLED_UDP) {
            if (tu == UV_DECOUPLED_SM)
                urLat = A_UDP_TO_DECOUPLED_SM_WAW + (!is_udp_move(sop(f)) && W ? 7 : 0);
        } else if (fu == UV_DECOUPLED_SM) {
            urLat = 0;
        }
    }
    lat = std::max(lat, urLat);
    if (lat == -1) lat = output_turing(f, t, mask);
    return lat;
}

int anti_dep_latency(const SInst &from, const SInst &to, int mask) {
    int lat = anti_hazard(from, to, mask);
    lat = anti_adjust(from, to, mask, lat);
    return std::max(lat, anti_sb_latency(from, to));
}

int order_dep_latency(const SInst &from, const SInst &to, unsigned memDomainMask, bool tepid) {
    (void)to;
    const unsigned BAR_DOMAINS = 1u << MD_GENMEM | 1u << MD_SURF | 1u << MD_GMEM | 1u << MD_SMEM;
    if (tepid && from.sc.sop == SOP_SM70_BAR && bar_defer_blocking(from) &&
        (memDomainMask & BAR_DOMAINS))
        return from.sc.latency + g_lat.barSuppLatency;
    return 0;
}

int dep_latency(int depType, const SInst &from, const SInst &to, int mask, unsigned memDomainMask,
                bool tepid) {
    if (!tepid && decoupled(from) && depType != DEP_ORDER) return 0;
    switch (depType) {
    case DEP_FLOW: return latency(from, &to, mask);
    case DEP_OUTPUT: return output_dep_latency(from, to, mask);
    case DEP_ANTI: return anti_dep_latency(from, to, mask);
    default: return order_dep_latency(from, to, memDomainMask, tepid);
    }
}

int read_sb_latency(const SInst &ip) {
    if (redirected(ip)) return SCOREBOARD_RAW_DELAY;
    int lat = READ_SB_BASE_LATENCY;
    int n = 0;
    for (int k = ip.nregs - 1; k >= 0 && !ip.regs[k].def; k--)
        if (ip.regs[k].cls == RC_R) n++;
    lat += (n - 1) * 2;
    int vq = ip.sc.vq;
    if (vq == VQ_MUFU || vq == VQ_ADU || vq == VQ_TEX || vq == VQ_CBU) lat += 1;
    if (ip.sc.sop == SOP_SM70_SUST) lat += 2;
    if (ip.flags & GF_NEEDS_WRITE_SB) lat = std::min(lat, latency(ip, nullptr, 0));
    return lat;
}

int write_sb_latency(const SInst &ip) {
    if (redirected(ip)) return SCOREBOARD_RAW_DELAY;
    return latency(ip, nullptr, 0);
}

}
}
}
