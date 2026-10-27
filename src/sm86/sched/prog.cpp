
#include "prog.h"

#include <algorithm>
#include <cstring>
#include <vector>

namespace ub {
namespace sm86 {
namespace sched {

namespace {

int val_of(const Inst &i, const char *name, int64_t dflt) {
    int v = val_index(i.cls, name);
    return v < 0 ? (int)dflt : (int)get(i, v);
}

int g_bra = -2, g_exit, g_break, g_ret, g_brx, g_brxu, g_call, g_bar, g_nop, g_warpsync, g_s2r, g_s2ur;

void init_ops() {
    if (g_bra != -2) return;
    g_bra = op_id("BRA");
    g_exit = op_id("EXIT");
    g_break = op_id("BREAK");
    g_ret = op_id("RET");
    g_brx = op_id("BRX");
    g_brxu = op_id("BRXU");
    g_call = op_id("CALL");
    g_bar = op_id("BAR");
    g_nop = op_id("NOP");
    g_warpsync = op_id("WARPSYNC");
    g_s2r = op_id("S2R");
    g_s2ur = op_id("S2UR");
}

bool is_branch_op(int op) {
    return op == g_bra || op == g_exit || op == g_break || op == g_ret || op == g_brx ||
           op == g_brxu || op == g_call;
}

bool named(const Operand &o, const char *nm) { return o.name && !strcmp(o.name, nm); }

bool kind_class(int kind, int *cls, int *invariant) {
    switch (kind) {
    case O_GPR: *cls = RC_R; *invariant = 255; return true;
    case O_UR: *cls = RC_UR; *invariant = 63; return true;
    case O_PRED: *cls = RC_P; *invariant = 7; return true;
    case O_UPRED: *cls = RC_UP; *invariant = 7; return true;
    case O_BAR: *cls = RC_CB; *invariant = -1; return true;
    default: return false;
    }
}

void push(SInst *s, int cls, int no, bool def, int opd, bool first_def, int attr = 0) {
    if (s->nregs >= SINST_MAX_REGS) return;
    SReg &r = s->regs[s->nregs++];
    r.cls = (uint8_t)cls;
    r.def = def;
    r.opd = (uint8_t)opd;
    r.first_def = first_def;
    r.no = (int16_t)no;
    r.attr = (uint8_t)attr;
}

int pr_mask_of(const Operand *o, int n) {
    for (int k = 0; k < n; k++)
        if (o[k].kind == O_IMM && o[k].name && !strcmp(o[k].name, "Sb")) return (int)(o[k].imm & 0x7f);
    return -1;
}

void add_operand(SInst *s, const Operand &o, bool def, int opd, bool first_def, bool half_track,
                 int copies, int pr_mask, int attr) {
    if (o.kind == O_PR || o.kind == O_UPR) {
        int cls = o.kind == O_PR ? RC_P : RC_UP;
        for (int k = 0; k < 7; k++) {
            bool in_mask = pr_mask < 0 || ((pr_mask >> k) & 1);

            if (o.role == R_DEFUSE ? (def ? in_mask : !in_mask) : in_mask)
                push(s, cls, k, def, opd, first_def, attr);
        }
        return;
    }
    int cls, inv;
    if (!kind_class(o.kind, &cls, &inv)) return;

    if (o.kind == O_BAR && named(o, "cbu_state")) cls = RC_STATE;
    int n = o.nregs ? o.nregs : 1;
    for (int k = 0; k < n; k++) {
        int r = o.reg + k;
        if (r == inv) continue;
        for (int c = 0; c < copies; c++) {
            int a = attr | (k == 0 && c == 0 ? SR_BASE : 0);
            if (cls == RC_R && half_track) {
                push(s, cls, r << 1, def, opd, first_def, a);
                push(s, cls, r << 1 | 1, def, opd, first_def, a & ~SR_BASE);
            } else {
                push(s, cls, r, def, opd, first_def, a);
            }
        }
    }
}

int name_rank(const Operand &o, const char *const *order) {
    for (int k = 0; order[k]; k++)
        if (named(o, order[k])) return k;
    return 99;
}

template <class F> void stable_by(std::vector<int> &idx, F key) {
    std::stable_sort(idx.begin(), idx.end(), [&](int a, int b) { return key(a) < key(b); });
}

}

void build_sinst(const Word &w, int shader_type, bool half_track, SInst *s) {
    init_ops();
    memset(s, 0, sizeof *s);
    s->w = w;
    s->rdSB = s->wrSB = -1;
    s->pred = -1;
    decode(w, &s->in);
    s->ok = classify(s->in, shader_type, &s->sc);
    s->flags = s->sc.flags;
    if (s->in.cls < 0) return;

    Operand o[MAX_OPNDS];
    int n = operands(s->in, o, MAX_OPNDS);
    std::vector<int> defs, uses;
    for (int k = 0; k < n; k++) {
        if (o[k].role == R_DEF || o[k].role == R_DEFUSE) defs.push_back(k);
        if (o[k].role == R_USE || o[k].role == R_DEFUSE) uses.push_back(k);
    }
    int sop = s->sc.sop;
    int copies_def = 1, copies_use = 1;
    switch (sop) {
    case SOP_SM70_SEL: case SOP_SM70_FSEL: case SOP_SM73_USEL:

        stable_by(uses, [&](int k) { return named(o[k], "Pp") || named(o[k], "UPp") ? 0 : 1; });
        break;
    case SOP_SM70_SHF: case SOP_SM73_USHF: {
        static const char *const ord[] = {"Ra", "URa", "Rc", "URc", "Rb", "URb", nullptr};
        stable_by(uses, [&](int k) { return name_rank(o[k], ord); });
        break;
    }
    case SOP_SM70_STG: case SOP_SM70_STL: case SOP_SM70_STS: case SOP_SM70_ST: case SOP_SM70_RED:
    case SOP_SM70_ATOMG: case SOP_SM70_ATOMS: case SOP_SM70_ATOM: case SOP_SM70_SUST:
    case SOP_SM73_ISBEWR:

        stable_by(uses, [&](int k) { return o[k].parent >= 0 ? 1 : 0; });
        break;
    case SOP_SM70_TEX: case SOP_SM70_TLD: case SOP_SM70_TLD4: case SOP_SM70_TXD:
    case SOP_SM70_TMML: case SOP_SM70_TXQ: case SOP_SM73_FOOTPRINT:
        stable_by(defs, [&](int k) { return named(o[k], "Rd2") ? 1 : 0; });
        break;
    case SOP_SM70_BREAK:
        stable_by(uses, [&](int k) { return named(o[k], "Pp") ? 1 : 0; });
        break;
    case SOP_SM70_HADD2: case SOP_SM70_HFMA2: case SOP_SM70_HMUL2: case SOP_SM82_HMNMX2:
    case SOP_SM70_HSET2: case SOP_SM70_HSETP2:
        copies_def = 2;
        copies_use = 2;
        break;
    case SOP_SM73_F2FPACK:
        copies_def = 2;
        std::reverse(uses.begin(), uses.end());
        break;
    case SOP_SM70_POPC: case SOP_SM73_UPOPC:
        copies_use = 2;
        break;
    default:
        break;
    }
    int prm = pr_mask_of(o, n);
    int opd = 0;
    bool first = true;

    int op = s->in.op;
    int pre_cls = -1, pre_no = 0;
    if (op == g_bar) pre_cls = RC_STATE, pre_no = -1;
    else if (op == g_warpsync) pre_cls = RC_ACTIVEM, pre_no = 0;
    for (int k = 0; k < n; k++)
        if (named(o[k], "atexit_pc")) pre_cls = RC_STATE, pre_no = 30;
    if (pre_cls >= 0) {
        push(s, pre_cls, pre_no, true, opd++, true, SR_BASE);
        first = false;
    }
    for (int k : defs) {
        int cp = o[k].kind == O_GPR ? copies_def : 1;
        add_operand(s, o[k], true, opd++, first, half_track, cp, prm, 0);
        first = false;
    }
    for (int k : uses) {
        int cp = o[k].kind == O_GPR || o[k].kind == O_UR ? copies_use : 1;

        if (cp == 2 && o[k].kind == O_GPR) {
            const char *sw = named(o[k], "Ra") ? "iswzA" : named(o[k], "Rb") ? "iswzB" : "iswzB_as_C";
            if (val_of(s->in, sw, 0) != 0) cp = 1;
        }
        int attr = 0;
        if (o[k].kind == O_UR && o[k].parent >= 0 && o[o[k].parent].kind == O_UCBUF) attr |= SR_BINDLESS;
        if (is_branch_op(s->in.op) && named(o[k], "Pp")) attr |= SR_GUARD;
        add_operand(s, o[k], false, opd++, false, half_track, cp, prm, attr);
    }

    if (op == g_s2r || op == g_s2ur) {
        for (int k = 0; k < n; k++)
            if (o[k].kind == O_SREG && o[k].imm >= 0x25 && o[k].imm <= 0x27)
                push(s, RC_STATE, (int)(64 + o[k].imm - 0x25), false, opd++, false, SR_BASE);
    }

    bool uni = false, neg = false;
    int g = guard(s->in, &uni, &neg);
    if (g != 7) {

        push(s, uni ? RC_UP : RC_P, g, false, opd++, false, is_branch_op(op) ? SR_BASE : SR_GUARD | SR_BASE);
    }
    if (is_branch_op(s->in.op)) {
        g = val_of(s->in, "Pp", 7);
        neg = val_of(s->in, "Pp@not", 0) != 0;
        uni = false;
    }
    if (g != 7) {
        s->pred = (int8_t)g;
        s->pred_cls = uni ? RC_UP : RC_P;
        s->pred_cond = neg ? PRED_COND_FALSE : PRED_COND_TRUE;
    }
}

void nop_stand_in(SInst *s, bool lastInBlock, int shader_type) {
    if (!lastInBlock) {
        s->sc.sop = SOP_SM70_BAR;
        return;
    }
    Inst m;
    SchedClass c;
    if (!decode(Word{0x0000000000007992ull, 0x000fc00000002000ull}, &m) || !classify(m, shader_type, &c)) return;
    s->sc = c;
    s->flags = c.flags | (s->flags & ~CLASSIFY_FLAGS);
    s->ok = true;
}

bool bar_blocks(int cls) {
    switch (cls) {
    case 55:
    case 56:
    case 57:
    case 58:
    case 63:
    case 64:
    case 65:
    case 66:
    case 68:
    case 69:
    case 70:
    case 71:
    case 72:
        return true;
    default:
        return false;
    }
}

}
}
}
