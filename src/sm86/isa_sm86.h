
#ifndef UBERSPEC_ISA_SM86_H
#define UBERSPEC_ISA_SM86_H
#include "nvn2_control.h"

namespace sm86x {

inline u32 rd32(const std::vector<u8> &v, size_t off) {
    u32 x = 0;
    if (off + 4 <= v.size()) std::memcpy(&x, v.data() + off, 4);
    return x;
}
inline void wr32(std::vector<u8> &v, size_t off, u32 x) {
    if (off + 4 > v.size()) fail("control blob too small for offset %#zx", off);
    std::memcpy(v.data() + off, &x, 4);
}

#define NVN2_CTL(f) ((u32)offsetof(NVN2shaderControl, f))
}

int issue_cycles86(const std::vector<u8> &bc, u32 co);
void phase_b86(std::vector<u8> &bc, u32 co);
int inst_class86(const std::vector<u8> &bc, u32 co, int n, u8 *cls);

void schedule86(std::vector<u8> &bc, std::vector<u8> &ct);

int validate86(const std::vector<u8> &bc, u32 co, int *first);
int shader_type86(const std::vector<u8> &bc);

struct Sm86 {
    typedef sm86::Word Word;
    typedef sm86::RSet86 RSet;

    static bool empty(Word w) { return !w.lo && !w.hi; }
    static bool word_eq(Word a, Word b) { return a == b; }
    static bool word_less(Word a, Word b) {
        return a.hi != b.hi ? a.hi < b.hi : a.lo < b.lo;
    }

    static const int kCode = 0x80;
    static constexpr u32 kCtlHead = sizeof(NVN2shaderControl);
    static int nslots(u32 co) { return ((int)co - kCode) / 16; }
    template <typename T> static size_t slot_off(T k) { return (size_t)kCode + 16 * (size_t)k; }
    template <typename T> static Word read_word(const std::vector<u8> &bc, T k) {
        Word w;
        std::memcpy(&w.lo, bc.data() + slot_off(k), 8);
        std::memcpy(&w.hi, bc.data() + slot_off(k) + 8, 8);
        return w;
    }
    template <typename T> static void write_word(std::vector<u8> &bc, T k, Word w) {
        std::memcpy(bc.data() + slot_off(k), &w.lo, 8);
        std::memcpy(bc.data() + slot_off(k) + 8, &w.hi, 8);
    }
    static void read_slots(const std::vector<u8> &bc, u32 co, std::vector<int> &rel,
                           std::vector<Word> &q);
    static u32 const_off(const std::vector<u8> &ct) {
        return sm86x::rd32(ct, NVN2_CTL(mConstBufOffset));
    }
    static bool ctl_ok(const std::vector<u8> &ct) {
        return ct.size() >= kCtlHead && sm86x::rd32(ct, NVN2_CTL(magic)) == NVN_CONTROL_MAGIC;
    }

    static const int kPad = 1;
    static Word nop();
    static Word exit_word();
    static Word bra_self_word();
    static int mov_dst_field() { return 0; }
    static int mov_src_field() { return 1; }

    static Word make_mov(int d, int s);
    static Word make_mov_imm(int d, u32 k);

    static void pad(std::vector<Word> &out, std::vector<int> &oldof);
    static u32 assemble(const std::vector<u8> &bc, u32 co, const std::vector<Word> &out,
                        std::vector<u8> &obc, std::vector<u8> &ct);

    static void layout_check(u32 co, const char *who) {
        if (co % 256 == 0 && co >= (u32)kCode) return;
        if (who) fail("%s: constant offset %#x is not 256-byte aligned", who, co);
        fail("constant offset %#x is not 256-byte aligned", co);
    }
    static u32 emit_layout(const std::vector<u8> &hdr, const std::vector<Word> &words,
                           std::vector<u8> &blob, std::vector<u8> &bc,
                           std::vector<u8> &ct);

    static int decode_op(Word w) {
        sm86::Inst in;
        return sm86::decode(w, &in) ? in.op : 0;
    }

    static unsigned decode_props(Word w) {
        sm86::Inst in;
        return sm86::decode(w, &in) ? (unsigned)in.cls : 0xFFFFu;
    }
    static const char *op_name(int op) { return sm86::op_name(op); }
    static const OpSets &sets();
    static void du(Word q, int nm, unsigned pr, RSet &d, RSet &md, RSet &u);
    static void hex(Word w, char *buf, size_t n) {
        snprintf(buf, n, "%016llx%016llx", (unsigned long long)w.hi,
                 (unsigned long long)w.lo);
    }

    static int guard_pred(Word q);
    static int guard_inv(Word q);
    static bool guard_is_pt(Word q) { return guard_pred(q) == PT && !guard_inv(q); }
    static void set_guard(Word &q, int pred, int inv);
    static int pred_fields(Word q, int nm, unsigned pr, int *offs);
    static int pred_field(Word q, int off);
    static int pred_field_inv(Word q, int off);
    static void set_pred_field(Word &q, int off, int pn, int inv);
    static bool pred_field_live(int nm, int off) { (void)nm; (void)off; return true; }
    static bool pred_literal_ok(int nm) { (void)nm; return true; }
    static int spurious_pred(int nm, Word q) { (void)nm; (void)q; return -1; }

    static void fieldmap(Word q, int nm, unsigned pr, std::vector<Field> &out);
    static int field_index(int off) { return off >= 0 && off < FIELD_SLOTS ? off : -1; }
    static void set_field(Word &q, int off, int reg);
    static int field_reg(Word q, int off);
    static int dest_field() { return 0; }

    static int dest_reg(Word q);
    static int tex_src_fields(Word q, int nm, int *offs) {
        (void)q; (void)nm; (void)offs;
        return 0;
    }
    static void true_srcs(Word q, int nm, unsigned pr, std::set<int> &out);

    static bool cbuf_operand(Word q, int nm, int *bank, int *off);
    static void set_cbuf_operand(Word &q, int bank, int off);
    static int cbuf_dwords(Word q, int nm);
    static void fold_cbuf_operand(Word &q, int slot, int bank, int off) {
        (void)q; (void)slot; (void)bank; (void)off;
        fail("sm86: constant buffer operand folding is not implemented");
    }

    static bool cbuf_read(Word q, int nm, int *bank, int *off);
    static int ldc_bank(Word q);
    static bool ldc_plain(Word q, int nm, int *ra, int *off);
    static void set_lmem_off(Word &q, int off) {
        (void)q; (void)off;
        fail("sm86: local memory is not rewritten");
    }
    static int src_fields(Word q, int nm, unsigned pr, int *offs);
    static Word cse_base(Word q, const int *offs, int m);
    static void field_free_key(std::string &key, Word q, const std::vector<Field> &fm);

    static bool wide_dest(Word q, int nm);

    static bool reg_move(Word q, int nm, int *d, int *s);
    static bool prop_copy(Word q, int nm, int *d, int *s) { return reg_move(q, nm, d, s); }

    static int copy_form(Word q, bool *imad);
    static Word copy_flip(Word q);
    static bool cbuf_copy(Word q, int nm, int *d, int *bank, int *off);
    static void cbfold_regs(const ProgramT<Sm86> &p, int i, std::vector<int> &out) {
        (void)p; (void)i;
        out.clear();
    }
    static void lmem_access(Word q, int nm, int *areg, int32_t *off, int *w) {
        (void)q; (void)nm;
        *areg = RZ; *off = -1; *w = 0;
    }
    static bool tex_rw_ok(Word q, int nm) { (void)q; (void)nm; return false; }
    static int float_copy_src(Word q, const VMap &v) { (void)q; (void)v; return -1; }
    static bool reads_cc(const ProgramT<Sm86> &p) { (void)p; return false; }
    static const OpSet &dce_ops();

    static int cf_kind(int nm);

    static int cf_kind_q(Word q, int nm);

    static bool branch_cond(Word q, int nm, int *pn, int *inv);

    static bool lit_read(const ProgramT<Sm86> &p, int i, int key);

    static bool keep_fwd_jumps() { return true; }

    static bool defs_busy() { return true; }

    static bool early_cycles() { return false; }
    static bool make_bra(Word from, Word &out);
    static void fix_calls(std::vector<Word> &words);
    static int indirect_reg(Word q);
    static int indirect_slot(const ProgramT<Sm86> &p, int i, u32 a);
    static int branch_dest(Word q, int rel);
    static bool set_branch(Word &q, int from, int to);
    static void build_cfg(const ProgramT<Sm86> &p, bool seed_orphans, CFGraph &g);

    static Word make_stl(int off, int s) {
        (void)off; (void)s;
        fail("sm86: no local memory store template");
    }
    static Word make_ldl(int d, int off) {
        (void)d; (void)off;
        fail("sm86: no local memory load template");
    }
    static bool eq_but_field(Word a, Word b, int off);
    static bool sink_op(Word q, int nm);
    static bool tex_mask(Word q, int nm, TnShape &s) { (void)q; (void)nm; (void)s; return false; }
    static bool tex_mask_narrow(const TnShape &s, int keep, Word &q) {
        (void)s; (void)keep; (void)q;
        return false;
    }

    static int key_limit() { return sm86::KEY_COUNT; }
    static int reg_bank(int r) { return r & 1; }

    static int run_align() { return 4; }

    static int renumber_mode();

    static int tuple_align(int w) { return w <= 1 ? 1 : w == 2 ? 2 : w <= 4 ? 4 : 8; }

    static bool dest_overlap_ok(Word q, int nm);

    static bool occupancy_first() { return true; }

    static int occupancy_of(int regs) {
        int r = std::max(regs, 1);
        r = (r + 7) / 8 * 8;
        return std::min(48, 4 * (512 / r));
    }

    static u32 decl_regs(int maxreg) { return (u32)std::max(maxreg + 3, 4); }
    static u32 reg_count(const std::vector<u8> &ct) {
        return sm86x::rd32(ct, NVN2_CTL(mProgramRegNum));
    }
    static void set_reg_count(std::vector<u8> &ct, u32 n) {
        sm86x::wr32(ct, NVN2_CTL(mProgramRegNum), n);
    }
    static Word renumber_mask(Word q);
    static bool eq_outside(Word a, Word b, Word m) {
        return ((a.lo ^ b.lo) & ~m.lo) == 0 && ((a.hi ^ b.hi) & ~m.hi) == 0;
    }
    static int inst_class(const std::vector<u8> &bc, u32 co, int n, u8 *cls) {
        return inst_class86(bc, co, n, cls);
    }

    static int issue_cycles(const std::vector<u8> &bc, u32 co) { return issue_cycles86(bc, co); }
    static void phase_b(std::vector<u8> &bc, u32 co) { phase_b86(bc, co); }
    static void reorder(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps) {
        (void)bc; (void)ct; (void)memdeps;
    }
    static void fill_bubbles(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps,
                             int rounds) {
        (void)bc; (void)ct; (void)memdeps; (void)rounds;
    }
    static void sched_cache_clear() {}
    static void control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f);
    static void verify(const std::vector<u8> &bc, const std::vector<u8> &ct, bool run_v8,
                       GateResult &R, const std::vector<u8> *shipped_bc,
                       const std::vector<u8> *shipped_ct, const std::vector<u8> *ref_bc,
                       const std::vector<u8> *ref_ct);

    static size_t program_start() { return 0; }
    static int anticopy_sites(const ProgramT<Sm86> &p, const std::vector<u8> &bc, u32 co,
                              int n, int nreal, const std::vector<int> &wuse,
                              const std::vector<int> &wdef, int *slot, int *reg,
                              int *bs, int *be, int *cnt) {
        (void)p; (void)bc; (void)co; (void)n; (void)nreal; (void)wuse; (void)wdef;
        (void)slot; (void)reg; (void)bs; (void)be; (void)cnt;
        return 0;
    }

    static void exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out);
};

#endif
