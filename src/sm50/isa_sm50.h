
#ifndef UBERSPEC_ISA_SM50_H
#define UBERSPEC_ISA_SM50_H

void exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out);
int issue_cycles(const std::vector<u8> &bc, u32 co);
void phase_b(std::vector<u8> &bc, u32 co);
int occupancy_of(int regs);
u64 renumber_mask(u64 q);
struct CtlFacts;
struct GateResult;
void verify(const std::vector<u8> &bc, const std::vector<u8> &ct, bool run_v8, GateResult &R,
            const std::vector<u8> *shipped_bc, const std::vector<u8> *shipped_ct,
            const std::vector<u8> *ref_bc, const std::vector<u8> *ref_ct);
void reorder(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps);
void fill_bubbles(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps, int rounds);
void fill_cache_clear();
void control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f);

struct Sm50 {
    typedef u64 Word;
    typedef ub::RSet RSet;

    static bool empty(Word w) { return w == 0; }
    static bool word_eq(Word a, Word b) { return a == b; }
    static bool word_less(Word a, Word b) { return a < b; }

    static int nslots(u32 co) { return 3 * ((int)co - INSTR_START) / 32; }
    template <typename T> static size_t slot_off(T k) { return ub::slot_off(k); }
    template <typename T> static Word read_word(const std::vector<u8> &bc, T k) {
        Word w;
        std::memcpy(&w, bc.data() + ub::slot_off(k), 8);
        return w;
    }
    template <typename T> static void write_word(std::vector<u8> &bc, T k, Word w) {
        std::memcpy(bc.data() + ub::slot_off(k), &w, 8);
    }
    static void read_slots(const std::vector<u8> &bc, u32 co, std::vector<int> &rel,
                           std::vector<Word> &q);
    static u32 const_off(const std::vector<u8> &ct) { return ub::const_off(ct); }
    static bool ctl_ok(const std::vector<u8> &ct) {
        return ct.size() >= CONSTOFF_OFF + 4;
    }

    static const int kPad = 3;
    static Word nop() { return 0x50b0000000070f00ull; }
    static Word exit_word() { return 0xe30000000007000full; }
    static Word bra_self_word() { return 0xe2400fffff87000full; }

    static int mov_dst_field() { return 0; }
    static int mov_src_field() { return 20; }
    static Word make_mov(int d, int s) {
        return set_field8(set_field8(0x5c9807800ff70000ull, 0, d), 20, s);
    }

    static Word make_mov_imm(int d, u32 k) {
        return 0x010000000000F000ull | ((u64)PT << 16) | (u64)(d & 0xFF) | ((u64)k << 20);
    }
    static void pad(std::vector<Word> &out, std::vector<int> &oldof) {
        while (out.size() % 3) { out.push_back(nop()); oldof.push_back(-1); }
    }

    static u32 assemble(const std::vector<u8> &bc, u32 co, const std::vector<Word> &out,
                        std::vector<u8> &obc, std::vector<u8> &ct) {
        size_t blobsz = bc.size() - (size_t)co;
        size_t nb = out.size() / 3;
        u32 co2 = (u32)(INSTR_START + nb * 32);
        co2 = (co2 + CBUF_ALIGN - 1) / CBUF_ALIGN * CBUF_ALIGN;
        obc.assign((size_t)co2 + blobsz, 0);
        std::memcpy(obc.data(), bc.data(), INSTR_START);
        for (size_t k = 0; k < out.size(); k++)
            std::memcpy(obc.data() + ub::slot_off(k), &out[k], 8);
        if (blobsz) std::memcpy(obc.data() + co2, bc.data() + co, blobsz);
        NVNshaderControl *oc = ctl(ct);
        oc->mProgramSize = (u32)(SPH_SIZE + nb * 32);
        oc->mConstBufOffset = co2;
        oc->mShaderSize = (u32)obc.size();
        return co2;
    }
    static void layout_check(u32 co, const char *who) {
        int ns = nslots(co);
        if (ns % 24 == 12) return;
        if (who) fail("%s: padded instruction count %d is not 12 mod 24", who, ns);
        fail("padded instruction count %d is not 12 mod 24", ns);
    }

    static u32 emit_layout(const std::vector<u8> &hdr, const std::vector<Word> &words,
                           std::vector<u8> &blob, std::vector<u8> &bc,
                           std::vector<u8> &ct);

    static int decode_op(Word w) { return ub::decode_op(w); }
    static unsigned decode_props(Word w) { return ub::decode_props(w); }
    static const char *op_name(int op) { return ub::op_name(op); }
    static const OpSets &sets() { return S(); }
    static void du(Word q, int nm, unsigned pr, RSet &d, RSet &md, RSet &u);
    static void hex(Word w, char *buf, size_t n) {
        snprintf(buf, n, "%016llx", (unsigned long long)w);
    }

    static int guard_pred(Word q) { return _predf(q); }
    static int guard_inv(Word q) { return _pinv(q); }

    static bool guard_is_pt(Word q) { return ((q >> 16) & 0xF) == 7; }
    static void set_guard(Word &q, int pred, int inv) {
        q = (q & ~((u64)0xF << 16)) | ((u64)(pred & 7) << 16) | ((u64)(inv & 1) << 19);
    }

    static int pred_fields(Word q, int nm, unsigned pr, int *offs) {
        (void)q;
        return pred_src_offsets(nm, pr, offs);
    }
    static int pred_field(Word q, int off) { return (int)((q >> off) & 7); }
    static int pred_field_inv(Word q, int off) { return (int)((q >> (off + 3)) & 1); }
    static void set_pred_field(Word &q, int off, int pn, int inv) {
        q = setbits(q, off, 3, (u64)pn);
        q = setbits(q, off + 3, 1, (u64)inv);
    }

    static bool pred_field_live(int nm, int off) {
        if (S().pred39_spurious[(size_t)nm]) return false;
        return !(off == 39 && S().pred39_gpr[(size_t)nm]);
    }

    static bool pred_literal_ok(int nm) { return S().pred_src_ok[(size_t)nm]; }

    static int spurious_pred(int nm, Word q) { return ub::spurious_pred(nm, q); }

    static void fieldmap(Word q, int nm, unsigned pr, std::vector<Field> &out);

    static int field_index(int off) {
        switch (off) {
        case 0:  return 0;
        case 8:  return 1;
        case 20: return 2;
        case 28: return 3;
        case 39: return 4;
        default: return -1;
        }
    }
    static void set_field(Word &q, int off, int reg) { q = setbits(q, off, 8, (u64)reg); }

    static int field_reg(Word q, int off) { return (int)((q >> off) & 0xFF); }

    static int dest_field() { return 0; }
    static int dest_reg(Word q) { return (int)(q & 0xFF); }

    static int tex_src_fields(Word q, int nm, int *offs) {
        (void)q; (void)nm;
        offs[0] = 8;
        offs[1] = 20;
        return 2;
    }

    static void true_srcs(Word q, int nm, unsigned pr, std::set<int> &out);

    static bool cbuf_operand(Word q, int nm, int *bank, int *off) {
        const OpSets &T = S();
        if ((T.alu_cbuf[(size_t)nm] && srcb_form(q) == FORM_CBUF) ||
            (T.alu_cbuf_srcc[(size_t)nm] && srcc_form(q))) {
            *bank = cbuf_bank(q);
            *off = cbuf_off(q);
            return true;
        }
        return false;
    }
    static void set_cbuf_operand(Word &q, int bank, int off) {
        q = setbits(q, 34, 5, (u64)bank);
        q = setbits(q, 20, 14, (u64)(off >> 2));
    }

    static int cbuf_dwords(Word q, int nm) { (void)q; (void)nm; return 1; }

    static void fold_cbuf_operand(Word &q, int slot, int bank, int off) {
        if (slot == 39) {
            int rb = (int)((q >> 20) & 0xFF);
            q = set_field8(q, 39, rb);
            q = setbits(q, 59, 5, CBUF_SRCC_TOP5);
        } else {
            q = setbits(q, 59, 5, CBUF_SRCB_TOP5);
        }
        q = setbits(q, 20, 14, (u64)(off >> 2));
        q = setbits(q, 34, 5, (u64)bank);
    }

    static bool cbuf_read(Word q, int nm, int *bank, int *off) {
        return cbuf_read_of(q, nm, bank, off);
    }
    static int ldc_bank(Word q) { return ldc_fields(q).bank; }

    static bool ldc_plain(Word q, int nm, int *ra, int *off) {
        LdcFields f = ldc_fields(q);
        *ra = f.ra;
        *off = f.off;
        return f.mode == 0 && ((q >> 48) & 7) == 4 && mem_data_regs(q, nm) == 1;
    }
    static void set_lmem_off(Word &q, int off) {
        q = setbits(q, 20, 24, (u64)off & 0xFFFFFF);
    }

    static int src_fields(Word q, int nm, unsigned pr, int *offs) {
        return gpr_src_offsets(q, nm, pr, offs);
    }

    static Word cse_base(Word q, const int *offs, int m) {
        u64 mask = 0xFFull | (0xFull << 16);
        for (int k = 0; k < m; k++) mask |= 0xFFull << offs[k];
        return q & ~mask;
    }

    static void field_free_key(std::string &key, Word q, const std::vector<Field> &fm) {
        u64 mask = 0;
        for (const Field &f : fm) mask |= (u64)0xFF << f.off;
        long long x = (long long)(q & ~mask);
        key.append((const char *)&x, sizeof x);
    }

    static bool wide_dest(Word q, int nm) {
        return S().tex_bases[(size_t)nm] || nm == S().O_Shfl || mem_data_regs(q, nm) > 1;
    }

    static bool reg_move(Word q, int nm, int *d, int *s) {
        if (nm != S().O_Mov) return false;
        if (srcb_form(q) != FORM_REG) return false;
        if (((q >> 39) & 0xF) != 0xF) return false;
        *d = (int)(q & 0xFF);
        *s = (int)((q >> 20) & 0xFF);
        return true;
    }

    static bool prop_copy(Word q, int nm, int *d, int *s) {
        if (nm != S().O_Mov || srcb_form(q) != FORM_REG) return false;
        *d = (int)(q & 0xFF);
        *s = (int)((q >> 20) & 0xFF);
        return true;
    }

    static bool cbuf_copy(Word q, int nm, int *d, int *bank, int *off) {
        if (nm != S().O_Mov || srcb_form(q) != FORM_CBUF) return false;
        *d = (int)(q & 0xFF);
        *bank = cbuf_bank(q);
        *off = cbuf_off(q);
        return true;
    }

    static void cbfold_regs(const ProgramT<Sm50> &p, int i, std::vector<int> &out);

    static void lmem_access(Word q, int nm, int *areg, int32_t *off, int *w) {
        *areg = (int)((q >> 8) & 0xFF);
        *off = lmem_off(q);
        *w = mem_data_regs(q, nm);
    }

    static bool tex_rw_ok(Word q, int nm);

    static int float_copy_src(Word q, const VMap &v);

    static bool reads_cc(const ProgramT<Sm50> &p);

    static const OpSet &dce_ops();

    static int cf_kind(int nm) {
        const OpSets &T = S();
        if (nm == T.O_Ssy) return C_SSY;
        if (nm == T.O_Pbk) return C_PBK;
        if (nm == T.O_Pcnt) return C_PCNT;
        if (nm == T.O_Sync) return C_SYNC;
        if (nm == T.O_Brk) return C_BRK;
        if (nm == T.O_Cont) return C_CONT;
        if (nm == T.O_Bra || nm == T.O_Jmp) return C_BRA;
        if (nm == T.O_Brx || nm == T.O_Jmx) return C_BRX;
        if (nm == T.O_Exit || nm == T.O_Ret) return C_EXIT;
        return C_OTHER;
    }

    static int cf_kind_q(Word q, int nm) { (void)q; return cf_kind(nm); }

    static bool branch_cond(Word q, int nm, int *pn, int *inv) {
        (void)q; (void)nm; (void)pn; (void)inv;
        return false;
    }

    static bool lit_read(const ProgramT<Sm50> &p, int i, int key) {
        (void)p; (void)i; (void)key;
        return true;
    }

    static bool keep_fwd_jumps() { return false; }

    static bool defs_busy() { return true; }

    static bool early_cycles() { return true; }

    static bool make_bra(Word from, Word &out) { (void)from; (void)out; return false; }

    static void fix_calls(std::vector<Word> &words) { (void)words; }

    static int indirect_reg(Word q) { return (int)((q >> 8) & 0xFF); }

    static int indirect_slot(const ProgramT<Sm50> &p, int i, u32 a);

    static int branch_dest(Word q, int rel) { return rel + 8 + branch_imm(q); }

    static bool set_branch(Word &q, int from, int to) {
        int disp = ub::slot_rel(to) - (ub::slot_rel(from) + 8);
        if (!branch_disp_ok(disp)) return false;
        q = setbits(q, 20, 24, (u64)(u32)disp & 0xFFFFFF);
        return true;
    }
    static void build_cfg(const ProgramT<Sm50> &p, bool seed_orphans, CFGraph &g);

    static Word make_stl(int off, int s) {
        return 0xEF5400000007FF00ull | (u64)s | ((u64)off << 20);
    }
    static Word make_ldl(int d, int off) {
        return 0xEF4400000007FF00ull | (u64)d | ((u64)off << 20);
    }

    static bool eq_but_field(Word a, Word b, int off) {
        u64 m = ~((u64)0xFF << off);
        return (a & m) == (b & m);
    }

    static bool sink_op(Word q, int nm);

    static bool tex_mask(Word q, int nm, TnShape &s);

    static bool tex_mask_narrow(const TnShape &s, int keep, Word &q);

    static int key_limit() { return PREG + 8; }

    static int reg_bank(int r) { return r & 3; }

    static int run_align() { return 4; }

    static int renumber_mode() { return RN_DEFS; }
    static int tuple_align(int w) { (void)w; return run_align(); }
    static bool dest_overlap_ok(Word q, int nm) { (void)q; (void)nm; return false; }

    static bool occupancy_first() { return false; }

    static int occupancy_of(int regs) { return ub::occupancy_of(regs); }

    static u32 decl_regs(int maxreg) { return (u32)std::max(maxreg + 1, 4); }
    static u32 reg_count(const std::vector<u8> &ct) { return ctl(ct)->mProgramRegNum; }
    static void set_reg_count(std::vector<u8> &ct, u32 n) { ctl(ct)->mProgramRegNum = n; }

    static Word renumber_mask(Word q) { return ub::renumber_mask(q); }

    static bool eq_outside(Word a, Word b, Word m) { return (a & ~m) == (b & ~m); }

    static int inst_class(const std::vector<u8> &bc, u32 co, int n, u8 *cls);

    static int issue_cycles(const std::vector<u8> &bc, u32 co) {
        return ub::issue_cycles(bc, co);
    }
    static void phase_b(std::vector<u8> &bc, u32 co) { ub::phase_b(bc, co); }

    static void reorder(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps) {
        ub::reorder(bc, ct, memdeps);
    }
    static void fill_bubbles(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps,
                             int rounds) {
        ub::fill_bubbles(bc, ct, memdeps, rounds);
    }

    static void sched_cache_clear() { ub::fill_cache_clear(); }

    static void control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f) {
        ub::control_rewrite(bc, ct, f);
    }

    static void verify(const std::vector<u8> &bc, const std::vector<u8> &ct, bool run_v8,
                       GateResult &R, const std::vector<u8> *shipped_bc,
                       const std::vector<u8> *shipped_ct, const std::vector<u8> *ref_bc,
                       const std::vector<u8> *ref_ct) {
        ub::verify(bc, ct, run_v8, R, shipped_bc, shipped_ct, ref_bc, ref_ct);
    }

    static size_t program_start() { return (size_t)SPH_OFF; }

    static int anticopy_sites(const ProgramT<Sm50> &p, const std::vector<u8> &bc, u32 co,
                              int n, int nreal, const std::vector<int> &wuse,
                              const std::vector<int> &wdef, int *slot, int *reg,
                              int *bs, int *be, int *cnt);
    static void exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out) {
        ub::exit_live_regs(bc, out);
    }
};

typedef ProgramT<Sm50> Program;

inline int Sm50::indirect_slot(const Program &p, int i, u32 a) {
    (void)i;
    int j = p.snap((int)(a & M32));
    if (j < 0) return -1;
    int diff = p.rel[(size_t)j] - (int)(a & M32);
    return (diff == 0 || diff == 8) ? j : -1;
}

#endif
