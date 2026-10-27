
#include "../uber.h"
#include "../emit.h"
#include "../alloc.h"
#include <cstring>
#include <algorithm>

namespace ub {

namespace sm86x {

}

using sm86x::rd32;
using sm86x::wr32;

static OpSet make_opset86(std::initializer_list<const char *> names) {
    OpSet s((size_t)sm86::nops(), 0);
    for (const char *nm : names) {
        int id = sm86::op_id(nm);
        if (id >= 0) s[(size_t)id] = 1;
    }
    return s;
}

static int opid(const char *nm) { return sm86::op_id(nm); }

const OpSets &Sm86::sets() {
    static OpSets *g = nullptr;
    if (g) return *g;
    OpSets *s = new OpSets();
    int N = sm86::nops();

    s->no_dest = make_opset86({
        "BRA", "BRX", "BRXU", "JMP", "JMX", "JMXU", "BSYNC", "BSSY", "BREAK", "WARPSYNC",
        "EXIT", "RET", "KILL", "NOP", "MEMBAR", "DEPBAR", "BAR", "RED", "ST", "STG",
        "STL", "STS", "AST", "CALL", "YIELD", "ERRBAR", "PMTRIG", "NANOSLEEP", "INVALID"});
    s->no_pred = make_opset86({});
    s->store_ops = make_opset86({"ST", "STG", "STL", "STS", "AST", "RED"});
    s->widemem = make_opset86({"LDC", "LD", "LDG", "LDL", "LDS", "ST", "STG", "STL", "STS"});
    s->texs_fam = make_opset86({});
    s->tex_fam = make_opset86({"TEX", "TLD", "TLD4", "TMML", "TXQ", "TXD", "FOOTPRINT", "GATHER"});
    s->tex_bases = OpSet((size_t)N, 0);
    for (size_t i = 0; i < s->tex_bases.size(); i++)
        s->tex_bases[i] = (char)(s->texs_fam[i] || s->tex_fam[i]);

    s->setp_fam = make_opset86({"FSETP", "ISETP", "DSETP", "HSETP2", "UISETP"});
    s->pred39_list = make_opset86({});
    s->side_effect = make_opset86({
        "AST", "ST", "STG", "STS", "STL", "RED", "ATOM", "ATOMG", "ATOMS", "KILL", "EXIT",
        "RET", "CALL", "BAR", "MEMBAR", "ERRBAR", "OUT", "PIXLD", "SHFL", "VOTE", "VOTEU",
        "BSSY", "BSYNC", "BREAK", "WARPSYNC", "YIELD", "RTT", "SUST", "SUATOM", "SURED",
        "LDGSTS", "DEPBAR", "NANOSLEEP", "NANOTRAP", "PMTRIG", "BPT", "INVALID"});
    s->branchy = make_opset86({"BRA", "BRX", "BRXU", "JMP", "JMX", "JMXU"});

    s->pushy = make_opset86({});
    s->freebie = make_opset86({"NOP", "DEPBAR", "YIELD"});

    s->alu_cbuf = make_opset86({});
    s->alu_cbuf_srcc = make_opset86({});

    s->pure_cse = make_opset86({});
    s->alu_srcb = make_opset86({});
    s->imm32_ops = make_opset86({"MOV", "UMOV"});
    s->transparent = make_opset86({});
    s->pred_src_ok = make_opset86({});

    s->branchy_imm = make_opset86({"BRA", "JMP", "BSSY", "CALL"});
    s->pred39_spurious = make_opset86({});
    s->pred39_gpr = make_opset86({});

    s->spec_side_effect = s->side_effect;
    s->spec_control = make_opset86({
        "BRA", "BRX", "BRXU", "JMP", "JMX", "JMXU", "BSSY", "BSYNC", "BREAK", "WARPSYNC",
        "CALL", "RET", "NOP"});
    s->safe_ops = OpSet((size_t)N, 1);
    s->load_or_store = make_opset86({
        "LDL", "STL", "LDS", "STS", "LDG", "STG", "LD", "ST", "ATOM", "ATOMG", "ATOMS",
        "RED", "MEMBAR", "SULD", "SUST", "SUATOM", "SURED", "LDGSTS", "LDC"});
    s->global_store = make_opset86({"STG", "ST", "RED", "ATOM", "ATOMG", "SUST", "SURED", "SUATOM"});
    s->fp64 = make_opset86({"DADD", "DMUL", "DFMA", "DSETP", "DMMA"});
    s->local_ops = make_opset86({"LDL", "STL"});

    s->ctl_texs_fam = make_opset86({});
    s->ctl_tex_fam = s->tex_fam;
    s->ctl_tex_bindless = make_opset86({});
    s->rate_quarter = make_opset86({"MUFU", "I2FP", "F2I", "I2F", "F2F", "FRND"});
    s->rate_half = make_opset86({"DADD", "DMUL", "DFMA"});
    s->tex_ops_audit = s->tex_fam;

    auto id = [&](const char *nm) { return opid(nm); };
    s->O_Nop = id("NOP"); s->O_Mov = id("MOV"); s->O_Mov32i = -1; s->O_Ldc = id("LDC");
    s->O_Stl = id("STL"); s->O_Ldl = id("LDL"); s->O_Invalid = id("INVALID"); s->O_Shfl = id("SHFL");
    s->O_Bra = id("BRA"); s->O_Jmp = id("JMP"); s->O_Ssy = -1; s->O_Pbk = -1; s->O_Pcnt = -1;
    s->O_Cal = id("CALL"); s->O_Brx = id("BRX"); s->O_Jmx = id("JMX"); s->O_Sync = -1;
    s->O_Brk = -1; s->O_Cont = -1; s->O_Exit = id("EXIT"); s->O_Ret = id("RET"); s->O_Kil = id("KILL");
    s->O_Isetp = id("ISETP"); s->O_Psetp = -1; s->O_Iset = -1; s->O_Imnmx = id("IMNMX");
    s->O_Sel = id("SEL"); s->O_Shl = -1; s->O_Shr = -1; s->O_Iadd = -1; s->O_Iadd32i = -1;
    s->O_Lop = -1; s->O_Lop32i = -1; s->O_Fsetp = id("FSETP"); s->O_Fset = id("FSET");
    s->O_Fmnmx = id("FMNMX"); s->O_Pset = -1; s->O_Xmad = -1; s->O_Ffma = id("FFMA");
    s->O_Texs = -1; s->O_Ast = id("AST"); s->O_Iadd3 = id("IADD3"); s->O_Ald = id("ALD");
    s->O_Al2p = id("AL2P"); s->O_F2f = id("F2F"); s->O_F2i = id("F2I"); s->O_I2f = id("I2F");
    s->O_I2i = id("I2I"); s->O_Fadd = id("FADD"); s->O_Fmul = id("FMUL"); s->O_Ipa = id("IPA");
    s->O_P2r = id("P2R"); s->O_Vote = id("VOTE"); s->O_Votevtg = -1; s->O_Flo = id("FLO");
    s->O_Popc = id("POPC");

    g = s;
    return *g;
}

const OpSet &Sm86::dce_ops() {
    static OpSet allow;
    static bool init = false;
    if (!init) {
        init = true;

        allow = make_opset86({
            "MOV", "UMOV", "SEL", "USEL", "MUFU", "IPA", "S2R", "CS2R", "S2UR", "R2UR",
            "FADD", "FFMA", "FMUL", "FMNMX", "FSEL", "FSET", "FSETP",
            "IADD3", "UIADD3", "IMNMX", "ISETP", "UISETP", "IMAD", "UIMAD",
            "LOP3", "ULOP3", "PLOP3", "UPLOP3", "SHF", "USHF", "LEA", "ULEA",
            "I2F", "I2FP", "I2I", "F2F", "F2I", "F2FP", "F2IP", "PRMT", "UPRMT",
            "IABS", "FLO", "UFLO", "POPC", "UPOPC", "BREV", "UBREV", "SGXT", "USGXT",
            "BMSK", "UBMSK", "P2R", "R2P", "FRND", "FCHK", "LDC"});
    }
    return allow;
}

bool Sm86::sink_op(Word q, int nm) {
    static OpSet allow;
    static bool init = false;
    if (!init) {
        init = true;
        allow = make_opset86({
            "MOV", "SEL", "FSEL", "MUFU", "IPA", "FADD", "FFMA", "FMUL", "FMNMX", "FSET",
            "IADD3", "IMNMX", "IMAD", "LOP3", "SHF", "LEA", "PRMT", "I2F", "I2FP", "I2I",
            "F2F", "F2I", "F2FP", "FRND", "IABS", "HADD2", "HMUL2", "HFMA2", "LDC"});
    }
    if (nm < 0 || (size_t)nm >= allow.size() || !allow[(size_t)nm]) return false;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return false;
    if (nm == sets().O_Ldc) {
        int ra = sm86::val_index(in.cls, "Ra");
        if (ra >= 0 && sm86::get(in, ra) != RZ) return false;
    }
    if (nm == sets().O_Mov) {
        int pm = sm86::val_index(in.cls, "PixMaskU04");
        if (pm < 0 || sm86::get(in, pm) != 0xf) return false;
    }
    return true;
}

void Sm86::read_slots(const std::vector<u8> &bc, u32 co, std::vector<int> &rel,
                      std::vector<Word> &q) {
    for (u32 off = kCode; off + 16 <= co; off += 16) {
        rel.push_back((int)(off - kCode));
        Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);

        bool imad;
        if (copy_form(w, &imad) == 0 && imad) w = copy_flip(w);
        q.push_back(w);
    }
}

static Sm86::Word from_hex(const char *h) {
    Sm86::Word w;
    char a[17], b[17];
    std::memcpy(a, h, 16); a[16] = 0;
    std::memcpy(b, h + 16, 16); b[16] = 0;
    w.hi = (u64)strtoull(a, nullptr, 16);
    w.lo = (u64)strtoull(b, nullptr, 16);
    return w;
}
static void set_val(sm86::Inst &in, const char *name, int64_t x) {
    int vi = sm86::val_index(in.cls, name);
    if (vi < 0) fail("sm86 template: no value %s on class %d", name, in.cls);
    if (!sm86::set(in, vi, x)) fail("sm86 template: cannot set %s=%lld", name, (long long)x);
}

Sm86::Word Sm86::nop() {
    static Word w = from_hex("000fc000000000000000000000007918");
    return w;
}
Sm86::Word Sm86::exit_word() {

    static Word built = [] {
        Word t = from_hex("000fea0003800000000000000000094d");
        sm86::Inst in; sm86::decode(t, &in);
        set_val(in, "Pg", 7); set_val(in, "Pg@not", 0);
        return in.w;
    }();
    return built;
}
Sm86::Word Sm86::bra_self_word() {

    static Word built = [] {
        Word t = from_hex("000fea0003800000000000a000000947");
        sm86::Inst in; sm86::decode(t, &in);
        set_val(in, "Pg", 7); set_val(in, "Pg@not", 0);
        set_val(in, "Pp", 7); set_val(in, "Pp@not", 0);
        set_val(in, "sImm", -16);
        return in.w;
    }();
    return built;
}
Sm86::Word Sm86::make_mov(int d, int s) {
    Word t = from_hex("000fe40000000f000000001800167202");
    sm86::Inst in; sm86::decode(t, &in);
    set_val(in, "Pg", 7); set_val(in, "Pg@not", 0);
    set_val(in, "Rd", d); set_val(in, "Rb", s); set_val(in, "PixMaskU04", 0xf);
    return in.w;
}
Sm86::Word Sm86::make_mov_imm(int d, u32 k) {
    Word t = from_hex("000fe20000000f0040000000000a7802");
    sm86::Inst in; sm86::decode(t, &in);
    set_val(in, "Pg", 7); set_val(in, "Pg@not", 0);
    set_val(in, "Rd", d); set_val(in, "Sb", (int64_t)(int32_t)k); set_val(in, "PixMaskU04", 0xf);
    return in.w;
}

void Sm86::pad(std::vector<Word> &out, std::vector<int> &oldof) {

    size_t k = out.size();
    while (k > 0 && decode_op(out[k - 1]) == sets().O_Nop) k--;
    if (k > 0 && k < out.size() && k <= oldof.size()) {
        sm86::Inst in;
        int si = -1, pg = -1;
        if (sm86::decode(out[k - 1], &in) && in.op == sets().O_Bra) {
            si = sm86::val_index(in.cls, "sImm");
            pg = sm86::val_index(in.cls, "Pg");
        }
        if (si >= 0 && pg >= 0 && sm86::get(in, si) == -16 && sm86::get(in, pg) == 7) {
            out.resize(k);
            oldof.resize(k);
        }
    }

    int extra = 8 + (int)((8 - out.size() % 8) % 8);
    for (int i = 0; i < extra; i++) { out.push_back(nop()); oldof.push_back(-1); }
}

static u32 align_up(u32 x, u32 a) { return (x + a - 1) / a * a; }

u32 Sm86::assemble(const std::vector<u8> &bc, u32 co, const std::vector<Word> &out,
                   std::vector<u8> &obc, std::vector<u8> &ct) {
    size_t blobsz = bc.size() - (size_t)co;
    u32 code_end = (u32)(kCode + 16 * out.size());
    u32 co2 = align_up(code_end, 256);
    u32 total = align_up(co2 + (u32)blobsz, 256);
    obc.assign(total, 0);
    std::memcpy(obc.data(), bc.data(), kCode);
    for (size_t k = 0; k < out.size(); k++) {
        std::memcpy(obc.data() + kCode + 16 * k, &out[k].lo, 8);
        std::memcpy(obc.data() + kCode + 16 * k + 8, &out[k].hi, 8);
    }
    if (blobsz) std::memcpy(obc.data() + co2, bc.data() + co, blobsz);
    wr32(ct, NVN2_CTL(mProgramSize), code_end);
    wr32(ct, NVN2_CTL(mConstBufSize), (u32)blobsz);
    wr32(ct, NVN2_CTL(mConstBufOffset), co2);
    wr32(ct, NVN2_CTL(mShaderSize), total);
    return co2;
}

u32 Sm86::emit_layout(const std::vector<u8> &hdr, const std::vector<Word> &words,
                      std::vector<u8> &blob, std::vector<u8> &bc, std::vector<u8> &ct) {
    u32 code_end = (u32)(kCode + 16 * words.size());
    u32 co = align_up(code_end, 256);
    while (blob.size() % 256) blob.push_back(0);
    u32 total = align_up(co + (u32)blob.size(), 256);
    bc.assign(total, 0);
    std::memcpy(bc.data(), hdr.data(), kCode);
    for (size_t k = 0; k < words.size(); k++) {
        std::memcpy(bc.data() + kCode + 16 * k, &words[k].lo, 8);
        std::memcpy(bc.data() + kCode + 16 * k + 8, &words[k].hi, 8);
    }
    if (!blob.empty()) std::memcpy(bc.data() + co, blob.data(), blob.size());
    wr32(ct, NVN2_CTL(mProgramSize), code_end);
    wr32(ct, NVN2_CTL(mConstBufSize), (u32)blob.size());
    wr32(ct, NVN2_CTL(mConstBufOffset), co);
    wr32(ct, NVN2_CTL(mShaderSize), total);
    return co;
}

void Sm86::du(Word q, int nm, unsigned pr, RSet &d, RSet &md, RSet &u) {
    (void)nm; (void)pr;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) { d.clear(); md.clear(); u.clear(); return; }
    sm86::def_use_split(in, &d, &md, &u);
}

void Sm86::true_srcs(Word q, int nm, unsigned pr, std::set<int> &out) {
    (void)nm; (void)pr;
    out.clear();
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return;

    bool uni, neg;
    if (sm86::guard(in, &uni, &neg) != 7) {
        Word g = q;
        set_guard(g, PT, 0);
        if (!sm86::decode(g, &in)) return;
    }
    RSet d, md, u;
    sm86::def_use_split(in, &d, &md, &u);
    std::vector<int> v;
    u.list(v);
    for (int r : v) out.insert(r);
}

int Sm86::guard_pred(Word q) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return PT;
    bool uni, neg;
    int g = sm86::guard(in, &uni, &neg);
    if (g == 7) return PT;
    return uni ? 8 + g : g;
}
int Sm86::guard_inv(Word q) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return 0;
    bool uni, neg;
    sm86::guard(in, &uni, &neg);
    return neg ? 1 : 0;
}
void Sm86::set_guard(Word &q, int pred, int inv) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) fail("sm86 set_guard: word does not decode");
    bool uni;
    int gv = sm86::val_index(in.cls, "Pg");
    const char *nm = "Pg", *nnm = "Pg@not";
    if (gv < 0) { gv = sm86::val_index(in.cls, "UPg"); nm = "UPg"; nnm = "UPg@not"; uni = true; }
    else uni = false;
    if (gv < 0) {
        if (pred == PT && !inv) return;
        fail("sm86 set_guard: class %d has no guard field", in.cls);
    }
    int reg = pred == PT ? 7 : (pred >= 8 ? pred - 8 : pred);
    if ((pred >= 8) != uni && pred != PT)
        fail("sm86 set_guard: guard file mismatch on class %d", in.cls);
    if (!sm86::set(in, gv, reg)) fail("sm86 set_guard: cannot set %s=%d", nm, reg);
    int nv = sm86::val_index(in.cls, nnm);
    if (nv >= 0 && !sm86::set(in, nv, inv ? 1 : 0))
        fail("sm86 set_guard: cannot set %s", nnm);
    q = in.w;
}

int Sm86::pred_fields(Word q, int nm, unsigned pr, int *offs) {
    (void)nm; (void)pr;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return 0;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    int m = 0;
    for (int k = 0; k < n && m < 8; k++)
        if ((o[k].kind == sm86::O_PRED || o[k].kind == sm86::O_UPRED) &&
            (o[k].role == sm86::R_USE || o[k].role == sm86::R_DEFUSE))
            offs[m++] = 100 + k;
    return m;
}

static bool pred_at(const Sm86::Word &q, int off, sm86::Inst *in, sm86::Operand *op) {
    if (off < 100) return false;
    if (!sm86::decode(q, in)) return false;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(*in, o, sm86::MAX_OPNDS);
    int k = off - 100;
    if (k >= n) return false;
    *op = o[k];
    return op->kind == sm86::O_PRED || op->kind == sm86::O_UPRED;
}
int Sm86::pred_field(Word q, int off) {
    sm86::Inst in; sm86::Operand op;
    if (!pred_at(q, off, &in, &op)) return PT;
    if (op.reg == 7) return PT;
    return op.kind == sm86::O_UPRED ? 8 + (int)op.reg : (int)op.reg;
}
int Sm86::pred_field_inv(Word q, int off) {
    sm86::Inst in; sm86::Operand op;
    if (!pred_at(q, off, &in, &op)) return 0;
    return (op.flags & sm86::F_NOT) ? 1 : 0;
}
void Sm86::set_pred_field(Word &q, int off, int pn, int inv) {
    sm86::Inst in; sm86::Operand op;
    if (!pred_at(q, off, &in, &op)) fail("sm86 set_pred_field: no predicate at handle %d", off);
    int reg = pn == PT ? 7 : (pn >= 8 ? pn - 8 : pn);
    if (!sm86::set_reg(in, op, reg)) fail("sm86 set_pred_field: cannot set predicate");
    if (op.val >= 0) {

        const char *base = sm86::val_name(in.cls, op.val);
        char nnm[64];
        snprintf(nnm, sizeof nnm, "%s@not", base);
        int nv = sm86::val_index(in.cls, nnm);
        if (nv >= 0 && !sm86::set(in, nv, inv ? 1 : 0))
            fail("sm86 set_pred_field: cannot set %s", nnm);
        else if (nv < 0 && inv)
            fail("sm86 set_pred_field: %s has no inverter", base);
    }
    q = in.w;
}

static int gpr_op_index(const sm86::Inst &in, int rank, sm86::Operand *out) {
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    int r = 0;
    for (int k = 0; k < n; k++) {
        if (o[k].kind != sm86::O_GPR) continue;
        if (r == rank) { *out = o[k]; return k; }
        r++;
    }
    return -1;
}

void Sm86::fieldmap(Word q, int nm, unsigned pr, std::vector<Field> &out) {
    (void)nm; (void)pr;
    out.clear();
    sm86::Inst in;
    if (!sm86::decode(q, &in)) fail("sm86 fieldmap: word does not decode");
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    int rank = 0;
    for (int k = 0; k < n; k++) {
        if (o[k].kind != sm86::O_GPR) continue;
        int r = rank++;
        if (o[k].role == sm86::R_NONE || o[k].nregs == 0) continue;
        if (o[k].reg >= RZ) continue;
        if (r >= FIELD_SLOTS) fail("sm86 fieldmap: more than %d GPR operands", FIELD_SLOTS);
        Field f;
        f.off = r;
        f.base = (int)o[k].reg;
        f.w = o[k].nregs;
        f.kind = (o[k].role == sm86::R_DEF || o[k].role == sm86::R_DEFUSE) ? 'd' : 'u';
        out.push_back(f);
    }
}

void Sm86::set_field(Word &q, int off, int reg) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) fail("sm86 set_field: word does not decode");
    sm86::Operand op;
    if (gpr_op_index(in, off, &op) < 0) fail("sm86 set_field: no GPR operand at rank %d", off);
    if (!sm86::set_reg(in, op, reg)) fail("sm86 set_field: cannot set R%d at rank %d", reg, off);
    q = in.w;
}
int Sm86::field_reg(Word q, int off) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return RZ;
    sm86::Operand op;
    if (gpr_op_index(in, off, &op) < 0) return RZ;
    return (int)op.reg;
}
int Sm86::dest_reg(Word q) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return RZ;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    for (int k = 0; k < n; k++)
        if (o[k].kind == sm86::O_GPR && (o[k].role == sm86::R_DEF || o[k].role == sm86::R_DEFUSE))
            return (int)o[k].reg;
    return RZ;
}

int Sm86::src_fields(Word q, int nm, unsigned pr, int *offs) {
    (void)nm; (void)pr;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return 0;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    int rank = 0, m = 0;
    for (int k = 0; k < n && m < 10; k++) {
        if (o[k].kind != sm86::O_GPR) continue;
        int r = rank++;
        if (o[k].role == sm86::R_USE || o[k].role == sm86::R_DEFUSE) offs[m++] = r;
    }
    return m;
}

static Sm86::Word clear_ctl(Sm86::Word q) {

    q.hi &= ~(((u64)1 << (128 - 102)) - 1) << (102 - 64);
    return q;
}
Sm86::Word Sm86::cse_base(Word q, const int *offs, int m) {
    Word w = clear_ctl(q);
    for (int k = 0; k < m; k++) {

        sm86::Inst in;
        if (sm86::decode(w, &in)) {
            sm86::Operand op;
            if (gpr_op_index(in, offs[k], &op) >= 0 && sm86::set_reg(in, op, 0)) w = in.w;
        }
    }

    sm86::Inst in;
    if (sm86::decode(w, &in)) {
        sm86::Operand o[sm86::MAX_OPNDS];
        int n = sm86::operands(in, o, sm86::MAX_OPNDS);
        for (int k = 0; k < n; k++)
            if (o[k].kind == sm86::O_GPR &&
                (o[k].role == sm86::R_DEF || o[k].role == sm86::R_DEFUSE) &&
                sm86::set_reg(in, o[k], 0)) { w = in.w; break; }
    }
    return w;
}
void Sm86::field_free_key(std::string &key, Word q, const std::vector<Field> &fm) {
    (void)fm;
    Word w = clear_ctl(q);

    sm86::Inst in;
    if (sm86::decode(w, &in)) {
        sm86::Operand o[sm86::MAX_OPNDS];
        int n = sm86::operands(in, o, sm86::MAX_OPNDS);
        for (int k = 0; k < n; k++)
            if (o[k].kind == sm86::O_GPR && sm86::set_reg(in, o[k], 0)) w = in.w;
    }
    key.append((const char *)&w.lo, 8);
    key.append((const char *)&w.hi, 8);
}

bool Sm86::wide_dest(Word q, int nm) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return true;

    const OpSets &T = sets();
    if (T.tex_bases[(size_t)in.op]) return true;
    if (T.load_or_store[(size_t)in.op]) return true;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    for (int k = 0; k < n; k++)
        if (o[k].kind == sm86::O_GPR && o[k].nregs > 1) return true;

    return !dce_ops()[(size_t)in.op];
}

int Sm86::renumber_mode() {
    int m = RN_SPLIT | RN_ALIGN | RN_OVERLAP | RN_ORDERS | RN_REGS | RN_CHECK | RN_DEFS;
    return m;
}

bool Sm86::dest_overlap_ok(Word q, int nm) {
    (void)q;
    static OpSet allow;
    static bool init = false;
    if (!init) {
        init = true;

        allow = make_opset86({"TEX", "TLD", "TLD4", "TXD", "TXQ", "LDG", "LDC", "LDL", "LDS",
                              "SULD", "ALD", "SHFL", "MUFU", "F2I", "FRND", "I2F", "FLO",
                              "POPC"});
    }
    return nm >= 0 && (size_t)nm < allow.size() && allow[(size_t)nm];
}

bool Sm86::reg_move(Word q, int nm, int *d, int *s) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in) || in.op != opid("MOV")) return false;
    int pm = sm86::val_index(in.cls, "PixMaskU04");
    if (pm < 0 || sm86::get(in, pm) != 0xf) return false;
    int rb = sm86::val_index(in.cls, "Rb"), rd = sm86::val_index(in.cls, "Rd");
    if (rb < 0 || rd < 0) return false;
    *d = (int)sm86::get(in, rd);
    *s = (int)sm86::get(in, rb);
    return true;
}

struct CopyPair {
    int mov, imad;
    const char *mov_t, *imad_t;
    const char *src[3][2];
    int nsrc;
};
static const CopyPair kCopies[] = {
    {660, 503, "000fe40000000f000000001800167202",
     "000fe200078e000a000000ffff132224", {{"Rb", "Rc"}}, 1},
    {659, 505, "000fe20000000f003f00000000067802",
     "000fe200078e00ff40008102ff2d7424", {{"Sb", "Sc"}}, 1},
    {657, 501, "000fe20000000f0001c00d0000047a02",
     "000fe200078e00ff01c00c00ff297624",
     {{"Sb", "Sc"}, {"Sb_bank", "Sc_bank"}, {"Sb_addr", "Sc_addr"}}, 3},
};
static long long val_of(const sm86::Inst &in, const char *nm, long long dflt) {
    int v = sm86::val_index(in.cls, nm);
    return v >= 0 ? (long long)sm86::get(in, v) : dflt;
}

static int copy_kind(const sm86::Inst &in, bool *imad) {
    for (int k = 0; k < 3; k++) {
        if (in.cls == kCopies[k].mov) {
            *imad = false;
            return val_of(in, "PixMaskU04", 0) == 0xf ? k : -1;
        }
        if (in.cls != kCopies[k].imad) continue;
        *imad = true;
        char neg[16];
        snprintf(neg, sizeof neg, "%s@negate", kCopies[k].src[0][1]);
        bool ok = val_of(in, "Ra", -1) == RZ && val_of(in, "Rb", -1) == RZ &&
                  val_of(in, neg, 0) == 0 && val_of(in, "wide", 1) == 0;
        return ok ? k : -1;
    }
    return -1;
}
int Sm86::copy_form(Word q, bool *imad) {
    sm86::Inst in;
    return sm86::decode(q, &in) ? copy_kind(in, imad) : -1;
}
Sm86::Word Sm86::copy_flip(Word q) {
    sm86::Inst in;
    bool imad;
    if (!sm86::decode(q, &in)) return q;
    int k = copy_kind(in, &imad);
    if (k < 0) return q;
    const CopyPair &cp = kCopies[k];
    sm86::Inst out;
    sm86::decode(from_hex(imad ? cp.mov_t : cp.imad_t), &out);

    auto put = [&](const char *nm, long long x) {
        int v = sm86::val_index(out.cls, nm);
        return v >= 0 && (sm86::set(out, v, x) || sm86::set(out, v, (long long)(int32_t)x) ||
                          sm86::set(out, v, (long long)(u32)x));
    };
    bool ok = put("Pg", val_of(in, "Pg", 7)) && put("Pg@not", val_of(in, "Pg@not", 0)) &&
              put("Rd", val_of(in, "Rd", RZ)) &&
              put("usched_info", val_of(in, "usched_info", 0)) &&
              put("pm_pred", val_of(in, "pm_pred", 0));
    for (int s = 0; s < cp.nsrc && ok; s++)
        ok = put(cp.src[s][imad ? 0 : 1], val_of(in, cp.src[s][imad ? 1 : 0], 0));
    if (!imad) ok = ok && put("Ra", RZ) && put("Rb", RZ);
    else ok = ok && put("PixMaskU04", 0xf);
    if (!ok) return q;
    sm86::Ctl c = sm86::ctl_get(out.w), o = sm86::ctl_get(q);
    c.wr = o.wr; c.rd = o.rd; c.wait = o.wait; c.pm = o.pm;
    out.w = sm86::ctl_set(out.w, c);
    if (!sm86::decode(out.w, &out) || !sm86::ctl_valid(out)) return q;
    return out.w;
}
bool Sm86::cbuf_copy(Word q, int nm, int *d, int *bank, int *off) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in) || in.op != opid("MOV")) return false;
    int rd = sm86::val_index(in.cls, "Rd");
    int b = sm86::val_index(in.cls, "Sb_bank"), a = sm86::val_index(in.cls, "Sb_addr");
    if (rd < 0 || b < 0 || a < 0) return false;
    *d = (int)sm86::get(in, rd);
    *bank = (int)sm86::get(in, b);
    *off = (int)sm86::get(in, a);
    return true;
}

bool Sm86::cbuf_operand(Word q, int nm, int *bank, int *off) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return false;
    if (in.op == opid("LDC")) return false;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);

    for (int k = 0; k < n; k++) {
        if (o[k].kind != sm86::O_CBUF && o[k].kind != sm86::O_UCBUF) continue;
        int bi = -1, ai = -1; bool idx = false;
        for (int j = 0; j < n; j++) {
            if (o[j].parent != k) continue;
            if (o[j].kind == sm86::O_IMM && std::strstr(o[j].name, "bank")) bi = j;
            else if (o[j].kind == sm86::O_IMM && std::strstr(o[j].name, "addr")) ai = j;
            else if (o[j].kind == sm86::O_GPR || o[j].kind == sm86::O_UR) idx = true;
        }
        if (idx || bi < 0 || ai < 0) continue;
        *bank = (int)o[bi].imm;
        *off = (int)o[ai].imm;
        return true;
    }
    return false;
}
void Sm86::set_cbuf_operand(Word &q, int bank, int off) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) fail("sm86 set_cbuf_operand: no decode");
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    for (int k = 0; k < n; k++) {
        if (o[k].kind != sm86::O_CBUF && o[k].kind != sm86::O_UCBUF) continue;
        for (int j = 0; j < n; j++) {
            if (o[j].parent != k) continue;
            if (o[j].kind == sm86::O_IMM && std::strstr(o[j].name, "bank")) {
                if (!sm86::set(in, o[j].val, bank)) fail("sm86 set_cbuf_operand: bank");
            } else if (o[j].kind == sm86::O_IMM && std::strstr(o[j].name, "addr")) {
                if (!sm86::set(in, o[j].val, off)) fail("sm86 set_cbuf_operand: addr");
            }
        }
        q = in.w;
        return;
    }
    fail("sm86 set_cbuf_operand: no immediate cbuf operand");
}
int Sm86::cbuf_dwords(Word q, int nm) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return 1;

    int sz = sm86::val_index(in.cls, "sz");
    if (sz < 0) return 1;
    switch ((int)sm86::get(in, sz)) {
    case 5: return 2;
    case 6: return 4;
    default: return 1;
    }
}

bool Sm86::cbuf_read(Word q, int nm, int *bank, int *off) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return false;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    for (int k = 0; k < n; k++) {
        if (o[k].kind != sm86::O_CBUF && o[k].kind != sm86::O_UCBUF) continue;
        int bi = -1, ai = -1; bool idx = false;
        for (int j = 0; j < n; j++) {
            if (o[j].parent != k) continue;
            if (o[j].kind == sm86::O_IMM && std::strstr(o[j].name, "bank")) bi = j;
            else if (o[j].kind == sm86::O_IMM && std::strstr(o[j].name, "addr")) ai = j;
            else if (o[j].kind == sm86::O_GPR || o[j].kind == sm86::O_UR) idx = true;
        }
        if (bi < 0) continue;
        *bank = (int)o[bi].imm;

        *off = (idx || ai < 0) ? 0x40000000 : (int)o[ai].imm;
        return true;
    }

    if (in.op == opid("LDC")) {
        int b = sm86::val_index(in.cls, "Sa_bank");
        if (b >= 0) {
            *bank = (int)sm86::get(in, b);
            int rai = sm86::val_index(in.cls, "Ra");
            bool idx = rai >= 0 && sm86::get(in, rai) != 255;
            int ao = sm86::val_index(in.cls, "Ra_offset");
            *off = idx ? 0x40000000 : (ao >= 0 ? (int)sm86::get(in, ao) : 0);
            return true;
        }
    }
    return false;
}
int Sm86::ldc_bank(Word q) {
    sm86::Inst in;
    if (!sm86::decode(q, &in) || in.op != opid("LDC")) return -1;
    int b = sm86::val_index(in.cls, "Sa_bank");
    return b < 0 ? -1 : (int)sm86::get(in, b);
}
bool Sm86::ldc_plain(Word q, int nm, int *ra, int *off) {
    (void)nm;
    sm86::Inst in;
    if (!sm86::decode(q, &in) || in.op != opid("LDC")) return false;
    int sz = sm86::val_index(in.cls, "sz");
    if (sz >= 0 && sm86::get(in, sz) != 4) return false;
    int rai = sm86::val_index(in.cls, "Ra"), ao = sm86::val_index(in.cls, "Ra_offset");
    *ra = rai < 0 ? RZ : (int)sm86::get(in, rai);
    *off = ao < 0 ? 0 : (int)sm86::get(in, ao);
    return true;
}

int Sm86::cf_kind(int nm) {
    const OpSets &T = sets();
    if (nm == T.O_Bra || nm == T.O_Jmp) return C_BRA;
    if (nm == T.O_Brx || nm == T.O_Jmx || nm == opid("BRXU") || nm == opid("JMXU")) return C_BRX;
    if (nm == T.O_Exit) return C_EXIT;
    if (nm == T.O_Cal) return C_CALL;
    if (nm == T.O_Ret) return C_RET;
    return C_OTHER;
}
int Sm86::cf_kind_q(Word q, int nm) {
    int c = cf_kind(nm);

    if (c == C_CALL && (guard_pred(q) != PT || guard_inv(q))) return C_BRA;
    return c;
}
bool Sm86::branch_cond(Word q, int nm, int *pn, int *inv) {
    if (cf_kind(nm) != C_BRA) return false;
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return false;
    int pp = sm86::val_index(in.cls, "Pp");
    if (pp < 0) return false;
    int reg = (int)sm86::get(in, pp);
    int ni = sm86::val_index(in.cls, "Pp@not");
    int neg = ni >= 0 ? (int)sm86::get(in, ni) : 0;
    *pn = reg == 7 ? PT : reg;
    *inv = neg;
    return true;
}
bool Sm86::lit_read(const ProgramT<Sm86> &p, int i, int key) {

    if (key < PREG || key >= sm86::KEY_UP + 7) return false;

    sm86::Inst in;
    if (!sm86::decode(p.q[i], &in)) return true;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);
    for (int k = 0; k < n; k++)
        if ((o[k].kind == sm86::O_PR || o[k].kind == sm86::O_UPR) &&
            (o[k].role == sm86::R_USE || o[k].role == sm86::R_DEFUSE))
            return false;
    return true;
}
bool Sm86::make_bra(Word from, Word &out) {
    int pn = guard_pred(from), inv = guard_inv(from);
    out = bra_self_word();
    set_guard(out, pn, inv);

    int cpn, cinv;
    if (branch_cond(from, decode_op(from), &cpn, &cinv)) {
        sm86::Inst in;
        if (sm86::decode(out, &in)) {
            int pp = sm86::val_index(in.cls, "Pp");
            int ni = sm86::val_index(in.cls, "Pp@not");
            if (pp >= 0) sm86::set(in, pp, cpn == PT ? 7 : cpn);
            if (ni >= 0) sm86::set(in, ni, cinv);
            out = in.w;
        }
    }
    return true;
}

int Sm86::indirect_reg(Word q) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return RZ;
    if (in.op == opid("BRX") || in.op == opid("RET")) {
        int r = sm86::val_index(in.cls, "Ra");
        return r < 0 ? RZ : (int)sm86::get(in, r);
    }
    if (in.op == opid("BRXU")) {
        int r = sm86::val_index(in.cls, "URa");
        return r < 0 ? RZ : sm86::KEY_UR + (int)sm86::get(in, r);
    }
    return RZ;
}
int Sm86::indirect_slot(const ProgramT<Sm86> &p, int i, u32 a) {

    sm86::Inst in;
    if (!sm86::decode(p.q[i], &in)) return -1;
    int off = 0;
    int ao = sm86::val_index(in.cls, "Ra_offset");
    if (ao < 0) ao = sm86::val_index(in.cls, "UR_offset");
    if (ao >= 0) off = (int)sm86::get(in, ao);
    u32 base = (u32)p.rel[(size_t)i];
    u32 target = base + a + (u32)off + 16;
    int j = p.snap((int)target);
    if (j < 0) return -1;
    return (u32)p.rel[(size_t)j] == target ? j : -1;
}

int Sm86::branch_dest(Word q, int rel) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return -1;
    int disp = 0;
    int si = sm86::val_index(in.cls, "sImm");
    if (si < 0) si = sm86::val_index(in.cls, "Sa");
    if (si >= 0) disp = (int)sm86::get(in, si);
    return rel + 16 + disp;
}
bool Sm86::set_branch(Word &q, int from, int to) {
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return false;
    int disp = 16 * to - (16 * from + 16);
    int si = sm86::val_index(in.cls, "sImm");
    const char *nm = "sImm";
    if (si < 0) { si = sm86::val_index(in.cls, "Sa"); nm = "Sa"; }
    if (si < 0) return false;
    (void)nm;
    return sm86::set(in, si, disp) ? (q = in.w, true) : false;
}

void Sm86::fix_calls(std::vector<Word> &words) {

    int n = (int)words.size();

    std::set<int> ret_regs;
    for (int k = 0; k < n; k++) {
        sm86::Inst in;
        if (!sm86::decode(words[(size_t)k], &in) || in.op != opid("RET")) continue;
        int r = sm86::val_index(in.cls, "Ra");
        if (r >= 0) ret_regs.insert((int)sm86::get(in, r));
    }
    for (int c = 0; c < n; c++) {
        sm86::Inst in;
        if (!sm86::decode(words[(size_t)c], &in) || in.op != opid("CALL")) continue;
        if (guard_pred(words[(size_t)c]) != PT || guard_inv(words[(size_t)c])) continue;

        int found = -1, reg = -1;
        for (int k = c - 1; k >= 0; k--) {
            sm86::Inst m;
            if (!sm86::decode(words[(size_t)k], &m)) continue;
            if (m.op == opid("MOV")) {
                int rd = sm86::val_index(m.cls, "Rd"), sb = sm86::val_index(m.cls, "Sb");
                if (rd >= 0 && sb >= 0 && ret_regs.count((int)sm86::get(m, rd))) {
                    found = k; reg = (int)sm86::get(m, rd); break;
                }
            }
            if (m.op == opid("IMAD")) {

                int rd = sm86::val_index(m.cls, "Rd"), sc = sm86::val_index(m.cls, "Sc");
                if (rd >= 0 && sc >= 0 && ret_regs.count((int)sm86::get(m, rd))) {
                    found = k; reg = (int)sm86::get(m, rd); break;
                }
            }
            if (cf_kind(m.op) == C_BRA && (guard_pred(words[(size_t)k]) != PT))
                continue;
            if (cf_kind(m.op) != C_OTHER) break;
        }
        if (found < 0) fail("sm86 fix_calls: no return-address load for CALL at %d", c);
        int retslot = c + 1;
        sm86::Inst m;
        sm86::decode(words[(size_t)found], &m);
        int sb = sm86::val_index(m.cls, m.op == opid("MOV") ? "Sb" : "Sc");
        if (!sm86::set(m, sb, 16 * retslot)) fail("sm86 fix_calls: cannot set return address");
        words[(size_t)found] = m.w;
        (void)reg;
    }

    for (int k = 0; k < n; k++) {
        sm86::Inst in;
        if (!sm86::decode(words[(size_t)k], &in) || in.op != opid("RET")) continue;
        int ao = sm86::val_index(in.cls, "Ra_offset");
        if (ao >= 0 && sm86::set(in, ao, -(16 * k + 16))) words[(size_t)k] = in.w;
    }
}

bool Sm86::eq_but_field(Word a, Word b, int off) {

    sm86::Inst ia;
    if (!sm86::decode(a, &ia)) return false;
    sm86::Operand op;
    if (gpr_op_index(ia, off, &op) < 0) return false;
    if (!sm86::set_reg(ia, op, field_reg(b, off))) return false;
    return ia.w == b;
}

Sm86::Word Sm86::renumber_mask(Word q) {
    Word m = {0, 0};
    sm86::Inst in;
    if (!sm86::decode(q, &in)) return m;
    sm86::Operand o[sm86::MAX_OPNDS];
    int n = sm86::operands(in, o, sm86::MAX_OPNDS);

    static const int tests[] = {0, 1, 2, 4, 8, 16, 32, 64, 128, 254};
    for (int k = 0; k < n; k++) {
        if (o[k].kind != sm86::O_GPR || o[k].val < 0) continue;
        bool have_base = false;
        sm86::Word base = q;
        for (int t : tests) {
            sm86::Inst a = in;
            if (!sm86::set(a, o[k].val, t)) continue;
            if (!have_base) { base = a.w; have_base = true; continue; }
            m.lo |= a.w.lo ^ base.lo;
            m.hi |= a.w.hi ^ base.hi;
        }
    }
    return m;
}

void Sm86::build_cfg(const ProgramT<Sm86> &p, bool seed_orphans, CFGraph &g) {
    const OpSets &T = sets();
    (void)T;
    int n = p.n;
    g.n = n;
    g.cat.assign((size_t)n, C_OTHER);
    g.tgt.assign((size_t)n, -1);
    g.grd.assign((size_t)n, 0);
    g.nev.assign((size_t)n, 0);
    g.succ.assign((size_t)n, {});
    g.pred.assign((size_t)n, {});
    g.unknown.assign((size_t)n, 0);
    g.overflow = false;
    std::vector<std::set<int>> ss((size_t)n);

    std::vector<int> ret_sites;
    for (int i = 0; i < n; i++) {
        int c = cf_kind_q(p.q[i], p.op[i]);
        g.cat[(size_t)i] = (int8_t)c;
        g.tgt[(size_t)i] = p.target(i);
        g.grd[(size_t)i] = (char)p.guarded(i);
        g.nev[(size_t)i] = (char)p.never(i);
        if (c == C_CALL && !p.guarded(i) && i + 1 < n) ret_sites.push_back(i + 1);
    }

    for (int i = 0; i < n; i++) {
        int c = g.cat[(size_t)i];
        int nxt = (i + 1 < n) ? i + 1 : -1;
        bool guarded = g.grd[(size_t)i], never = g.nev[(size_t)i];
        if (never) { if (nxt >= 0) ss[(size_t)i].insert(nxt); continue; }
        if (c == C_BRA) {
            int t = g.tgt[(size_t)i];
            int pn, inv;
            bool cond = branch_cond(p.q[i], p.op[i], &pn, &inv) && pn != PT;
            if (t >= 0) ss[(size_t)i].insert(t); else g.unknown[(size_t)i] = 1;
            if ((guarded || cond) && nxt >= 0) ss[(size_t)i].insert(nxt);
        } else if (c == C_BRX) {
            g.unknown[(size_t)i] = 1;
            if (guarded && nxt >= 0) ss[(size_t)i].insert(nxt);
        } else if (c == C_CALL) {
            int t = g.tgt[(size_t)i];
            if (t >= 0) ss[(size_t)i].insert(t); else g.unknown[(size_t)i] = 1;
        } else if (c == C_RET) {
            for (int r : ret_sites) ss[(size_t)i].insert(r);
            if (ret_sites.empty()) g.unknown[(size_t)i] = 1;
        } else if (c == C_EXIT) {
            if (guarded && nxt >= 0) ss[(size_t)i].insert(nxt);
        } else {
            if (nxt >= 0) ss[(size_t)i].insert(nxt);
        }
    }
    (void)seed_orphans;
    for (int i = 0; i < n; i++)
        g.succ[(size_t)i].assign(ss[(size_t)i].begin(), ss[(size_t)i].end());
    for (int i = 0; i < n; i++)
        for (int j : g.succ[(size_t)i]) g.pred[(size_t)j].push_back(i);
}

static u64 sph_bits(const u8 *b, int lo, int w) {
    u64 v = 0;
    for (int k = 0; k < w; k++) {
        int bit = lo + k;
        if ((b[bit >> 3] >> (bit & 7)) & 1) v |= (u64)1 << k;
    }
    return v;
}
static void sph_put(u8 *b, int lo, int w, u64 v) {
    for (int k = 0; k < w; k++) {
        int bit = lo + k;
        u8 m = (u8)(1 << (bit & 7));
        if ((v >> k) & 1) b[bit >> 3] |= m; else b[bit >> 3] &= (u8)~m;
    }
}

void Sm86::exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out) {
    out.clear();
    if (bc.size() < kCode) return;
    const u8 *sph = bc.data();

    if ((sph[0] & 0x1f) != 2) return;

    int reg = 0;
    for (int i = 0; i < 8; i++) {
        u64 m = sph_bits(sph, 576 + 4 * i, 4);
        for (int c = 0; c < 4; c++)
            if (m & ((u64)1 << c)) out.push_back(reg++);
    }

    u64 w19 = sph_bits(sph, 608, 2);
    if (w19 & 1) out.push_back(reg++);
    if (w19 & 2) out.push_back(reg++);
}

void Sm86::control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f) {

    if (bc.size() < kCode) return;

    schedule86(bc, ct);
    u8 *sph = bc.data();

    int max_gpr = -1;
    bool kills = false, gstore = false, ldst = false, fp64 = false;
    u32 co = const_off(ct);
    const OpSets &T = sets();
    std::vector<Field> fm;
    for (u32 off = kCode; off + 16 <= co; off += 16) {
        Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        if (empty(w)) continue;
        int nm = decode_op(w);
        if (nm == T.O_Kil) kills = true;
        if (cf_kind_q(w, nm) == C_BRX) fail("sm86 control: a computed jump survived to the control");
        if (T.global_store[(size_t)nm]) gstore = true;
        if (T.load_or_store[(size_t)nm]) ldst = true;
        if (T.fp64[(size_t)nm]) fp64 = true;
        try {
            fieldmap(w, nm, decode_props(w), fm);
            for (const Field &fd : fm)
                for (int k = 0; k < fd.w; k++)
                    if (fd.base + k < RZ) max_gpr = std::max(max_gpr, fd.base + k);
        } catch (const UbError &) {}
    }
    (void)ldst;

    u32 regs = decl_regs(max_gpr);
    set_reg_count(ct, regs);
    f.gpr_count = (int)regs;
    f.kills_pixels = kills ? 1 : 0;

    sph_put(sph, 15, 1, kills ? 1 : 0);
    sph_put(sph, 16, 1, gstore ? 1 : 0);
    sph_put(sph, 27, 1, fp64 ? 1 : 0);
    sph_put(sph, 32, 24, 0);

    const u32 id = NVN2_CTL(debugBuildId);
    if (ct.size() >= id + 16) {
        wr32(ct, id, UBERSPEC_STAMP_MAGIC);
        wr32(ct, id + 4, UBERSPEC_CODEGEN_VER_NVN2);
        wr32(ct, id + 8, 0);
        wr32(ct, id + 12, 0);
    }

    if (ct.size() < kCtlHead) fail("sm86 control: %zu bytes, shorter than its header", ct.size());
    u32 vmaj = rd32(ct, NVN2_CTL(mMajorVer)), vmin = rd32(ct, NVN2_CTL(mMinorVer));
    if (vmaj != NVN2_CONTROL_MAJOR || vmin != NVN2_CONTROL_MINOR)
        fail("sm86 control: version %u.%u, the jump list is placed for 201.20", vmaj, vmin);
    if (rd32(ct, NVN2_CTL(mEmbeddedSize)) || rd32(ct, NVN2_CTL(mExtensionSize)) ||
        rd32(ct, NVN2_CTL(mEmbeddedOffset)) > kCtlHead || rd32(ct, NVN2_CTL(mExtensionOffset)) > kCtlHead)
        fail("sm86 control: the block at +0xbc or +0xc8 is not empty");
    ct.resize(kCtlHead);
    for (u32 o : {NVN2_CTL(mControlSize), NVN2_CTL(mControlSize2), NVN2_CTL(mDataEnd),
                  NVN2_CTL(mJumpTableOffset)})
        wr32(ct, o, kCtlHead);
    wr32(ct, NVN2_CTL(mJumpTableSize), 0);
}

void Sm86::verify(const std::vector<u8> &bc, const std::vector<u8> &ct, bool run_v8,
                  GateResult &R, const std::vector<u8> *shipped_bc,
                  const std::vector<u8> *shipped_ct, const std::vector<u8> *ref_bc,
                  const std::vector<u8> *ref_ct) {
    (void)run_v8; (void)shipped_bc; (void)shipped_ct; (void)ref_bc; (void)ref_ct;
    char buf[256];
    u32 co = const_off(ct);
    bool ok_layout = (co % 256 == 0) && co >= (u32)kCode && co <= bc.size();
    snprintf(buf, sizeof buf, "const_off %#x, size %zu", co, bc.size());
    R.add("V1 layout", ok_layout, buf);

    int bad = 0, nbrx = 0, firstbad = -1;
    for (u32 off = kCode; off + 16 <= co; off += 16) {
        Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        if (empty(w)) continue;
        sm86::Inst in;
        if (!sm86::decode(w, &in)) { if (firstbad < 0) firstbad = (int)off; bad++; continue; }
        if (!sm86::ctl_valid(in)) { if (firstbad < 0) firstbad = (int)off; bad++; }
        int c = cf_kind_q(w, in.op);
        if (c == C_BRX) nbrx++;
    }
    snprintf(buf, sizeof buf, "%d words fail decode/ctl (first at %#x)", bad, firstbad);
    R.add("V2 words", bad == 0, buf);

    snprintf(buf, sizeof buf, "%d computed jumps remain", nbrx);
    R.add("V5 no computed jump", nbrx == 0, buf);

    int max_gpr = -1;
    std::vector<Field> fm;
    for (u32 off = kCode; off + 16 <= co; off += 16) {
        Word w;
        std::memcpy(&w.lo, bc.data() + off, 8);
        std::memcpy(&w.hi, bc.data() + off + 8, 8);
        if (empty(w)) continue;
        try {
            fieldmap(w, decode_op(w), decode_props(w), fm);
            for (const Field &fd : fm)
                for (int k = 0; k < fd.w; k++)
                    if (fd.base + k < RZ) max_gpr = std::max(max_gpr, fd.base + k);
        } catch (const UbError &) {}
    }
    u32 regs = reg_count(ct);
    snprintf(buf, sizeof buf, "regs %u, highest named R%d", regs, max_gpr);
    R.add("V3 reg count", (int)regs > max_gpr && regs >= 4, buf);

    {
        int nbad = 0, firstw = -1, fb = -1, fw = 0;
        int nov = 0, firsto = -1, ofr = -1;
        for (u32 off = kCode; off + 16 <= co; off += 16) {
            Word w;
            std::memcpy(&w.lo, bc.data() + off, 8);
            std::memcpy(&w.hi, bc.data() + off + 8, 8);
            if (empty(w)) continue;
            sm86::Inst in;
            if (!sm86::decode(w, &in)) continue;
            sm86::Operand o[sm86::MAX_OPNDS];
            int n = sm86::operands(in, o, sm86::MAX_OPNDS);
            u64 dw[4] = {0, 0, 0, 0};
            bool ov = false;
            for (int k = 0; k < n; k++) {
                if (o[k].kind != sm86::O_GPR || o[k].reg >= RZ || o[k].nregs <= 0) continue;
                int b = o[k].reg, nr = o[k].nregs;
                if (o[k].role == sm86::R_DEF || o[k].role == sm86::R_DEFUSE)
                    for (int j = 0; j < nr && b + j < RZ; j++) {
                        u64 bit = (u64)1 << ((b + j) & 63);
                        if (dw[(b + j) >> 6] & bit) {
                            if (!ov && firsto < 0) { firsto = (int)(off - kCode) / 16; ofr = b + j; }
                            ov = true;
                        }
                        dw[(b + j) >> 6] |= bit;
                    }
                if (b % tuple_align(nr) == 0 && b + nr - 1 <= 253) continue;
                if (firstw < 0) { firstw = (int)(off - kCode) / 16; fb = b; fw = nr; }
                nbad++;
            }
            nov += ov;
        }
        snprintf(buf, sizeof buf, "%d misplaced tuples (first at word %d: R%d, %d wide)", nbad,
                 firstw, fb, fw);
        R.add("V16 tuples", nbad == 0, buf);
        snprintf(buf, sizeof buf, "%d instructions write a register twice (first at word %d: R%d)",
                 nov, firsto, ofr);
        R.add("V17 destinations", nov == 0, buf);
    }

    int first = -1;
    int hz = validate86(bc, co, &first);
    snprintf(buf, sizeof buf, "%d hazards (first at word %d)", hz, first);
    R.add("V14 hazards", hz == 0, buf);

    {
        const u32 vmaj = ct.size() >= NVN2_CTL(mMinorVer) + 4 ? rd32(ct, NVN2_CTL(mMajorVer)) : 0;
        const u32 vmin = ct.size() >= NVN2_CTL(mMinorVer) + 4 ? rd32(ct, NVN2_CTL(mMinorVer)) : 0;
        bool ok = ct.size() >= kCtlHead && vmaj == NVN2_CONTROL_MAJOR && vmin == NVN2_CONTROL_MINOR;
        u32 lo = 0, sz = 0, n = 0;
        if (ok) {
            lo = rd32(ct, NVN2_CTL(mJumpTableOffset));
            sz = rd32(ct, NVN2_CTL(mJumpTableSize));
            ok = lo >= kCtlHead && (u64)lo + sz <= ct.size();
            if (ok && sz >= 4) n = rd32(ct, lo);
            ok = ok && sz == (n ? 4 + 16 * n : 0) && (int)n == nbrx;
            u32 end = (std::max(kCtlHead, lo + sz) + 7) & ~7u;
            ok = ok && ct.size() == end;
            for (u32 o : {NVN2_CTL(mControlSize), NVN2_CTL(mControlSize2), NVN2_CTL(mDataEnd)})
                ok = ok && rd32(ct, o) == end;
        }
        snprintf(buf, sizeof buf, "control %u.%u, %zu bytes, jump list %u entries at %#x, %d computed jumps",
                 vmaj, vmin, ct.size(), n, lo, nbrx);
        R.add("V15 control", ok, buf);
    }

    const u32 id = NVN2_CTL(debugBuildId);
    bool ok_stamp = ct.size() >= id + 8 && rd32(ct, id) == UBERSPEC_STAMP_MAGIC;
    snprintf(buf, sizeof buf, "stamp %#x ver %u", ok_stamp ? rd32(ct, id) : 0,
             ok_stamp ? rd32(ct, id + 4) : 0);
    R.add("V13 stamp", ok_stamp, buf);
}

}
