
#include "uber.h"
#include <cstdarg>
#include <chrono>

extern "C" {
#include "sm50tab.h"
}

namespace ub {

void fail(const char *fmt, ...) {
    char buf[2048];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    throw UbError(buf);
}

const char *op_name(int op) {
    if (op < 0 || op >= SM50_NNAMES) return "Invalid";
    return SM50_NAME[op];
}
int op_id(const char *name) {
    for (int i = 0; i < SM50_NNAMES; i++)
        if (std::strcmp(SM50_NAME[i], name) == 0) return i;
    return -1;
}
int decode_op(u64 q) { return (int)SM50_TAB_NAME[q >> 50]; }
unsigned decode_props(u64 q) { return (unsigned)SM50_TAB_PROPS[q >> 50]; }

OpSet make_opset(std::initializer_list<const char *> names) {
    OpSet s((size_t)SM50_NNAMES, 0);
    for (const char *nm : names) {
        int id = op_id(nm);
        if (id >= 0) s[(size_t)id] = 1;

    }
    return s;
}

static OpSets *g_sets = nullptr;

PerfCounters g_perf;
double perf_now() {
    return (double)std::chrono::duration_cast<std::chrono::nanoseconds>(
               std::chrono::steady_clock::now().time_since_epoch()).count() * 1e-9;
}

const OpSets &S() {
    if (g_sets) return *g_sets;
    OpSets *s = new OpSets();

    s->no_dest = make_opset({
        "Bra", "Brx", "Jmp", "Jmx", "Sync", "Ssy", "Brk", "Pbk", "Cont",
        "Pcnt", "Exit", "Ret", "Kil", "Nop", "Membar", "Depbar", "Bar",
        "Red", "St", "Stg", "Sts", "Stl", "Ast", "Cctl", "Cctll", "Pexit",
        "Cal", "Jcal", "Rtt", "Setcrsptr", "Plongjmp", "Pret",

        "Invalid"});
    s->no_pred = make_opset({"Ssy", "Pbk", "Pcnt"});
    s->store_ops = make_opset({"St", "Stg", "Stl", "Sts", "Ast", "Red"});
    s->widemem = make_opset({"Ldc", "Ld", "Ldg", "Ldl", "Lds", "St", "Stg",
                             "Stl", "Sts"});
    s->texs_fam = make_opset({"Texs", "Tlds", "Tld4s", "TexsF16", "TldsF16",
                              "Tld4sF16"});
    s->tex_fam = make_opset({"Tex", "Tld", "Tld4", "Tmml", "Txq", "Txd",
                             "TexB", "TldB", "Tld4B", "TxdB", "TxqB", "TmmlB"});
    s->tex_bases = OpSet((size_t)SM50_NNAMES, 0);
    for (size_t i = 0; i < s->tex_bases.size(); i++)
        s->tex_bases[i] = (char)(s->texs_fam[i] || s->tex_fam[i]);

    s->setp_fam = make_opset({"Fsetp", "Isetp", "Dsetp", "Hsetp2", "Csetp",
                              "Psetp", "Vsetp"});
    s->pred39_list = make_opset({
        "Fsetp", "Isetp", "Dsetp", "Hsetp2", "Csetp", "Psetp", "Vsetp",
        "Fset", "Iset", "Dset", "Cset", "Pset", "Sel", "Fmnmx", "Dmnmx",
        "Imnmx", "Icmp", "Fcmp", "Shf", "Iadd", "Iadd3", "Vote", "P2r",
        "Fswzadd"});

    s->side_effect = make_opset({
        "Ast", "St", "Stg", "Sts", "Red", "Atom", "Atoms", "Kil", "Exit",
        "Ret", "Bar", "Membar", "Cctl", "Cctll", "Out", "Pixld", "Shfl",
        "Vote", "Setcrsptr", "Plongjmp", "Pret", "Rtt", "Cal", "Jcal",
        "Pexit", "Invalid"});
    s->branchy = make_opset({"Bra", "Brx", "Jmp", "Jmx", "Brk", "Cont", "Sync"});
    s->pushy = make_opset({"Ssy", "Pbk", "Pcnt"});
    s->freebie = make_opset({"Nop", "Depbar"});

    s->alu_cbuf = make_opset({
        "Fadd", "Fmul", "Ffma", "Fmnmx", "Fsetp", "Fset", "Fcmp", "Fchk",
        "Iadd", "Iadd3", "Imnmx", "Isetp", "Iset", "Icmp", "Lop", "Lop3",
        "Sel", "Shl", "Shr", "Shf", "Xmad", "I2f", "I2i", "F2f", "F2i",
        "Iscadd", "Lea", "Prmt", "Popc", "Flo", "Rro", "Mov", "Dadd",
        "Dmul", "Dfma", "Dsetp", "Dmnmx"});
    s->alu_cbuf_srcc = make_opset({
        "Bfi", "Dfma", "Fcmp", "Ffma", "Icmp", "Imad", "Imadsp", "Prmt",
        "Xmad"});
    s->pure_cse = make_opset({
        "Fadd", "Fadd32i", "Fmul", "Fmul32i", "Ffma", "Fmnmx", "Fset",
        "Fcmp", "Mufu", "Rro", "F2f", "F2i", "I2f", "I2i", "Ipa",
        "Iadd", "Iadd32i", "Iadd3", "Imnmx", "Iset", "Icmp", "Iscadd",
        "Lea", "Shl", "Shr", "Shf", "Xmad", "Sel", "Lop", "Lop32i", "Lop3",
        "Prmt", "Popc", "Flo", "Ldc", "Bfe", "Bfi"});

    s->alu_srcb = make_opset({
        "Imnmx", "Fmnmx", "Dmnmx", "Shl", "Shr", "Iadd", "Iscadd", "Imul",
        "Lop", "Popc", "Flo", "Bfe", "Sel", "Icmp", "Iset", "Isetp", "Fadd",
        "Fmul", "Fset", "Fsetp", "F2f", "F2i", "I2f", "I2i", "Mufu", "Rro",
        "Shf", "Prmt", "Lea", "Bfi", "Xmad", "Imad", "Ffma", "Fcmp",
        "Iadd3", "Lop3", "Vmnmx", "Hadd2", "Hmul2", "Hfma2"});
    s->imm32_ops = make_opset({
        "Mov32i", "Iadd32i", "Lop32i", "Imad32i", "Fadd32i", "Fmul32i",
        "Ffma32i", "Iscadd32i", "Hadd232i", "Hmul232i"});
    s->transparent = make_opset({
        "Mov", "Imnmx", "Shl", "Shr", "Iadd32i", "Iadd", "Iadd3", "Lop32i",
        "Lop", "Lop3", "Bfe", "I2i", "Sel", "Imad", "Xmad", "Iscadd",
        "Icmp", "Prmt", "Shf", "Mov32i", "Iset", "Popc", "Flo", "P2r",
        "Ldc"});

    s->pred_src_ok = make_opset({
        "Fsetp", "Isetp", "Dsetp", "Hsetp2", "Csetp", "Psetp", "Vsetp",
        "Fset", "Iset", "Dset", "Cset", "Pset", "Sel", "Fmnmx", "Dmnmx",
        "Imnmx"});
    s->branchy_imm = make_opset({"Bra", "Jmp", "Ssy", "Pbk", "Pcnt", "Cal"});

    s->pred39_spurious = make_opset({"Iadd", "Iadd3", "Shf", "Fswzadd"});
    s->pred39_gpr = make_opset({"Fcmp", "Icmp"});

    s->spec_side_effect = make_opset({
        "Ast", "St", "Stg", "Stl", "Sts", "Red", "Atom", "Atoms", "Kil",
        "Exit", "Ret", "Bar", "Membar", "Depbar", "Cctl", "Cctll", "Out",
        "Pixld", "Al2p", "Ipa", "Ald"});
    s->spec_control = make_opset({
        "Bra", "Brx", "Jmp", "Jmx", "Ssy", "Sync", "Pbk", "Brk", "Pcnt",
        "Cont", "Nop"});

    s->safe_ops = make_opset({
        "Nop", "Bra", "Brk", "Cont", "Ssy", "Pbk", "Pcnt", "Sync", "Exit",
        "Kil", "Ret", "Depbar", "Membar", "Bar",
        "Mov", "Mov32i", "Sel", "Rro", "Mufu", "Ipa", "S2r", "Fswzadd",
        "Fadd", "Fadd32i", "Ffma", "Fmul", "Fmul32i", "Fmnmx", "Fset",
        "Fsetp", "Fcmp",
        "Iadd", "Iadd3", "Iadd32i", "Imnmx", "Iset", "Isetp", "Icmp",
        "Iscadd", "Lop", "Lop3", "Lop32i", "Shl", "Shr", "Shf", "Bfe",
        "Bfi", "Xmad", "Pset", "Psetp", "P2r", "R2p",

        "Vote", "Flo", "Popc", "Red",
        "F2f", "F2i", "I2f", "I2i",
        "Ldc", "Ldl", "Stl", "Lds", "Sts", "Ald", "Ast", "Al2p",
        "Tex", "TexB", "Texs", "TexsF16", "Tld", "TldB", "Tlds", "TldsF16",
        "Tld4", "Tld4B", "Tld4s", "Tld4sF16", "Tmml", "TmmlB", "Txq",
        "TxqB", "Txd", "TxdB"});

    s->load_or_store = make_opset({
        "Ldl", "Stl", "Lds", "Sts", "Ldg", "Stg", "Ld", "St", "Atom",
        "Atoms", "Red", "Membar", "Suld", "Sust", "Suatom", "Suldga",
        "Sustga", "Sured", "Ldslk", "Stslk"});
    s->global_store = make_opset({
        "Stg", "St", "Red", "Atom", "Sust", "Sustga", "Suatom", "Sured"});
    s->fp64 = make_opset({
        "Dadd", "Dmul", "Dfma", "Dset", "Dsetp", "Dmnmx", "F2f64", "I2d",
        "D2f", "D2i", "Dmma"});
    s->local_ops = make_opset({"Ldl", "Stl"});

    s->rate_quarter = make_opset({
        "Mufu", "Rro", "F2f", "F2i", "I2f", "I2i", "Ipa", "Ald",
        "Ast", "Al2p", "Bra", "Brx", "Jmp", "Jmx", "Ssy", "Sync",
        "Pbk", "Brk", "Pcnt", "Cont", "Exit", "Kil", "Ret",
        "Depbar", "Bar", "Cal", "Jcal", "Pexit", "Shfl", "Vote"});
    s->rate_half = make_opset({
        "Dadd", "Dmul", "Dfma", "Dset", "Dsetp", "Dmnmx", "Imad",
        "Imadsp", "Imul", "Imul32i", "Imad32i", "Xmad", "Popc",
        "Flo", "Shf", "Lea", "Iadd3", "Prmt", "Bfe", "Bfi"});

    s->ctl_texs_fam = make_opset({"Texs", "Tlds", "Tld4s", "TexsF16",
                                  "TldsF16", "Tld4sF16"});
    s->ctl_tex_fam = make_opset({"Tex", "Tld", "Tld4", "Tmml", "Txq", "Txd"});
    s->ctl_tex_bindless = make_opset({"TexB", "TldB", "Tld4B", "TxdB",
                                      "TxqB", "TmmlB"});
    s->tex_ops_audit = make_opset({"Tex", "Texs", "Tld", "Tlds", "Tld4",
                                   "Tld4s", "Txq", "Tmml", "Txd", "Txa",
                                   "Tld4_b", "Tex_b", "Texs_b"});

#define ID(x) s->O_##x = op_id(#x)
    ID(Nop); ID(Mov); ID(Mov32i); ID(Ldc); ID(Stl); ID(Ldl); ID(Invalid);
    ID(Shfl); ID(Bra); ID(Jmp); ID(Ssy); ID(Pbk); ID(Pcnt); ID(Cal);
    ID(Brx); ID(Jmx); ID(Sync); ID(Brk); ID(Cont); ID(Exit); ID(Ret);
    ID(Kil); ID(Isetp); ID(Psetp); ID(Iset); ID(Imnmx); ID(Sel); ID(Shl);
    ID(Shr); ID(Iadd); ID(Iadd32i); ID(Lop); ID(Lop32i); ID(Fsetp);
    ID(Fset); ID(Fmnmx); ID(Pset); ID(Xmad); ID(Ffma); ID(Texs); ID(Ast);
    ID(Iadd3); ID(Ald); ID(Al2p); ID(F2f); ID(F2i); ID(I2f); ID(I2i);
    ID(Fadd);
    ID(Ipa); ID(Fmul);
    ID(P2r); ID(Vote); ID(Votevtg); ID(Flo); ID(Popc);
#undef ID

    g_sets = s;
    return *s;
}

int g_strict_decode = 0;

int mem_data_regs(u64 q, int nm) {
    if (nm < 0) return 1;
    if (g_strict_decode & STRICT_ALD) {

        const OpSets &T = S();
        if (nm == T.O_Ald || nm == T.O_Ast || nm == T.O_Al2p)
            return 1 + (int)((q >> 47) & 3);
    }
    if (!S().widemem[(size_t)nm]) return 1;
    int sz = (int)((q >> 48) & 7);
    if (sz == 5) return 2;
    if (sz == 6 || sz == 7) return 4;
    return 1;
}

static int dedup_sorted(const int *tmp, int n, int *offs) {
    int m = 0;
    for (int i = 0; i < n; i++) {
        bool dup = false;
        for (int j = 0; j < m; j++) if (offs[j] == tmp[i]) { dup = true; break; }
        if (!dup) offs[m++] = tmp[i];
    }
    std::sort(offs, offs + m);
    return m;
}

int gpr_src_offsets(u64 q, int nm, unsigned props, int *offs) {
    (void)q;
    int tmp[8], n = 0;
    if (props & P_RA) tmp[n++] = (nm == S().O_Mov) ? 20 : 8;
    if (props & P_RB) tmp[n++] = 20;
    if (props & P_RC) tmp[n++] = 39;
    if (props & P_RD2) tmp[n++] = 28;
    if (props & P_RB2) tmp[n++] = 39;
    return dedup_sorted(tmp, n, offs);
}

int pred_src_offsets(int nm, unsigned props, int *offs) {
    const OpSets &T = S();
    int tmp[8], n = 0;
    if (props & P_PS) tmp[n++] = 39;
    if (T.pred39_list[(size_t)nm]) tmp[n++] = 39;
    if (nm == T.O_Psetp || nm == T.O_Pset) { tmp[n++] = 12; tmp[n++] = 29; }
    return dedup_sorted(tmp, n, offs);
}

bool cbuf_read_of(u64 q, int nm, int *bank, int *off) {
    if (nm == S().O_Ldc) {
        LdcFields f = ldc_fields(q);
        *bank = f.bank; *off = f.off;
        return true;
    }
    if (cbuf_top5(q) == CBUF_SRCB_TOP5 || cbuf_top5(q) == CBUF_SRCC_TOP5) {
        *bank = cbuf_bank(q); *off = cbuf_off(q);
        return true;
    }
    return false;
}

int spurious_pred(int nm, u64 q) {
    const OpSets &T = S();
    if (!T.pred39_spurious[(size_t)nm] && !T.pred39_gpr[(size_t)nm]) return -1;
    int pn = (int)((q >> 39) & 7);
    return (pn != PT) ? PREG + pn : -1;
}

static const int TEXS_MASKLUT[2][8] = {
    {0x1, 0x2, 0x4, 0x8, 0x3, 0x9, 0xA, 0xC},
    {0x7, 0xB, 0xD, 0xE, 0xF, 0x0, 0x0, 0x0}};
static const int TEXS_SRC[14][2] = {
    {1,0},{1,1},{1,1},{2,1},{2,1},{2,2},{2,1},{2,1},{2,1},{2,2},{2,1},{2,1},
    {2,1},{2,2}};

static void tlds_src(int tgt, int *nA, int *nB) {
    switch (tgt) {
    case 0x0: *nA = 1; *nB = 0; return;
    case 0x1: *nA = 1; *nB = 1; return;
    case 0x2: *nA = 1; *nB = 1; return;
    case 0x4: *nA = 1; *nB = 2; return;
    case 0x5: *nA = 2; *nB = 1; return;
    case 0x6: *nA = 1; *nB = 2; return;
    case 0x7: *nA = 2; *nB = 1; return;
    case 0x8: *nA = 2; *nB = 1; return;
    case 0xc: *nA = 2; *nB = 2; return;
    default:  *nA = 2; *nB = 2; return;
    }
}

static bool name_starts(int nm, const char *pfx) {
    const char *s = op_name(nm);
    return std::strncmp(s, pfx, std::strlen(pfx)) == 0;
}

static int popcount4(int x) { int c = 0; while (x) { c += x & 1; x >>= 1; } return c; }

void tex_defs(u64 q, int nm, RSet &out) {
    const OpSets &T = S();
    if (T.texs_fam[(size_t)nm]) {
        int dest = (int)(q & 0xFF), dest2 = (int)((q >> 28) & 0xFF);
        int wm = name_starts(nm, "Tld4s") ? 4 : (int)((q >> 50) & 7);
        int comp = popcount4(TEXS_MASKLUT[dest2 == 255 ? 0 : 1][wm]);
        for (int i = 0; i < comp; i++) {
            int rd = (i >> 1) ? dest2 : dest;
            if (rd != 255) out.add(rd + (i & 1));
        }
        return;
    }
    if (T.tex_fam[(size_t)nm]) {
        int dest = (int)(q & 0xFF), wm = (int)((q >> 31) & 0xF), k = 0;
        if (dest != 255)
            for (int bit = 0; bit < 4; bit++)
                if (wm & (1 << bit)) out.add(dest + k++);
        return;
    }
}

void tex_uses(u64 q, int nm, RSet &out) {
    const OpSets &T = S();
    if (T.texs_fam[(size_t)nm]) {
        int srcA = (int)((q >> 8) & 0xFF), srcB = (int)((q >> 20) & 0xFF);
        int nA, nB;
        if (name_starts(nm, "Tld4s")) { nA = 2; nB = 1; }
        else {
            int tgt = (int)((q >> 53) & 0xF);
            if (name_starts(nm, "Texs")) {
                int k = tgt < 13 ? tgt : 13;
                nA = TEXS_SRC[k][0]; nB = TEXS_SRC[k][1];
            } else tlds_src(tgt, &nA, &nB);
        }
        for (int k = 0; k < nA; k++) if (srcA + k < 255) out.add(srcA + k);
        for (int k = 0; k < nB; k++) if (srcB + k < 255) out.add(srcB + k);
        return;
    }
    int srcA = (int)((q >> 8) & 0xFF), nA, srcB;
    const char *s = op_name(nm);
    if (!std::strcmp(s, "Txq") || !std::strcmp(s, "TxqB")) { nA = 1; srcB = 255; }
    else if (!std::strcmp(s, "Tmml") || !std::strcmp(s, "TmmlB")) { nA = 2; srcB = 255; }
    else {
        srcB = (int)((q >> 20) & 0xFF);
        bool is_b = !std::strcmp(s, "TexB") || !std::strcmp(s, "TldB") ||
                    !std::strcmp(s, "Tld4B") || !std::strcmp(s, "TxdB");
        static const int dim_coords[8] = {1, 2, 2, 3, 3, 3, 3, 4};
        nA = dim_coords[(q >> 28) & 7];
        if ((q >> 50) & 1) nA++;
        int lod = (int)((is_b ? (q >> 37) : (q >> 55)) & 7);
        if (lod == 2 || lod == 3) nA++;
    }
    for (int k = 0; k < nA; k++) if (srcA + k < 255) out.add(srcA + k);
    if (srcB < 255) out.add(srcB);
}

void Program::du_word(u64 q, int nm, unsigned props, RSet &defs, RSet &maydefs,
                      RSet &uses) {
    const OpSets &T = S();
    defs.clear(); maydefs.clear(); uses.clear();
    if (q == 0 || nm == T.O_Nop) return;

    bool has_pred = !T.no_pred[(size_t)nm];
    int p = _predf(q);
    bool predicated = has_pred && (p != PT || _pinv(q));
    if (has_pred && p != PT) uses.add(PREG + p);

    auto addr = [&](int r) { if (r >= 0 && r < 255) uses.add(r); };
    auto addp = [&](int pn) { if (pn >= 0 && pn < 7) uses.add(PREG + pn); };

    if (T.tex_bases[(size_t)nm]) {
        RSet t; tex_uses(q, nm, t);
        std::vector<int> v; t.list(v);
        for (int r : v) addr(r);
    } else {
        int offs[8];
        int m = gpr_src_offsets(q, nm, props, offs);
        for (int k = 0; k < m; k++) {

            if ((g_strict_decode & STRICT_SHFL) && nm == T.O_Shfl) {
                if (offs[k] == 20 && ((q >> 28) & 1)) continue;
                if (offs[k] == 39 && ((q >> 29) & 1)) continue;
            }
            addr((int)((q >> offs[k]) & 0xFF));
        }

        bool skip39 = (g_strict_decode & STRICT_IADD) &&
                      T.pred39_spurious[(size_t)nm];
        if ((props & P_PS) && !skip39) addp((int)((q >> 39) & 7));
        if (T.pred39_list[(size_t)nm] && !skip39) addp((int)((q >> 39) & 7));
        if (nm == T.O_Psetp || nm == T.O_Pset) {
            addp((int)((q >> 12) & 7));
            addp((int)((q >> 29) & 7));
        }

        if (nm == T.O_P2r) for (int pn = 0; pn < 7; pn++) addp(pn);
    }

    bool no_dest = T.no_dest[(size_t)nm] != 0;
    RSet &sink = predicated ? maydefs : defs;

    if (T.setp_fam[(size_t)nm]) {
        int pn0 = (int)((q >> 3) & 7), pn1 = (int)(q & 7);
        if (pn0 != PT) sink.add(PREG + pn0);
        if (pn1 != PT) sink.add(PREG + pn1);
    } else if (T.tex_bases[(size_t)nm]) {
        RSet t; tex_defs(q, nm, t);
        std::vector<int> v; t.list(v);
        for (int r : v) if (r < 255) sink.add(r);
    } else if (!no_dest && (props & P_RD)) {
        int rd = _rd(q);
        if (rd < 255) {
            int w = mem_data_regs(q, nm);
            for (int k = 0; k < w; k++) if (rd + k < 255) sink.add(rd + k);
        }
        if ((props & (P_PD | P_LPD)) == P_LPD) {
            int pn = (int)((q >> 48) & 7);
            if (pn != PT) sink.add(PREG + pn);
        }

        if ((props & P_VPD) == P_VPD) {
            int pn = (int)((q >> 45) & 7);
            if (pn != PT) sink.add(PREG + pn);
        }
    } else if (no_dest) {
        if (T.store_ops[(size_t)nm]) {
            int rd = _rd(q);
            int w = mem_data_regs(q, nm);
            for (int k = 0; k < w; k++) if (rd + k < 255) addr(rd + k);
            addr(_ra(q));
        }
    }

    uses.unite(maydefs);
}

void Program::du(int i, RSet &d, RSet &md, RSet &u) const {
    du_word(q[i], op[i], props[i], d, md, u);
}

std::vector<u8> read_file(const std::string &p) {
    FILE *f = fopen(p.c_str(), "rb");
    if (!f) fail("cannot open %s", p.c_str());
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    std::vector<u8> b((size_t)(n > 0 ? n : 0));
    if (n > 0 && fread(b.data(), 1, (size_t)n, f) != (size_t)n) {
        fclose(f);
        fail("short read on %s", p.c_str());
    }
    fclose(f);
    return b;
}

void Program::load_paths(const std::string &bcp, const std::string &ctp) {
    load_bytes(read_file(bcp), read_file(ctp));
}

void Program::load_bytes(std::vector<u8> b, std::vector<u8> c) {
    bc = std::move(b);
    ct = std::move(c);
    build();
}

void Program::build() {
    if (ct.size() < CONSTOFF_OFF + 4) fail("control blob too small");
    co = const_off(ct);
    if (co > bc.size()) fail("ConstBufOffset %#x past bytecode (%zu)", co, bc.size());
    blob = bc.data() + co;
    blobsz = bc.size() - co;

    rel.clear(); q.clear(); idx_of.clear();
    for (u32 off = INSTR_START; off + 8 <= co; off += 8) {
        if ((off - INSTR_START) % 32 == 0) continue;
        rel.push_back((int)(off - INSTR_START));
        u64 w; std::memcpy(&w, bc.data() + off, 8);
        q.push_back(w);
    }
    n = (int)rel.size();
    for (int i = 0; i < n; i++) idx_of[rel[i]] = i;

    op.resize((size_t)n);
    props.resize((size_t)n);
    for (int i = 0; i < n; i++) {
        op[i] = (int16_t)decode_op(q[i]);
        props[i] = (uint16_t)decode_props(q[i]);
    }
    defs.resize((size_t)n);
    maydefs.resize((size_t)n);
    uses.resize((size_t)n);
    for (int i = 0; i < n; i++) du(i, defs[i], maydefs[i], uses[i]);
}

int Program::snap(int addr) const {
    auto it = idx_of.find(addr);
    if (it != idx_of.end()) return it->second;

    size_t lo = 0, hi = rel.size();
    while (lo < hi) {
        size_t mid = (lo + hi) >> 1;
        if (rel[mid] < addr) lo = mid + 1; else hi = mid;
    }
    return lo < (size_t)n ? (int)lo : -1;
}

bool Program::guarded(int i) const {
    if (S().no_pred[(size_t)op[i]]) return false;
    return _predf(q[i]) != PT;
}

bool Program::never(int i) const {
    if (S().no_pred[(size_t)op[i]]) return false;
    return _predf(q[i]) == PT && _pinv(q[i]);
}

int Program::target(int i) const {
    const OpSets &T = S();
    int nm = op[i];
    if (!(nm == T.O_Bra || nm == T.O_Jmp || nm == T.O_Ssy || nm == T.O_Pbk ||
          nm == T.O_Pcnt || nm == T.O_Cal))
        return -1;
    return snap(rel[i] + 8 + branch_imm(q[i]));
}

bool Program::blob_u32(int byte_off, u32 *out) const {
    if (byte_off < 0 || (size_t)byte_off + 4 > blobsz) return false;
    std::memcpy(out, blob + byte_off, 4);
    return true;
}

struct StackPool {

    std::vector<std::vector<int64_t>> list;
    std::unordered_map<std::string, int> pool;

    int intern(const std::vector<int64_t> &s) {
        std::string key((const char *)s.data(), s.size() * sizeof(int64_t));
        auto it = pool.find(key);
        if (it != pool.end()) return it->second;
        int k = (int)list.size();
        pool.emplace(std::move(key), k);
        list.push_back(s);
        return k;
    }
    const std::vector<int64_t> &get(int id) const { return list[(size_t)id]; }
};

static inline int64_t mkent(int kind, int tgt) {
    return ((int64_t)kind << 32) | (int64_t)(u32)tgt;
}
static inline int ent_kind(int64_t e) { return (int)(e >> 32); }
static inline int ent_tgt(int64_t e) { return (int)(int32_t)(u32)(e & 0xFFFFFFFF); }

void CFGraph::build(const Program &p, bool seed_orphans) {
    const OpSets &T = S();
    prog = &p;
    n = p.n;
    cat.assign((size_t)n, C_OTHER);
    tgt.assign((size_t)n, -1);
    grd.assign((size_t)n, 0);
    nev.assign((size_t)n, 0);
    succ.assign((size_t)n, {});
    pred.assign((size_t)n, {});
    unknown.assign((size_t)n, 0);
    overflow = false;

    for (int i = 0; i < n; i++) {
        int nm = p.op[i];
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
        tgt[(size_t)i] = p.target(i);
        grd[(size_t)i] = (char)p.guarded(i);
        nev[(size_t)i] = (char)p.never(i);
    }

    StackPool pool;
    std::vector<std::set<int>> stacks((size_t)n);
    std::vector<std::pair<int, int>> work;
    std::vector<std::set<int>> succset((size_t)n);

    auto push = [&](int i, const std::vector<int64_t> &stk) {
        if (i < 0 || i >= n) return;
        int sid = pool.intern(stk);
        auto &s = stacks[(size_t)i];
        if (!s.count(sid)) { s.insert(sid); work.push_back({i, sid}); }
    };

    std::vector<std::vector<int64_t>> tstack((size_t)n);
    {
        std::vector<int64_t> cur;
        for (int i = 0; i < n; i++) {
            tstack[(size_t)i] = cur;
            int c = cat[(size_t)i];
            if (c == C_SSY || c == C_PBK || c == C_PCNT) {
                if ((int)cur.size() < MAX_DEPTH)
                    cur.push_back(mkent(c == C_SSY ? 0 : c == C_PBK ? 1 : 2,
                                        tgt[(size_t)i]));
            } else if (c == C_SYNC) {
                if (!cur.empty() && ent_kind(cur.back()) == 0) cur.pop_back();
            } else if (c == C_BRK) {
                for (int pp = (int)cur.size() - 1; pp >= 0; pp--)
                    if (ent_kind(cur[(size_t)pp]) == 1) { cur.resize((size_t)pp); break; }
            } else if (c == C_CONT) {
                for (int pp = (int)cur.size() - 1; pp >= 0; pp--)
                    if (ent_kind(cur[(size_t)pp]) == 2) { cur.resize((size_t)pp + 1); break; }
            }
        }
    }

    push(0, {});
    size_t head = 0;
    int scan = 0;
    for (;;) {
        while (head < work.size()) {
            int ci = work[head].first, sid = work[head].second;
            head++;
            const std::vector<int64_t> stk = pool.get(sid);
            int nxt = (ci + 1 < n) ? ci + 1 : -1;
            int c = cat[(size_t)ci];

            if (nev[(size_t)ci]) {
                if (nxt >= 0) { succset[(size_t)ci].insert(nxt); push(nxt, stk); }
                continue;
            }
            if (c == C_SSY || c == C_PBK || c == C_PCNT) {
                if (nxt >= 0) succset[(size_t)ci].insert(nxt);
                if ((int)stk.size() < MAX_DEPTH) {
                    std::vector<int64_t> ns = stk;
                    ns.push_back(mkent(c == C_SSY ? 0 : c == C_PBK ? 1 : 2,
                                       tgt[(size_t)ci]));
                    push(nxt, ns);
                } else { overflow = true; push(nxt, stk); }
            } else if (c == C_SYNC) {
                if (!stk.empty() && ent_kind(stk.back()) == 0) {
                    int j = ent_tgt(stk.back());
                    if (j >= 0) {
                        succset[(size_t)ci].insert(j);
                        std::vector<int64_t> ns(stk.begin(), stk.end() - 1);
                        push(j, ns);
                    } else unknown[(size_t)ci] = 1;
                } else unknown[(size_t)ci] = 1;
                if (grd[(size_t)ci] && nxt >= 0) {
                    succset[(size_t)ci].insert(nxt);
                    push(nxt, stk);
                }
            } else if (c == C_BRK || c == C_CONT) {
                int want = (c == C_BRK) ? 1 : 2;
                int k = -1;
                for (int pp = (int)stk.size() - 1; pp >= 0; pp--)
                    if (ent_kind(stk[(size_t)pp]) == want) { k = pp; break; }
                if (k >= 0 && ent_tgt(stk[(size_t)k]) >= 0) {
                    int j = ent_tgt(stk[(size_t)k]);
                    succset[(size_t)ci].insert(j);
                    std::vector<int64_t> ns(stk.begin(),
                        stk.begin() + (c == C_BRK ? k : k + 1));
                    push(j, ns);
                } else unknown[(size_t)ci] = 1;
                if (grd[(size_t)ci] && nxt >= 0) {
                    succset[(size_t)ci].insert(nxt);
                    push(nxt, stk);
                }
            } else if (c == C_BRA) {
                int t = tgt[(size_t)ci];
                if (t >= 0) { succset[(size_t)ci].insert(t); push(t, stk); }
                else unknown[(size_t)ci] = 1;
                if (grd[(size_t)ci] && nxt >= 0) {
                    succset[(size_t)ci].insert(nxt);
                    push(nxt, stk);
                }
            } else if (c == C_BRX) {
                unknown[(size_t)ci] = 1;
                if (grd[(size_t)ci] && nxt >= 0) {
                    succset[(size_t)ci].insert(nxt);
                    push(nxt, stk);
                }
            } else if (c == C_EXIT) {
                if (grd[(size_t)ci] && nxt >= 0) {
                    succset[(size_t)ci].insert(nxt);
                    push(nxt, stk);
                }
            } else {
                if (nxt >= 0) { succset[(size_t)ci].insert(nxt); push(nxt, stk); }
            }
        }
        if (!seed_orphans) break;
        while (scan < n && !stacks[(size_t)scan].empty()) scan++;
        if (scan >= n) break;
        push(scan, tstack[(size_t)scan]);
    }

    for (int i = 0; i < n; i++)
        succ[(size_t)i].assign(succset[(size_t)i].begin(), succset[(size_t)i].end());
    for (int i = 0; i < n; i++)
        for (int j : succ[(size_t)i]) pred[(size_t)j].push_back(i);
}

std::vector<char> CFGraph::reachable_from_entry() const {
    std::vector<char> seen((size_t)n, 0);
    std::vector<int> st;
    if (n <= 0) return seen;
    st.push_back(0);
    while (!st.empty()) {
        int i = st.back(); st.pop_back();
        if (seen[(size_t)i]) continue;
        seen[(size_t)i] = 1;
        for (int j : succ[(size_t)i]) if (!seen[(size_t)j]) st.push_back(j);
    }
    return seen;
}

}
