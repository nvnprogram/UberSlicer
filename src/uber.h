
#ifndef UBERSPEC_UBER_H
#define UBERSPEC_UBER_H

#include <cstdint>
#include <cstring>
#include <cstdio>
#include <string>
#include <vector>
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <stdexcept>
#include <functional>

#define UBERSPEC_STAMP_MAGIC 0x50534255u
#define UBERSPEC_CODEGEN_VER 1u

namespace ub {

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t  u8;

static const int INSTR_START = 0x80;

#include "nvn_control.h"
static const int CONSTOFF_OFF =
    (int)offsetof(NVNshaderControl, mConstBufOffset);

static const int SPH_OFF = (int)offsetof(GPUProgramHeader, nvsh);
static const int SPH_SIZE = (int)sizeof(NvShaderHeader);
static const int RZ = 255;
static const int PT = 7;
static const int PREG = 256;

static const int LMBIT = 512;
static const int LMMAX = 1024;

static const int LMBASE = 1024;

static const int LMVAL = 2048;

static const int32_t CBBASE = -(1 << 24);

static const u32 M32 = 0xFFFFFFFFu;

static const int CBUF_ALIGN = 256;

template <typename T> inline T slot_rel(T k) {
    return (k / 3) * 32 + (k % 3) * 8 + 8;
}
template <typename T> inline size_t slot_off(T k) {
    return (size_t)INSTR_START + (size_t)slot_rel(k);
}

inline NVNshaderControl *ctl(std::vector<u8> &ct) {
    return reinterpret_cast<NVNshaderControl *>(ct.data());
}
inline const NVNshaderControl *ctl(const std::vector<u8> &ct) {
    return reinterpret_cast<const NVNshaderControl *>(ct.data());
}

inline u32 const_off(const std::vector<u8> &ct) {
    return ctl(ct)->mConstBufOffset;
}

enum {
    P_RD = 1, P_RD2 = 2, P_RA = 4, P_RB = 8, P_RB2 = 16, P_IB = 32,
    P_RC = 64, P_PD = 128, P_LPD = 256, P_SPD = 384, P_TPD = 512,
    P_VPD = 640, P_PDN = 1024, P_PS = 2048, P_TEX = 4096, P_TEXB = 8192,
    P_BRA = 16384, P_NOPRED = 32768
};

enum { FORM_IMM = 0, FORM_CBUF = 1, FORM_REG = 2 };

enum {
    C_SSY = 0, C_PBK, C_PCNT, C_SYNC, C_BRK, C_CONT, C_BRA, C_BRX, C_EXIT,
    C_OTHER
};

static const int MAX_DEPTH = 64;

static const int CBUF_SRCB_TOP5 = 0x09;
static const int CBUF_SRCC_TOP5 = 0x0A;

class UbError : public std::runtime_error {
public:
    explicit UbError(const std::string &m) : std::runtime_error(m) {}
};

[[noreturn]] void fail(const char *fmt, ...);

static const int MASKW = 24;

struct Mask {
    u64 w[MASKW];
    Mask() { clear(); }
    void clear() { std::memset(w, 0, sizeof w); }
    bool test(int b) const { return (w[b >> 6] >> (b & 63)) & 1u; }
    void set(int b) { w[b >> 6] |= (u64)1 << (b & 63); }
    void reset(int b) { w[b >> 6] &= ~((u64)1 << (b & 63)); }
    bool any() const {
        for (int i = 0; i < MASKW; i++) if (w[i]) return true;
        return false;
    }
    bool operator==(const Mask &o) const {
        return std::memcmp(w, o.w, sizeof w) == 0;
    }
    bool operator!=(const Mask &o) const { return !(*this == o); }
    Mask &operator|=(const Mask &o) {
        for (int i = 0; i < MASKW; i++) w[i] |= o.w[i];
        return *this;
    }
    Mask &operator&=(const Mask &o) {
        for (int i = 0; i < MASKW; i++) w[i] &= o.w[i];
        return *this;
    }
    bool intersects(const Mask &o) const {
        for (int i = 0; i < MASKW; i++) if (w[i] & o.w[i]) return true;
        return false;
    }

    void andnot_or(const Mask &k, const Mask &g) {
        for (int i = 0; i < MASKW; i++) w[i] = (w[i] & ~k.w[i]) | g.w[i];
    }
    void andnot(const Mask &k) {
        for (int i = 0; i < MASKW; i++) w[i] &= ~k.w[i];
    }
    int popcount() const {
        int n = 0;
        for (int i = 0; i < MASKW; i++) {
            u64 x = w[i];
            while (x) { x &= x - 1; n++; }
        }
        return n;
    }
    void bits(std::vector<int> &out) const {
        out.clear();
        for (int i = 0; i < MASKW; i++) {
            u64 x = w[i];
            while (x) {
                int b = __builtin_ctzll(x);
                out.push_back(i * 64 + b);
                x &= x - 1;
            }
        }
    }
};

typedef std::vector<std::pair<int32_t, u32>> VMap;

inline const u32 *vmap_get(const VMap &m, int32_t k) {
    size_t lo = 0, hi = m.size();
    while (lo < hi) {
        size_t mid = (lo + hi) >> 1;
        if (m[mid].first < k) lo = mid + 1; else hi = mid;
    }
    if (lo < m.size() && m[lo].first == k) return &m[lo].second;
    return nullptr;
}
inline void vmap_set(VMap &m, int32_t k, u32 v) {
    size_t lo = 0, hi = m.size();
    while (lo < hi) {
        size_t mid = (lo + hi) >> 1;
        if (m[mid].first < k) lo = mid + 1; else hi = mid;
    }
    if (lo < m.size() && m[lo].first == k) m[lo].second = v;
    else m.insert(m.begin() + (long)lo, std::make_pair(k, v));
}
inline void vmap_erase(VMap &m, int32_t k) {
    size_t lo = 0, hi = m.size();
    while (lo < hi) {
        size_t mid = (lo + hi) >> 1;
        if (m[mid].first < k) lo = mid + 1; else hi = mid;
    }
    if (lo < m.size() && m[lo].first == k) m.erase(m.begin() + (long)lo);
}

struct EMap {
    typedef std::pair<int32_t, int32_t> value_type;
    typedef std::vector<value_type>::iterator iterator;
    typedef std::vector<value_type>::const_iterator const_iterator;
    std::vector<value_type> v;

    iterator begin() { return v.begin(); }
    iterator end() { return v.end(); }
    const_iterator begin() const { return v.begin(); }
    const_iterator end() const { return v.end(); }
    size_t size() const { return v.size(); }
    bool empty() const { return v.empty(); }

    iterator lower(int32_t k) {
        return std::lower_bound(v.begin(), v.end(), k,
            [](const value_type &a, int32_t b) { return a.first < b; });
    }
    const_iterator lower(int32_t k) const {
        return std::lower_bound(v.begin(), v.end(), k,
            [](const value_type &a, int32_t b) { return a.first < b; });
    }
    iterator find(int32_t k) {
        iterator it = lower(k);
        return (it != v.end() && it->first == k) ? it : v.end();
    }
    const_iterator find(int32_t k) const {
        const_iterator it = lower(k);
        return (it != v.end() && it->first == k) ? it : v.end();
    }
    size_t count(int32_t k) const { return find(k) != v.end() ? 1 : 0; }
    int32_t &operator[](int32_t k) {
        iterator it = lower(k);
        if (it == v.end() || it->first != k)
            it = v.insert(it, std::make_pair(k, (int32_t)0));
        return it->second;
    }
    iterator erase(iterator it) { return v.erase(it); }
    size_t erase(int32_t k) {
        iterator it = find(k);
        if (it == v.end()) return 0;
        v.erase(it);
        return 1;
    }
};

const char *op_name(int op);
int op_id(const char *name);
int decode_op(u64 q);
unsigned decode_props(u64 q);

typedef std::vector<char> OpSet;
OpSet make_opset(std::initializer_list<const char *> names);

inline int _rd(u64 q) { return (int)(q & 0xFF); }
inline int _ra(u64 q) { return (int)((q >> 8) & 0xFF); }
inline int _predf(u64 q) { return (int)((q >> 16) & 7); }
inline int _pinv(u64 q) { return (int)((q >> 19) & 1); }

inline int tex_handle(u64 q) { return (int)((q >> 36) & 0x1FFF); }
inline int cbuf_bank(u64 q) { return (int)((q >> 34) & 0x1F); }
inline int cbuf_off(u64 q) { return (int)(((q >> 20) & 0x3FFF) << 2); }
inline int cbuf_top5(u64 q) { return (int)((q >> 59) & 0x1F); }
inline bool srcc_form(u64 q) { return cbuf_top5(q) == CBUF_SRCC_TOP5; }

inline int srcb_form(u64 q) {
    if (((q >> 61) & 7) == 1) return FORM_IMM;
    if (!((q >> 60) & 1)) return FORM_CBUF;
    return FORM_REG;
}
inline u32 imm20i(u64 q) {
    return (u32)(((q >> 37) & 0x80000) | ((q >> 20) & 0x7FFFF));
}
inline int32_t imm20i_signed(u64 q) {
    u32 v = imm20i(q);
    return (v & 0x80000) ? (int32_t)(v - (1u << 20)) : (int32_t)v;
}
inline u32 imm32(u64 q) { return (u32)((q >> 20) & 0xFFFFFFFFull); }

inline int32_t sext24(u32 v) {
    return (v >= 0x800000) ? (int32_t)v - 0x1000000 : (int32_t)v;
}

inline int32_t branch_imm(u64 q) { return sext24((u32)((q >> 20) & 0xFFFFFF)); }

inline int32_t lmem_off(u64 q)   { return sext24((u32)((q >> 20) & 0xFFFFFF)); }

inline bool branch_disp_ok(long disp) {
    return disp >= -0x800000 && disp < 0x800000;
}
inline u64 setbits(u64 q, int lo, int width, u64 val) {
    u64 m = (((u64)1 << width) - 1) << lo;
    return (q & ~m) | ((val & (((u64)1 << width) - 1)) << lo);
}
inline u64 set_field8(u64 q, int off, int val) {
    return (q & ~((u64)0xFF << off)) | ((u64)(val & 0xFF) << off);
}

struct LdcFields { int rd, ra, off, bank, mode; };
inline LdcFields ldc_fields(u64 q) {
    LdcFields f;
    f.rd = (int)(q & 0xFF);
    f.ra = (int)((q >> 8) & 0xFF);
    f.off = (int)((q >> 20) & 0xFFFF);
    f.bank = (int)((q >> 36) & 0x1F);
    f.mode = (int)((q >> 44) & 3);
    return f;
}

enum { STRICT_IADD = 1, STRICT_SHFL = 2, STRICT_ALD = 4, STRICT_ALL = 7 };
extern int g_strict_decode;

int mem_data_regs(u64 q, int op);

int gpr_src_offsets(u64 q, int op, unsigned props, int *offs);

int pred_src_offsets(int op, unsigned props, int *offs);

bool cbuf_read_of(u64 q, int nm, int *bank, int *off);

int spurious_pred(int nm, u64 q);

std::vector<u8> read_file(const std::string &p);

u64 xxh3_64(const void *data, size_t len);

struct RSet {
    u64 r[4];
    u8 p;
    RSet() { clear(); }
    void clear() { r[0] = r[1] = r[2] = r[3] = 0; p = 0; }
    void add(int x) {
        if (x >= PREG) { if (x - PREG < 7) p |= (u8)(1 << (x - PREG)); }
        else if (x >= 0 && x < 255) r[x >> 6] |= (u64)1 << (x & 63);
    }
    bool has(int x) const {
        if (x >= PREG) return (x - PREG < 7) && ((p >> (x - PREG)) & 1);
        return (x >= 0 && x < 255) && ((r[x >> 6] >> (x & 63)) & 1);
    }
    bool any() const { return r[0] || r[1] || r[2] || r[3] || p; }
    int count() const {
        int n = 0;
        for (int i = 0; i < 4; i++) { u64 x = r[i]; while (x) { x &= x - 1; n++; } }
        for (int i = 0; i < 7; i++) if ((p >> i) & 1) n++;
        return n;
    }
    void unite(const RSet &o) {
        for (int i = 0; i < 4; i++) r[i] |= o.r[i];
        p |= o.p;
    }
    bool operator==(const RSet &o) const {
        return r[0] == o.r[0] && r[1] == o.r[1] && r[2] == o.r[2] &&
               r[3] == o.r[3] && p == o.p;
    }
    void list(std::vector<int> &out) const {
        out.clear();
        for (int i = 0; i < 4; i++) {
            u64 x = r[i];
            while (x) { int b = __builtin_ctzll(x); out.push_back(i * 64 + b); x &= x - 1; }
        }
        for (int i = 0; i < 7; i++) if ((p >> i) & 1) out.push_back(PREG + i);
    }
    void to_mask(Mask &m) const {
        for (int i = 0; i < 4; i++) m.w[i] |= r[i];
        m.w[4] |= (u64)p;
    }
};

struct Program {
    std::vector<u8> bc, ct;
    u32 co = 0;
    const u8 *blob = nullptr;
    size_t blobsz = 0;

    int n = 0;
    std::vector<int> rel;
    std::vector<u64> q;
    std::vector<int16_t> op;
    std::vector<uint16_t> props;
    std::unordered_map<int, int> idx_of;

    std::vector<RSet> defs, maydefs, uses;

    void load_paths(const std::string &bcp, const std::string &ctp);
    void load_bytes(std::vector<u8> b, std::vector<u8> c);
    void build();

    const char *name(int i) const { return op_name(op[i]); }
    int snap(int addr) const;
    bool guarded(int i) const;
    bool never(int i) const;
    int target(int i) const;
    bool blob_u32(int byte_off, u32 *out) const;
    void du(int i, RSet &d, RSet &md, RSet &u) const;
    static void du_word(u64 qq, int nm, unsigned pr, RSet &d, RSet &md, RSet &u);
};

void tex_defs(u64 q, int nm, RSet &out);
void tex_uses(u64 q, int nm, RSet &out);

struct CFGraph {
    const Program *prog = nullptr;
    int n = 0;
    std::vector<int8_t> cat;
    std::vector<int> tgt;
    std::vector<char> grd, nev;
    std::vector<std::vector<int>> succ;
    std::vector<std::vector<int>> pred;
    std::vector<char> unknown;
    bool overflow = false;

    void build(const Program &p, bool seed_orphans);
    std::vector<char> reachable_from_entry() const;
};

struct OpSets {
    OpSet no_dest, no_pred, store_ops, widemem, texs_fam, tex_fam, tex_bases;
    OpSet setp_fam;
    OpSet pred39_list;
    OpSet side_effect;
    OpSet branchy, pushy, freebie;
    OpSet alu_cbuf, alu_cbuf_srcc, pure_cse;
    OpSet alu_srcb, imm32_ops, transparent;
    OpSet pred_src_ok, branchy_imm, pred39_spurious;

    OpSet pred39_gpr;
    OpSet spec_side_effect;
    OpSet spec_control;
    OpSet safe_ops;
    OpSet load_or_store, global_store, fp64, local_ops;
    OpSet ctl_texs_fam, ctl_tex_fam, ctl_tex_bindless;
    OpSet tex_ops_audit;

    int O_Nop, O_Mov, O_Mov32i, O_Ldc, O_Stl, O_Ldl, O_Invalid, O_Shfl;
    int O_Bra, O_Jmp, O_Ssy, O_Pbk, O_Pcnt, O_Cal, O_Brx, O_Jmx, O_Sync;
    int O_Brk, O_Cont, O_Exit, O_Ret, O_Kil, O_Isetp, O_Psetp, O_Iset;
    int O_Imnmx, O_Sel, O_Shl, O_Shr, O_Iadd, O_Iadd32i, O_Lop, O_Lop32i;
    int O_Fsetp, O_Fset, O_Fmnmx, O_Pset, O_Xmad, O_Ffma, O_Texs, O_Ast;
    int O_Iadd3, O_Ald, O_Al2p, O_F2f, O_F2i, O_I2f, O_I2i;
    int O_Fadd, O_Fmul;
    int O_P2r, O_Vote, O_Votevtg, O_Flo, O_Popc;
};
const OpSets &S();

struct PerfCounters {
    long long n_compose = 0;
    long long n_compose_lm = 0, n_compose_cp = 0, n_compose_top = 0;
    long long n_run3 = 0, n_alloc = 0, n_emitbody = 0, n_renumber = 0;
    long long n_fill = 0;
    long long n_run3_hit = 0, n_alloc_hit = 0;
    long long n_emit_dup = 0, n_rn_hit = 0, n_fill_hit = 0;
    double t_run3 = 0, t_alloc = 0, t_webreg = 0, t_postco = 0, t_copyco = 0,
           t_emitbody = 0, t_reorder = 0, t_fill = 0, t_renumber = 0,
           t_control = 0;
    double x[16] = {0};
    long long xn[16] = {0};
};
extern PerfCounters g_perf;
double perf_now();
struct PerfScope {
    double *acc; double t0;
    explicit PerfScope(double *a) : acc(a), t0(perf_now()) {}
    ~PerfScope() { *acc += perf_now() - t0; }
};

}

#endif
