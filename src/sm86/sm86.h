
#ifndef UB_SM86_H
#define UB_SM86_H

#include <cstdint>
#include <cstddef>
#include <vector>

namespace ub {
namespace sm86 {

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;

struct Word {
    u64 lo, hi;
    bool operator==(const Word &o) const { return lo == o.lo && hi == o.hi; }
    bool operator!=(const Word &o) const { return !(*this == o); }
};

inline u64 bits(const Word &w, int lo, int width) {
    u64 m = width >= 64 ? ~(u64)0 : (((u64)1 << width) - 1);
    if (lo >= 64) return (w.hi >> (lo - 64)) & m;
    u64 v = w.lo >> lo;
    if (lo + width > 64) v |= w.hi << (64 - lo);
    return v & m;
}
inline void put_bits(Word &w, int lo, int width, u64 val) {
    for (int k = 0; k < width; k++) {
        int b = lo + k;
        u64 bit = (val >> k) & 1;
        u64 &half = b >= 64 ? w.hi : w.lo;
        int s = b & 63;
        half = (half & ~((u64)1 << s)) | (bit << s);
    }
}

enum {
    KEY_P = 256,
    KEY_UP = 264,
    KEY_B = 272,
    KEY_UR = 320,
    KEY_COUNT = 384
};
enum RegFile { F_GPR, F_P, F_UP, F_B, F_UR, F_NONE };
inline int key_gpr(int n) { return n; }
inline int key_p(int n) { return KEY_P + n; }
inline int key_up(int n) { return KEY_UP + n; }
inline int key_b(int n) { return KEY_B + n; }
inline int key_ur(int n) { return KEY_UR + n; }
inline int key_file(int k) {
    if (k >= 0 && k < 255) return F_GPR;
    if (k >= KEY_P && k < KEY_P + 7) return F_P;
    if (k >= KEY_UP && k < KEY_UP + 7) return F_UP;
    if (k >= KEY_B && k < KEY_B + 16) return F_B;
    if (k >= KEY_UR && k < KEY_UR + 63) return F_UR;
    return F_NONE;
}
inline int key_num(int k) {
    switch (key_file(k)) {
    case F_GPR: return k;
    case F_P: return k - KEY_P;
    case F_UP: return k - KEY_UP;
    case F_B: return k - KEY_B;
    case F_UR: return k - KEY_UR;
    default: return -1;
    }
}

struct RSet86 {
    u64 w[6];
    RSet86() { clear(); }
    void clear() { for (int i = 0; i < 6; i++) w[i] = 0; }
    void add(int k) { if (key_file(k) != F_NONE) w[k >> 6] |= (u64)1 << (k & 63); }
    void remove(int k) { if (k >= 0 && k < KEY_COUNT) w[k >> 6] &= ~((u64)1 << (k & 63)); }
    bool has(int k) const {
        return k >= 0 && k < KEY_COUNT && ((w[k >> 6] >> (k & 63)) & 1);
    }
    bool any() const { for (int i = 0; i < 6; i++) if (w[i]) return true; return false; }
    int count() const {
        int n = 0;
        for (int i = 0; i < 6; i++) n += __builtin_popcountll(w[i]);
        return n;
    }
    void unite(const RSet86 &o) { for (int i = 0; i < 6; i++) w[i] |= o.w[i]; }
    bool intersects(const RSet86 &o) const {
        for (int i = 0; i < 6; i++) if (w[i] & o.w[i]) return true;
        return false;
    }
    bool operator==(const RSet86 &o) const {
        for (int i = 0; i < 6; i++) if (w[i] != o.w[i]) return false;
        return true;
    }
    bool operator!=(const RSet86 &o) const { return !(*this == o); }
    void list(std::vector<int> &out) const;

    template <class M> void to_mask(M &m) const {
        for (int i = 0; i < 6; i++)
            if (w[i]) { m.w[i] |= w[i]; m.set(i * 64 + __builtin_ctzll(w[i])); }
    }
};

struct Inst {
    Word w;
    int16_t cls;
    int16_t op;
};

bool decode(Word w, Inst *out);
const char *op_name(int op);
int nclasses();
int nops();
int op_id(const char *name);

const char *val_name(int cls, int v);
int val_index(int cls, const char *name);
int64_t get(const Inst &i, int v);

void get_all(const Inst &i, int64_t *out);

bool set(Inst &i, int v, int64_t x);
static const int MAX_VALS = 32;

enum OpndKind {
    O_GPR, O_UR, O_PRED, O_UPRED, O_BAR, O_PR, O_UPR, O_SREG, O_CBUF, O_UCBUF, O_MEM, O_ATTR,
    O_DESC, O_IMM, O_FIMM, O_REL, O_ENUM, O_OTHER
};
enum Role { R_NONE, R_DEF, R_USE, R_DEFUSE };
enum { F_NEG = 1, F_ABS = 2, F_INV = 4, F_NOT = 8, F_REUSE = 16 };
enum Slot { S_DEST, S_DEST2, S_SRCA, S_SRCB, S_SRCC, S_SRCE };

struct Operand {
    u8 kind;
    u8 role;
    u8 nregs;
    u8 flags;
    int16_t val;
    int8_t parent;
    int8_t slot;
    int32_t reg;
    int64_t imm;
    const char *name;
};
static const int MAX_OPNDS = 16;

int operands(const Inst &i, Operand *out, int max);

int guard(const Inst &i, bool *uniform, bool *neg);
bool set_reg(Inst &i, const Operand &o, int reg);

void def_use(const Inst &i, RSet86 *def, RSet86 *use);

void def_use_split(const Inst &i, RSet86 *def, RSet86 *maydef, RSet86 *use);

struct Ctl {
    u8 stall;
    u8 yld;
    u8 wr;
    u8 rd;
    u8 wait;
    u8 hi3;
    u8 pm;
};
Ctl ctl_get(const Word &w);
Word ctl_set(Word w, const Ctl &c);

bool ctl_valid(const Inst &i);

int ctl_reuse(const Inst &i);

bool encode(int cls, const int64_t *vals, Word *out);

Word unused_mask(int cls);

enum ShaderType { ST_UNKNOWN = 0, ST_PS = 1, ST_TI = 2, ST_TS = 3, ST_GS = 4, ST_CS = 5,
                  ST_VSA = 6, ST_VSB = 7 };

enum {
    CI_SIDE_EFFECT = 1 << 0, CI_ATOMIC = 1 << 1, CI_BRANCH = 1 << 2, CI_CONVERGENCE = 1 << 3,
    CI_SYNC = 1 << 4, CI_EXIT = 1 << 5, CI_FOLDABLE = 1 << 6, CI_CROSS_LANE = 1 << 7,
    CI_UNIFORM = 1 << 8, CI_VARLAT = 1 << 9, CI_VARLAT_SRC = 1 << 10
};
enum { SP_GLOBAL = 1, SP_SHARED = 2, SP_LOCAL = 4, SP_GENERIC = 8, SP_CONST = 16, SP_ATTR = 32,
       SP_SURFACE = 64, SP_TEXTURE = 128 };
struct ClassInfo {
    u8 itype;
    u8 vq;
    u8 branch_type;
    u8 min_wait;
    u8 valid_shaders;
    uint16_t flags;
    u8 space_rd, space_wr;
};
ClassInfo info(int cls);

}
}

#endif
