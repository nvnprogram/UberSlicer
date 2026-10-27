
#include "sm86.h"
#include <cstdio>
#include <cstring>
#include "sm86tab.h"

namespace ub {
namespace sm86 {

void RSet86::list(std::vector<int> &out) const {
    out.clear();
    for (int i = 0; i < 6; i++) {
        u64 x = w[i];
        while (x) {
            int b = __builtin_ctzll(x);
            out.push_back(i * 64 + b);
            x &= x - 1;
        }
    }
}

static u64 field_raw(const Word &w, const FieldDesc86 &f) {
    u64 v = 0;
    for (int r = 0; r < f.nr; r++) {
        int hi = f.r[r][0], lo = f.r[r][1], n = hi - lo + 1;
        v = (v << n) | bits(w, lo, n);
    }
    return v;
}

static void field_put(Word &w, const FieldDesc86 &f, u64 v) {
    int pos = f.width;
    for (int r = 0; r < f.nr; r++) {
        int hi = f.r[r][0], lo = f.r[r][1], n = hi - lo + 1;
        pos -= n;
        put_bits(w, lo, n, (v >> pos) & (n >= 64 ? ~(u64)0 : (((u64)1 << n) - 1)));
    }
}

static int table_row(int t, u64 raw) {
    const TabDesc86 &d = TABS[t];
    if (raw >= d.ninv) return -1;
    int r = TINV[d.inv0 + raw];
    return r < 0 ? -1 : d.row0 + r;
}

static int64_t val_of(const ClassDesc86 &c, const Word &w, int v) {
    const ValDesc86 &d = VALS[c.v0 + v];
    if (d.field < 0) return d.dflt;
    const FieldDesc86 &f = FIELDS[c.f0 + d.field];
    u64 raw = field_raw(w, f);
    if (f.kind == 3) {
        int r = table_row(f.table, raw);
        return r < 0 ? -1 : TROWS[r][1 + d.targ];
    }
    int64_t x = (int64_t)raw;
    if (d.sign && !f.conv && f.width < 64 && ((raw >> (f.width - 1)) & 1))
        x -= (int64_t)1 << f.width;
    return x * f.scale;
}

static bool in_domains(const ClassDesc86 &c, const Word &w) {
    for (int k = 0; k < c.nd; k++) {
        const DomDesc86 &d = DOMS[c.d0 + k];
        u64 v = 0;
        for (int r = 0; r < d.nr; r++) {
            int n = d.r[r][0] - d.r[r][1] + 1;
            v = (v << n) | bits(w, d.r[r][1], n);
        }
        if (v >= 256 || !((d.set[v >> 6] >> (v & 63)) & 1)) return false;
    }
    return true;
}

static int match_class(const Word &w) {
    int key = (int)((((w.hi >> 27) & 1) << 12) | (w.lo & 0xfff));
    for (int e = BUCKET[key]; e < BUCKET[key + 1]; e++) {
        const EntryDesc86 &E = ENTRIES[e];
        if ((w.lo & E.mlo) != E.vlo || (w.hi & E.mhi) != E.vhi) continue;
        if (!in_domains(CLASSES[E.cls], w)) continue;
        return E.cls;
    }
    return -1;
}

bool decode(Word w, Inst *out) {
    out->w = w;
    out->cls = (int16_t)match_class(w);
    out->op = out->cls >= 0 ? (int16_t)CLASSES[out->cls].op : 0;
    return out->cls >= 0;
}

const char *op_name(int op) { return op >= 0 && op < NOPS ? OP_NAME[op] : "INVALID"; }
int nclasses() { return NCLASS; }
int nops() { return NOPS; }
int op_id(const char *name) {
    for (int i = 0; i < NOPS; i++)
        if (!strcmp(OP_NAME[i], name)) return i;
    return -1;
}

const char *val_name(int cls, int v) { return VALS[CLASSES[cls].v0 + v].name; }
int val_index(int cls, const char *name) {
    const ClassDesc86 &c = CLASSES[cls];
    for (int v = 0; v < c.nvals; v++)
        if (!strcmp(VALS[c.v0 + v].name, name)) return v;
    return -1;
}

int64_t get(const Inst &i, int v) {
    if (i.cls < 0 || v < 0) return 0;
    return val_of(CLASSES[i.cls], i.w, v);
}

void get_all(const Inst &i, int64_t *out) {
    const ClassDesc86 &c = CLASSES[i.cls];
    for (int v = 0; v < c.nvals; v++) out[v] = val_of(c, i.w, v);
}

static bool direct_raw(const ValDesc86 &d, const FieldDesc86 &f, int64_t x, u64 *raw) {
    if (f.scale > 1 && x % f.scale) return false;
    int64_t r = x / f.scale;
    if (d.sign && !f.conv) {
        int64_t lo = -((int64_t)1 << (f.width - 1)), hi = ((int64_t)1 << (f.width - 1)) - 1;
        if (r < lo || r > hi) return false;
    } else if (r < 0 || (f.width < 64 && (u64)r >> f.width)) {
        return false;
    }
    *raw = (u64)r & (f.width >= 64 ? ~(u64)0 : (((u64)1 << f.width) - 1));
    return true;
}

static int64_t table_lookup(int t, int n, const int64_t *a) {
    const TabDesc86 &d = TABS[t];
    for (int r = 0; r < d.nrows; r++) {
        const int32_t *row = TROWS[d.row0 + r];
        bool ok = true;
        for (int k = 0; k < n && ok; k++) ok = row[1 + k] == a[k];
        if (ok) return row[0];
    }
    return -1;
}

static bool set_word(int cls, Word &w, int v, int64_t x) {
    const ClassDesc86 &c = CLASSES[cls];
    const ValDesc86 &d = VALS[c.v0 + v];
    if (d.field < 0) return x == d.dflt;
    const FieldDesc86 &f = FIELDS[c.f0 + d.field];
    u64 raw;
    if (f.kind == 3) {
        int64_t a[5];
        for (int k = 0; k < f.nargs; k++) {
            int av = FARGS[f.arg0 + k];
            a[k] = av == v ? x : val_of(c, w, av);
        }
        int64_t r = table_lookup(f.table, f.nargs, a);
        if (r < 0) return false;
        raw = (u64)r;
    } else if (f.kind == 2) {
        if (!direct_raw(d, f, x, &raw)) return false;
    } else {
        return x == f.cval;
    }
    field_put(w, f, raw);
    return true;
}

bool set(Inst &i, int v, int64_t x) {
    if (i.cls < 0 || v < 0 || v >= CLASSES[i.cls].nvals) return false;
    Word w = i.w;
    if (!set_word(i.cls, w, v, x)) return false;
    if (match_class(w) != i.cls) return false;
    i.w = w;
    return true;
}

int guard(const Inst &i, bool *uniform, bool *neg) {
    const ClassDesc86 &c = CLASSES[i.cls];
    if (uniform) *uniform = c.guard_uniform != 0;
    if (neg) *neg = c.v_guard_not >= 0 && val_of(c, i.w, c.v_guard_not) != 0;
    return c.v_guard >= 0 ? (int)val_of(c, i.w, c.v_guard) : 7;
}

static int nregs_of(const OpndDesc86 &o, const int64_t *V, int64_t reg) {
    switch (o.kind) {
    case O_GPR:
        if (reg >= 255) return 0;
        return o.size >= 0 ? (int)((size_bits(o.size, V, 0) + 31) / 32) : 1;
    case O_UR:
        if (reg >= 63) return 0;
        return o.size >= 0 ? (int)((size_bits(o.size, V, 0) + 31) / 32) : 1;
    case O_PRED:
    case O_UPRED:
        return reg >= 7 ? 0 : 1;
    case O_BAR:
        return reg >= 0 && reg < 16 ? 1 : 0;
    case O_PR:
    case O_UPR:
        return 7;
    default:
        return 0;
    }
}

int operands(const Inst &i, Operand *out, int max) {
    if (i.cls < 0) return 0;
    const ClassDesc86 &c = CLASSES[i.cls];
    int64_t V[MAX_VALS];
    get_all(i, V);
    int n = 0;
    for (int k = 0; k < c.no && n < max; k++) {
        const OpndDesc86 &o = OPNDS[c.o0 + k];
        Operand &r = out[n++];
        int64_t x = o.val >= 0 ? V[o.val] : 0;
        r.kind = o.kind;
        r.role = o.role;
        r.val = o.val;
        r.parent = o.parent;
        r.slot = o.slot;
        r.name = o.name;
        r.imm = x;
        bool isreg = o.kind <= O_UPR;
        r.reg = isreg ? (int32_t)x : -1;
        r.nregs = (u8)nregs_of(o, V, x);
        r.flags = 0;
        if (o.v_neg >= 0 && V[o.v_neg]) r.flags |= F_NEG;
        if (o.v_abs >= 0 && V[o.v_abs]) r.flags |= F_ABS;
        if (o.v_inv >= 0 && V[o.v_inv]) r.flags |= F_INV;
        if (o.v_not >= 0 && V[o.v_not]) r.flags |= F_NOT;
        if (o.v_reuse >= 0 && V[o.v_reuse]) r.flags |= F_REUSE;
    }
    return n;
}

bool set_reg(Inst &i, const Operand &o, int reg) {
    if (o.val < 0) return false;
    return set(i, o.val, reg);
}

static void add_tuple(RSet86 *s, int kind, int64_t reg, int n) {
    for (int k = 0; k < n; k++) {
        int64_t r = reg + k;
        switch (kind) {
        case O_GPR: if (r < 255) s->add(key_gpr((int)r)); break;
        case O_UR: if (r < 63) s->add(key_ur((int)r)); break;
        case O_PRED: if (r < 7) s->add(key_p((int)r)); break;
        case O_UPRED: if (r < 7) s->add(key_up((int)r)); break;
        case O_BAR: if (r >= 0 && r < 16) s->add(key_b((int)r)); break;
        case O_PR: s->add(key_p(k)); break;
        case O_UPR: s->add(key_up(k)); break;
        }
    }
}

static int pr_mask(const ClassDesc86 &c, const int64_t *V) {
    for (int k = 0; k < c.no; k++) {
        const OpndDesc86 &o = OPNDS[c.o0 + k];
        if (o.kind == O_IMM && o.val >= 0 && !strcmp(o.name, "Sb")) return (int)(V[o.val] & 0x7f);
    }
    return -1;
}

void def_use(const Inst &i, RSet86 *def, RSet86 *use) {
    def->clear();
    use->clear();
    if (i.cls < 0) return;
    const ClassDesc86 &c = CLASSES[i.cls];
    int64_t V[MAX_VALS];
    get_all(i, V);
    if (c.v_guard >= 0 && V[c.v_guard] != 7) {
        if (c.guard_uniform) use->add(key_up((int)V[c.v_guard]));
        else use->add(key_p((int)V[c.v_guard]));
    }
    for (int k = 0; k < c.no; k++) {
        const OpndDesc86 &o = OPNDS[c.o0 + k];
        if (o.role == R_NONE || o.val < 0) continue;
        int64_t reg = V[o.val];
        int n = nregs_of(o, V, reg);
        if (!n) continue;
        if (o.kind == O_PR || o.kind == O_UPR) {

            int mask = pr_mask(c, V);
            RSet86 *s = (c.op == OP_R2P || c.op == OP_UR2UP) ? def : use;
            int base = o.kind == O_PR ? KEY_P : KEY_UP;
            if (mask >= 0) {
                for (int b = 0; b < 7; b++) if ((mask >> b) & 1) s->add(base + b);
                continue;
            }
        }
        if (o.role == R_DEF || o.role == R_DEFUSE) add_tuple(def, o.kind, reg, n);
        if (o.role == R_USE || o.role == R_DEFUSE) add_tuple(use, o.kind, reg, n);
    }

    if (c.op == OP_MOV) {
        int pm = val_index(i.cls, "PixMaskU04");
        if (pm >= 0 && V[pm] != 0xf) use->unite(*def);
    }
}

void def_use_split(const Inst &i, RSet86 *def, RSet86 *maydef, RSet86 *use) {
    def_use(i, def, use);
    maydef->clear();
    bool neg = false;
    int g = i.cls >= 0 ? guard(i, nullptr, &neg) : 7;
    if (g != 7 || neg) {
        *maydef = *def;
        def->clear();
        use->unite(*maydef);
    }
}

Ctl ctl_get(const Word &w) {
    Ctl c;
    c.pm = (u8)bits(w, 102, 2);
    c.stall = (u8)bits(w, 105, 4);
    c.yld = (u8)bits(w, 109, 1);
    c.wr = (u8)bits(w, 110, 3);
    c.rd = (u8)bits(w, 113, 3);
    c.wait = (u8)bits(w, 116, 6);
    c.hi3 = (u8)bits(w, 122, 3);
    return c;
}

Word ctl_set(Word w, const Ctl &c) {
    put_bits(w, 102, 2, c.pm);
    put_bits(w, 105, 4, c.stall);
    put_bits(w, 109, 1, c.yld);
    put_bits(w, 110, 3, c.wr);
    put_bits(w, 113, 3, c.rd);
    put_bits(w, 116, 6, c.wait);
    put_bits(w, 122, 3, c.hi3);
    return w;
}

bool ctl_valid(const Inst &i) {
    if (i.cls < 0) return false;
    const ClassDesc86 &c = CLASSES[i.cls];
    if (c.f_opex < 0) return true;
    const FieldDesc86 &f = FIELDS[c.f0 + c.f_opex];
    return table_row(f.table, field_raw(i.w, f)) >= 0;
}

int ctl_reuse(const Inst &i) {
    if (i.cls < 0) return 0;
    const ClassDesc86 &c = CLASSES[i.cls];
    int r = 0;
    if (c.v_reuse_a >= 0 && val_of(c, i.w, c.v_reuse_a) > 0) r |= 1;
    if (c.v_reuse_b >= 0 && val_of(c, i.w, c.v_reuse_b) > 0) r |= 2;
    if (c.v_reuse_c >= 0 && val_of(c, i.w, c.v_reuse_c) > 0) r |= 4;
    return r;
}

bool encode(int cls, const int64_t *vals, Word *out) {
    if (cls < 0 || cls >= NCLASS) return false;
    const ClassDesc86 &c = CLASSES[cls];
    Word w = {c.conv_lo, c.conv_hi};
    for (int k = 0; k < c.nf; k++) {
        const FieldDesc86 &f = FIELDS[c.f0 + k];
        u64 raw;
        if (f.kind == 0 || f.kind == 1) {
            raw = (u64)f.cval;
        } else if (f.kind == 2) {
            if (f.same >= 0 && vals[f.same] != vals[f.val]) return false;
            if (!direct_raw(VALS[c.v0 + f.val], f, vals[f.val], &raw)) return false;
        } else {
            int64_t a[5];
            for (int j = 0; j < f.nargs; j++) a[j] = vals[FARGS[f.arg0 + j]];
            int64_t r = table_lookup(f.table, f.nargs, a);
            if (r < 0) return false;
            raw = (u64)r;
        }
        field_put(w, f, raw);
    }
    *out = w;
    return true;
}

Word unused_mask(int cls) {
    Word w = {CLASSES[cls].unused_lo, CLASSES[cls].unused_hi};
    return w;
}

ClassInfo info(int cls) {
    const ClassDesc86 &c = CLASSES[cls];
    ClassInfo r;
    r.itype = c.itype;
    r.vq = c.vq;
    r.branch_type = c.btype;
    r.min_wait = c.min_wait;
    r.valid_shaders = c.valid_shaders;
    r.flags = c.flags;
    r.space_rd = c.space_rd;
    r.space_wr = c.space_wr;
    return r;
}

}
}
