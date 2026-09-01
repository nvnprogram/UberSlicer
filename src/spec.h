
#ifndef UBERSPEC_SPEC_H
#define UBERSPEC_SPEC_H

#include "uber.h"

namespace ub {

struct Mask263 {
    u64 w[5];
    Mask263() { std::memset(w, 0, sizeof w); }
    void set(int b) { w[b >> 6] |= (u64)1 << (b & 63); }
    bool operator==(const Mask263 &o) const {
        return std::memcmp(w, o.w, sizeof w) == 0;
    }
    bool intersects(const Mask &m) const {
        for (int i = 0; i < 5; i++) if (w[i] & m.w[i]) return true;
        return false;
    }
    void unite(const Mask &m) { for (int i = 0; i < 5; i++) w[i] |= m.w[i]; }
};

struct CseKey {
    int op;
    u64 qm;
    int32_t ns;
    int32_t s[8];
    CseKey() : op(0), qm(0), ns(0) { std::memset(s, 0, sizeof s); }
    void add(int32_t v) {
        if (ns >= 8) fail("CseKey: more than 8 GPR sources");
        s[ns++] = v;
    }
    bool operator==(const CseKey &o) const {
        if (op != o.op || qm != o.qm || ns != o.ns) return false;
        return std::memcmp(s, o.s, (size_t)ns * sizeof s[0]) == 0;
    }
    bool operator<(const CseKey &o) const {
        if (op != o.op) return op < o.op;
        if (qm != o.qm) return qm < o.qm;
        if (ns != o.ns) return ns < o.ns;
        return std::memcmp(s, o.s, (size_t)ns * sizeof s[0]) < 0;
    }
};
struct AvVal {
    int d;
    Mask263 dm;
    bool operator==(const AvVal &o) const { return d == o.d && dm == o.dm; }
};
struct AvMap {
    typedef std::pair<CseKey, AvVal> value_type;
    typedef std::vector<value_type>::iterator iterator;
    typedef std::vector<value_type>::const_iterator const_iterator;
    std::vector<value_type> v;

    iterator begin() { return v.begin(); }
    iterator end() { return v.end(); }
    const_iterator begin() const { return v.begin(); }
    const_iterator end() const { return v.end(); }
    bool empty() const { return v.empty(); }
    size_t size() const { return v.size(); }

    iterator lower(const CseKey &k) {
        return std::lower_bound(v.begin(), v.end(), k,
            [](const value_type &a, const CseKey &b) { return a.first < b; });
    }
    iterator find(const CseKey &k) {
        iterator it = lower(k);
        return (it != v.end() && it->first == k) ? it : v.end();
    }
    const_iterator find(const CseKey &k) const {
        const_iterator it = std::lower_bound(v.begin(), v.end(), k,
            [](const value_type &a, const CseKey &b) { return a.first < b; });
        return (it != v.end() && it->first == k) ? it : v.end();
    }
    AvVal &operator[](const CseKey &k) {
        iterator it = lower(k);
        if (it == v.end() || !(it->first == k))
            it = v.insert(it, std::make_pair(k, AvVal()));
        return it->second;
    }
    iterator erase(iterator it) { return v.erase(it); }
};

typedef int8_t Tri;
static const Tri TRI_T = 1, TRI_F = 0, TRI_U = -1;

struct StackPoolV {
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

struct RunRes {

    std::vector<char> visited;
    std::vector<int> reach;
    std::vector<char> in_reach;
    std::vector<VMap> vals;
    std::vector<std::vector<int>> stacks;
    StackPoolV pool;
    long long states = 0;

    std::vector<std::vector<int>> succ;
    std::vector<Tri> guard;
    std::vector<char> need, noop, dead2;
    std::vector<int> kept;
    std::vector<EMap> env;
    std::vector<Mask> live_in, gen, kill;
    int rounds = 0;

    std::vector<std::unordered_map<int, int>> mul_in;
    std::vector<int> fmac;
    std::vector<int8_t> fmac_slot;
};

enum {
    FOLD_PSET = 1, FOLD_FPRED = 2, FOLD_FCMP = 4, FOLD_XMAD = 8,
    FOLD_LMVAL = 16,

    FOLD_FVAL = 32
};
static const int FOLD_ALL = FOLD_PSET | FOLD_FPRED | FOLD_FCMP | FOLD_XMAD |
                            FOLD_LMVAL;

struct EvalOut {
    bool present = false;
    std::vector<std::pair<int32_t, u32>> kv;
    void put(int32_t k, u32 v) { present = true; kv.push_back({k, v}); }
    const u32 *get(int32_t k) const {
        for (auto &p : kv) if (p.first == k) return &p.second;
        return nullptr;
    }
};

extern bool g_cse_mov32i;

extern bool g_fmac;
extern bool g_fmac_all;

struct LmSlot { int off = 0, w = 0; bool store = false; bool valid = false; };

class Spec {
public:
    const Program *p = nullptr;
    int bank = 6;
    bool fold_blob = true;
    int folds = 0;
    bool texrw = false;
    bool lm_dse = false, copyprop = true, lmfwd = true, cbfold = true,
         cse = true, fix_maydef = true;
    Mask exit_mask;

    std::vector<int8_t> cat;
    std::vector<int> tgt;
    std::vector<std::vector<int32_t>> dd;
    std::vector<int8_t> pnum, pinv;
    std::vector<char> nopred;

    std::vector<Mask> def_mask, dall_mask;
    std::vector<std::vector<int>> use_list;
    std::vector<std::vector<int>> maydef_set;
    std::vector<int> copy_src;
    std::vector<int> cb_src_d;
    std::vector<int32_t> cb_src_key;
    std::vector<std::vector<int>> cb_slots;
    std::vector<char> norw;
    std::vector<char> cse_ok;
    std::vector<int> cse_dst;
    std::vector<u64> cse_base_q;
    std::vector<std::vector<int>> cse_srcoff;
    std::vector<Mask> cse_pmask;
    std::vector<LmSlot> lm;
    bool lm_ok = true, lm_live = false, stl_is_se = true, lmval = false;
    std::vector<char> is_se, is_branchy, is_pushy, is_free;
    std::vector<char> tex_rw, tex_dstgroup;
    std::vector<RSet> truesrc;
    int n_fixed = 0;

    const std::vector<u32> *opt = nullptr;

    void init(const Program &prog, int opt_bank, const std::vector<int> &exit_live,
              bool lm_dse_, bool cbfold_, int folds_, bool texrw_);

    void run(const std::vector<u32> &optvals, RunRes &R);

    void run3(const std::vector<u32> &optvals, RunRes &R);
    void dce_pass(RunRes &R);

    int cbfold_slot(int i, const EMap &env) const;

    bool fmac_ok(const RunRes &R, int i, int *jout, int *slotout) const;
    u64 fmac_word(const RunRes &R, int i, int j, int slot) const;
    void fmac_uses(const RunRes &R, int i, std::vector<int> &out) const;
    bool fmac_mul_ok(int j) const;

    bool cb(int bank_, int off, u32 *out) const;
    Tri predval(const VMap &v, int pn, int inv) const;

private:
    bool srcbval(u64 q, const VMap &v, u32 *out) const;
    bool regval(const VMap &v, int r, u32 *out) const;
    void lop_out(u64 q, int lop, bool ha, u32 a, bool hb, u32 b, int d, int pd,
                 int pop, EvalOut &out) const;
    void eval(int i, const VMap &v, EvalOut &out) const;
    void eval5(int i, const VMap &v, EvalOut &out) const;
    void succ_of(const RunRes &R, std::vector<std::vector<int>> &succ) const;
    void copyprop_pass(RunRes &R) const;
};

const RunRes &run3_cached(Spec &sp, const std::vector<u32> &optvals);
void run3_cache_clear();

bool xmad_shape(u64 q, int *sela, int *selb, int *psl, int *mrg, int *cbcc);
u32 xmad_value(u32 sa, int hia, u32 sb, int hib, u32 sc, int psl, int mrg,
               int cbcc);

}

#endif
