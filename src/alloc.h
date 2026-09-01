
#ifndef UBERSPEC_ALLOC_H
#define UBERSPEC_ALLOC_H

#include "spec.h"
#include <memory>

namespace ub {

struct UF {
    std::vector<int> p;
    int find(int x) {
        int r = x;
        for (;;) {
            if ((size_t)r >= p.size()) break;
            int nx = p[(size_t)r];
            if (nx == 0 || nx == r) break;
            r = nx;
        }
        while ((size_t)x < p.size()) {
            int nx = p[(size_t)x];
            if (nx == 0 || nx == x) break;
            p[(size_t)x] = r;
            x = nx;
        }
        return r;
    }
    int unite(int a, int b) {
        a = find(a); b = find(b);
        if (a != b) {
            if ((size_t)b >= p.size()) p.resize((size_t)b + 1, 0);
            p[(size_t)b] = a;
        }
        return a;
    }
};

struct DefMap {
    typedef std::pair<int, int> value_type;
    typedef std::vector<value_type>::iterator iterator;
    typedef std::vector<value_type>::const_iterator const_iterator;
    std::vector<value_type> v;

    iterator begin() { return v.begin(); }
    iterator end() { return v.end(); }
    const_iterator begin() const { return v.begin(); }
    const_iterator end() const { return v.end(); }
    size_t size() const { return v.size(); }
    bool empty() const { return v.empty(); }

    iterator lower(int k) {
        return std::lower_bound(v.begin(), v.end(), k,
            [](const value_type &a, int b) { return a.first < b; });
    }
    const_iterator lower(int k) const {
        return std::lower_bound(v.begin(), v.end(), k,
            [](const value_type &a, int b) { return a.first < b; });
    }
    iterator find(int k) {
        iterator it = lower(k);
        return (it != v.end() && it->first == k) ? it : v.end();
    }
    const_iterator find(int k) const {
        const_iterator it = lower(k);
        return (it != v.end() && it->first == k) ? it : v.end();
    }
    size_t count(int k) const { return find(k) != v.end() ? 1 : 0; }
    int &operator[](int k) {
        iterator it = lower(k);
        if (it == v.end() || it->first != k)
            it = v.insert(it, std::make_pair(k, 0));
        return it->second;
    }
};

struct DefTab {
    std::shared_ptr<std::vector<DefMap>> v;
    void assign(size_t n, const DefMap &d) {
        v = std::make_shared<std::vector<DefMap>>(n, d);
    }
    DefMap &operator[](size_t i) { return (*v)[i]; }
    const DefMap &operator[](size_t i) const { return (*v)[i]; }
};

struct Copy { int i, dw, sw; int kind; };

struct Alloc {
    std::vector<int> kept;
    std::unordered_map<int, int> ordn;
    int K = 0;
    DefTab st_in, st_out;
    std::vector<Mask> lout;
    std::vector<std::vector<int>> uses, hard, soft;
    std::vector<std::vector<int>> succ_k;
    UF uf;
    std::unordered_map<int, std::vector<u64>> livepts;
    std::set<int> constrained;
    std::vector<Copy> copies;
    std::unordered_map<int, int> base_root;
    int ndid = 0;
    std::vector<std::pair<int, int>> did_key;
    int n_after = 0, max_live = 0, undefined_uses = 0;

    int ord(int i) const { return ordn.at(i); }
    size_t words() const { return (size_t)((K + 63) / 64); }
};

void allocate(Spec &sp, const RunRes &R, Alloc &al);

void webreg(Spec &sp, Alloc &al, std::unordered_map<int, int> &wr);

void post_coalesce(Spec &sp, const RunRes &R, Alloc &al,
                   std::unordered_map<int, int> &wr,
                   std::set<int> &removed,
                   std::unordered_map<int, int> &lmparent);

extern bool g_copyprop_nopin;

struct CopyStats {
    int cands = 0, merged = 0, already = 0;
    int rej_pred = 0, rej_constrained = 0, rej_nogpr = 0, rej_interfere = 0,
        rej_clash = 0;
    int pin_kept = 0, reverted = 0;

    int lm_cands = 0, lm_merged = 0, lm_rounds = 0, lm_elided = 0;

    int id_cands = 0, id_merged = 0;
};

extern bool g_idfold;
int idfold_src(const Spec &sp, const RunRes &R, int i);

int copy_coalesce(Spec &sp, Alloc &al, std::unordered_map<int, int> &wr,
                  std::set<int> &removed,
                  std::unordered_map<int, int> &lmparent, CopyStats &cs,
                  int kinds = 1);

}

#endif
