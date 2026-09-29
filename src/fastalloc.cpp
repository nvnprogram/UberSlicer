
#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <new>

namespace {

const size_t kAlign   = 16;
const size_t kMaxCls  = 256;
const size_t kBigCls  = 24;
const size_t kChunk   = 1u << 21;

void *g_free[kMaxCls + kBigCls + 1];
char *g_bump;
size_t g_left;

inline void *fa_alloc(size_t n) {
    size_t need = n + kAlign;
    size_t cls  = (need + kAlign - 1) / kAlign;
    if (cls <= kMaxCls) {
        void *p = g_free[cls];
        if (p) {
            g_free[cls] = *(void **)p;
            *(size_t *)p = cls;
            ((size_t *)p)[1] = n;
            return (char *)p + kAlign;
        }
        size_t sz = cls * kAlign;
        if (g_left < sz) {
            char *c = (char *)std::malloc(kChunk);
            if (!c) return nullptr;
            g_bump = c;
            g_left = kChunk;
        }
        char *q = g_bump;
        g_bump += sz;
        g_left -= sz;
        *(size_t *)q = cls;
        ((size_t *)q)[1] = n;
        return q + kAlign;
    }

    int e = 13;
    while (((size_t)1 << e) < need && e < 36) e++;
    if (e < 36) {
        size_t bc = kMaxCls + (size_t)(e - 12);
        void *p = g_free[bc];
        if (p) {
            g_free[bc] = *(void **)p;
            *(size_t *)p = bc;
            ((size_t *)p)[1] = n;
            return (char *)p + kAlign;
        }
        char *q = (char *)std::malloc((size_t)1 << e);
        if (!q) return nullptr;
        *(size_t *)q = bc;
        ((size_t *)q)[1] = n;
        return q + kAlign;
    }
    char *q = (char *)std::malloc(need);
    if (!q) return nullptr;
    *(size_t *)q = 0;
    ((size_t *)q)[1] = n;
    return q + kAlign;
}

inline void fa_free(void *v) {
    if (!v) return;
    char *p = (char *)v - kAlign;
    size_t cls = *(size_t *)p;
    if (cls) {
        *(void **)p = g_free[cls];
        g_free[cls] = p;
    } else {
        std::free(p);
    }
}

inline void *fa_new(size_t n) {
    for (;;) {
        void *p = fa_alloc(n ? n : 1);
        if (p) return p;
        std::new_handler h = std::get_new_handler();
        if (!h) throw std::bad_alloc();
        h();
    }
}

}

void *operator new(size_t n) { return fa_new(n); }
void *operator new[](size_t n) { return fa_new(n); }
void *operator new(size_t n, const std::nothrow_t &) noexcept { return fa_alloc(n ? n : 1); }
void *operator new[](size_t n, const std::nothrow_t &) noexcept { return fa_alloc(n ? n : 1); }
void operator delete(void *p) noexcept { fa_free(p); }
void operator delete[](void *p) noexcept { fa_free(p); }
void operator delete(void *p, size_t) noexcept { fa_free(p); }
void operator delete[](void *p, size_t) noexcept { fa_free(p); }
void operator delete(void *p, const std::nothrow_t &) noexcept { fa_free(p); }
void operator delete[](void *p, const std::nothrow_t &) noexcept { fa_free(p); }

extern "C" {

void *ub_cmalloc(size_t n) { return fa_alloc(n ? n : 1); }

void *ub_ccalloc(size_t a, size_t b) {
    size_t n = a * b;
    void *p = fa_alloc(n ? n : 1);
    if (p && n) std::memset(p, 0, n);
    return p;
}

void ub_cfree(void *p) { fa_free(p); }

void *ub_crealloc(void *p, size_t n) {
    if (!p) return fa_alloc(n ? n : 1);
    if (!n) { fa_free(p); return nullptr; }
    size_t *h = (size_t *)((char *)p - kAlign);
    size_t cls = h[0], old = h[1];

    if (cls && cls <= kMaxCls && n <= cls * kAlign - kAlign) { h[1] = n; return p; }
    if (cls > kMaxCls && n <= ((size_t)1 << (cls - kMaxCls + 12)) - kAlign) {
        h[1] = n;
        return p;
    }
    void *q = fa_alloc(n);
    if (!q) return nullptr;
    std::memcpy(q, p, old < n ? old : n);
    fa_free(p);
    return q;
}

}
