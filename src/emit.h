
#ifndef UBERSPEC_EMIT_H
#define UBERSPEC_EMIT_H

#include "alloc.h"

namespace ub {

struct EmitStats {
    std::string name;
    std::vector<u8> bc, ct;
    int n_emit = 0;
};

extern bool g_copyprop;

extern bool g_lmem_compact;
extern bool g_lmem_promote;

extern bool g_lmem_copyprop;

template <class I = Sm50>
void words_used_regs(const std::vector<typename I::Word> &words, std::set<int> &out);

u64 renumber_mask(u64 q);

template <class I>
void emit(ProgramT<I> &uber, SpecT<I> &sp, const std::vector<u32> &c6,
          const std::string &name, EmitStats &out);

struct RegStats {
    int new_decl = 0;

    int floored = 0;

    int rp_tuple = 0;
};

int occupancy_of(int regs);

inline bool slots_ok(int n) { return n % 24 == 12; }

template <class I = Sm50>
void renumber(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
              bool bank_aware, RegStats &st, int need_warps = 0);

template <class I = Sm50>
void renumber_cache_clear();
void fill_cache_clear();

extern bool g_bank;

void exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out);

bool bytecode_is_fragment(const std::vector<u8> &bc, const char *what);

struct CtlFacts {
    bool fragment = false;
    int n_real = 0, gpr_count = 0;

    long long rate_weight = 0;
    int ipa_redundant = 0;
    int slm_low = 0, slm_high = 0, slm_crs = 0;
    u32 lmem_bytes = 0;
    int does_load_or_store = 0, does_global_store = 0, does_fp64 = 0;
    int kills_pixels = 0, ncolor_outputs = 0;

    u8 imap_gen_read[32] = {};
    u32 imap_sys_read = 0;
    bool imap_indexed = false;
    std::vector<int> tex_slots;
    int tex_bindless = 0;
};
void control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f);

void control_facts(const std::vector<u8> &bc, const std::vector<u8> &ct,
                   CtlFacts &f);

void phase_b(std::vector<u8> &bc, u32 co);

void reorder(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps);

void fill_bubbles(std::vector<u8> &bc, std::vector<u8> &ct, bool memdeps, int rounds);
int issue_cycles(const std::vector<u8> &bc, u32 co);

template <class I = Sm50>
void dce2(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment);

struct AnticopyStats {
    int applied = 0;
};

struct VnStats {
    int rounds = 0;
};
extern bool g_vn;
template <class I = Sm50>
void entry_live(const std::vector<u8> &bc, const std::vector<u8> &ct,
                std::vector<int> &out);
template <class I = Sm50>
void vn_cse(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
            VnStats &st, int reach);

struct SinkStats {
    int moved = 0;
    int maxlive0 = -1;
};
extern int g_sink_back, g_sink_rounds, g_sink_ext, g_remat_max, g_spill_max,
           g_spill_warps;
template <class I = Sm50>
void sink_cheap(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
                SinkStats &st);
extern bool g_anticopy;
extern long long g_ac_budget;

template <class I = Sm50>
void anticopy(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
              AnticopyStats &st);

void pred_masks(const Program &p, int n, std::vector<u8> &pdefs,
                std::vector<u8> &puses);

struct TexNarrowStats {
    int narrowed = 0;
};
extern bool g_texnarrow;
template <class I = Sm50>
void texnarrow(std::vector<u8> &bc, const std::vector<u8> &ct, bool fragment,
               TexNarrowStats &st);
bool gate_memorder(const std::vector<u8> &pre_bc, const std::vector<u8> &pre_ct,
                   const std::vector<u8> &post_bc, const std::vector<u8> &post_ct,
                   std::string &detail);

static const int WEB_STRIDE = 256;

template <class I = Sm50>
bool web_map(const std::vector<u8> &bc, const std::vector<u8> &ct, bool fragment,
             std::vector<int> &wuse, std::vector<int> &wdef, int &nslots);

struct GateResult {
    std::vector<std::tuple<std::string, bool, std::string>> rows;
    void add(const std::string &g, bool ok, const std::string &d) {
        rows.emplace_back(g, ok, d);
    }
    int nbad() const {
        int n = 0;
        for (auto &r : rows) if (!std::get<1>(r)) n++;
        return n;
    }
};
void verify(const std::vector<u8> &bc, const std::vector<u8> &ct,
            bool run_v8, GateResult &R,
            const std::vector<u8> *shipped_bc = nullptr,
            const std::vector<u8> *shipped_ct = nullptr,
            const std::vector<u8> *ref_bc = nullptr,
            const std::vector<u8> *ref_ct = nullptr);

void tex_samplers(const std::vector<u8> &bc, const std::vector<u8> &ct,
                  std::vector<int> &out);

}

#endif
