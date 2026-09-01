
#ifndef UBERSPEC_EMIT_H
#define UBERSPEC_EMIT_H

#include "alloc.h"

namespace ub {

struct EmitStats {
    std::string name;
    std::vector<u8> bc, ct;
    int padded = 0, words = 0, n_kept = 0, n_emit = 0, n_coalesced = 0;
    int opt_relocated = 0, n_remat = 0, p5_after = 0;

    int lm_ops = 0, lm_promoted = 0, lm_movs = 0, lm_slots = 0,
        lm_frame_dw = 0, lm_compacted = 0;
    CopyStats cp;
    u32 co = 0;
    size_t size = 0;
};

extern bool g_copyprop;

extern bool g_lmem_compact;
extern bool g_lmem_promote;

extern bool g_lmem_copyprop;

void words_used_regs(const std::vector<u64> &words, std::set<int> &out);

u64 renumber_mask(u64 q);

void emit(Program &uber, Spec &sp, const std::vector<u32> &c6,
          const std::string &name, EmitStats &out);

struct RegStats {
    int old_max = -1, new_max = -1, old_decl = 0, new_decl = 0;
    int maxlive = 0, nregs = 0, nruns = 0, bank_pass = 0, nconstrained = 0;

    int rp_offered = 0, rp_used = 0, rp_webs = 0;
};

int occupancy_of(int regs);

inline bool slots_ok(int n) { return n % 24 == 12; }
void renumber(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
              bool bank_aware, RegStats &st);

void renumber_cache_clear();
void fill_cache_clear();

extern bool g_rp_colour;
extern bool g_rp_align;

extern bool g_rp_split;

extern bool g_rp_defrelax;

extern bool g_rp_force;
extern int g_rp_offered_n, g_rp_kept_n, g_rp_occ_n;

extern bool g_bank, g_bank_force;
extern long long g_bank_rows, g_bank_kept, g_bank_before, g_bank_after;

void exit_live_regs(const std::vector<u8> &bc, std::vector<int> &out);

bool bytecode_is_fragment(const std::vector<u8> &bc, const char *what);

struct CtlFacts {
    bool fragment = false;
    int n_real = 0, max_gpr = -1, gpr_count = 0;
    int slm_low = 0, slm_high = 0, slm_crs = 0;
    u32 lmem_bytes = 0;
    int does_load_or_store = 0, does_global_store = 0, does_fp64 = 0;
    int kills_pixels = 0, ncolor_outputs = 0;
    std::vector<int> tex_slots;
    int tex_bindless = 0, back_edges = 0, max_stack_depth = 0;
};
void control_rewrite(std::vector<u8> &bc, std::vector<u8> &ct, CtlFacts &f);

void control_facts(const std::vector<u8> &bc, const std::vector<u8> &ct,
                   CtlFacts &f);

struct PressFacts {
    int maxlive = 0, over48 = 0, over56 = 0, npts = 0;

    int nnames = 0, nwebs = 0;
};
void pressure_facts(const std::vector<u8> &bc, const std::vector<u8> &ct,
                    PressFacts &f);

void phase_b(std::vector<u8> &bc, u32 co);

struct ReorderStats {
    int moved = 0, slots = 0, memops = 0, v11_violations = 0;
    int fill_moved = 0, fill_rounds = 0, fill_before = 0, fill_after = 0;
    int fill_reverted = 0;
    int hoist_moved = 0, hoist_reverted = 0;
};
extern bool g_reorder_report_only;
void reorder(std::vector<u8> &bc, std::vector<u8> &ct, ReorderStats &st,
             bool memdeps);
void fill_bubbles(std::vector<u8> &bc, std::vector<u8> &ct, ReorderStats &st,
                  bool memdeps, int rounds);
int issue_cycles(const std::vector<u8> &bc, u32 co);

struct Dce2Stats {
    int dead = 0, self = 0, rounds = 0, reverted = 0, cc_declined = 0;
    int trimmed = 0, deleted = 0;
    int cycles_saved = 0;
};
extern bool g_dce2, g_dce2_force, g_dce2_early;
extern long long g_dce2_dead, g_dce2_self, g_dce2_calls, g_dce2_rev;

extern long long g_dce2_notrunc, g_dce2_badtrunc;
void dce2(std::vector<u8> &bc, std::vector<u8> &ct, bool fragment,
          Dce2Stats &st, bool guard = true);

struct TexNarrowStats {
    int sites = 0;
    int narrowed = 0;
    int comps = 0;
    int declined = 0;
    int allDead = 0;
    int unmodelled = 0;

    int selfcopies = 0;
    int deadops = 0;
    int nopped = 0;

    int ghostRejected = 0;
};
extern bool g_texnarrow;
extern long long g_texnarrow_sites, g_texnarrow_progs, g_texnarrow_calls;
void texnarrow(std::vector<u8> &bc, const std::vector<u8> &ct, bool fragment,
               TexNarrowStats &st);
bool gate_memorder(const std::vector<u8> &pre_bc, const std::vector<u8> &pre_ct,
                   const std::vector<u8> &post_bc, const std::vector<u8> &post_ct,
                   std::string &detail);

static const int WEB_STRIDE = 256;

struct FEStats {
    long long seen[3] = {0, 0, 0}, fals[3] = {0, 0, 0};
    long long cp_all = 0, cp_nofalse = 0;
    void clear() { *this = FEStats(); }
};
extern FEStats g_fe;
extern bool g_presched_probe, g_presched_drop, g_stage_fragment;
extern bool g_fe_locked;

extern bool g_anti, g_anti_force;

extern bool g_exitfold;
extern long long g_exitfold_hit, g_exitfold_miss;
extern bool g_grow;
extern bool g_grow_bank;
extern int  g_grow_k;
extern long long g_grow_room, g_grow_calls;
extern long long g_anti_rows, g_anti_kept, g_anti_before, g_anti_after;
extern long long g_anti_cyc_saved, g_anti_calls;
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
