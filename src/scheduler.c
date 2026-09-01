
#include <stdio.h>
#include <stdarg.h>
#include "nv_sched_ctl.h"

int ub_sched_verbose = 0;

static int ub_sched_printf(const char *fmt, ...) {
    va_list ap;
    int r;
    if (!ub_sched_verbose) return 0;
    va_start(ap, fmt);
    r = vprintf(fmt, ap);
    va_end(ap);
    return r;
}

#undef printf
#define printf ub_sched_printf

#include "inkstd_sched.c"

#undef printf


int ub_vote_latency(u64 q) {
    int pd = (int)((q >> 45) & 7);
    return PBL_FMAI + (pd != 7 ? 7 : 0);
}
int uber_vote_floor_fail = 0;

static u32 ubv_floor(u32 c, int want) {
    int code = (int)(c & 0x1F);
    if (SCHED_WAIT_DEC[code] >= want) return c;
    if (code == 0 || code >= 28) { uber_vote_floor_fail = 1; return c; }
    if (want > 15) want = 15;
    return (u32)((c & ~0x1Fu) | (u32)(want & 0xF));
}

int uber_phase_b(unsigned char *bc, unsigned int constOff)
{
    int n, idx;
    unsigned int off;
    u32 *rebuilt;
    rebuilt = pb_schedule_program(bc, constOff, &n);
    if (!rebuilt) return -1;
    uber_vote_floor_fail = 0;
    idx = 0;
    for (off = INSTR_START; off + 32 <= constOff; off += 32) {
        int s;
        for (s = 0; s < 3; s++, idx++) {
            u64 q;
            u32 ioff = off + 8 + (u32)s * 8;
            if (ioff + 8 > constOff || idx >= n) break;
            memcpy(&q, bc + ioff, 8);
            if (q && op_of(q) == OP_Vote)
                rebuilt[idx] = ubv_floor(rebuilt[idx], ub_vote_latency(q));
        }
    }
    idx = 0;
    for (off = INSTR_START; off + 32 <= constOff; off += 32) {
        u64 w = 0;
        int s;
        for (s = 0; s < 3; s++, idx++) {
            u32 c = (idx < n) ? rebuilt[idx] : 0u;
            w |= ((u64)(c & SCHED_CTL_MASK)) << (SCHED_CTL_BITS * s);
        }
        memcpy(bc + off, &w, 8);
    }
    free(rebuilt);
    return n;
}

int uber_validate(unsigned char *bc, unsigned int constOff)
{
    return pb_validate_stream(bc, constOff, 0, 0, 0x7FFFFFFF, "validate");
}

void uber_set_pa_anti(int v) { _pa_anti = v; }

#define UBM_NONE   0
#define UBM_LOCAL  1
#define UBM_ATTR   2
#define UBM_SHARED 3
#define UBM_GLOBAL 4
#define UBM_ALL    9

typedef struct {
    int  cls;
    int  isw;
    int  ra;
    long off;
    int  size;
    int  refine;
} UbMemRef;

static int ubm_ldst_bytes(int t) {
    switch (t) {
    case 0: case 1: return 1;
    case 2: case 3: return 2;
    case 4: return 4;
    case 5: return 8;
    case 6: return 16;
    default: return -1;
    }
}

static void ubm_ref(const PBInst *ip, UbMemRef *o) {
    u64 q = ip->q;
    o->cls = UBM_NONE; o->isw = 0; o->ra = -1; o->off = 0; o->size = 0;
    o->refine = 0;
    switch (ip->op) {
    case OP_Ldl: case OP_Stl: {

        long off = (long)((q >> 20) & 0xFFFFFF);
        int sz = ubm_ldst_bytes((int)((q >> 48) & 7));
        if (off & 0x800000) off -= 0x1000000;
        o->cls = UBM_LOCAL;
        o->isw = (ip->op == OP_Stl);
        o->ra = (int)((q >> 8) & 0xFF);
        o->off = off;
        o->size = sz;
        o->refine = (sz > 0 && off >= 0);
        break;
    }
    case OP_Ald: case OP_Ast: {

        int ncomp = (int)((q >> 47) & 3);
        int rb = (int)((q >> 39) & 0xFF);
        o->cls = UBM_ATTR;
        o->isw = (ip->op == OP_Ast);
        o->ra = (int)((q >> 8) & 0xFF);
        o->off = (long)((q >> 20) & 0x7FF);
        o->size = 4 * (ncomp + 1);
        o->refine = (rb == 255);
        break;
    }
    case OP_Lds: case OP_Sts:
        o->cls = UBM_SHARED; o->isw = (ip->op == OP_Sts); break;
    case OP_Ld: case OP_St: case OP_Ldg: case OP_Stg:
        o->cls = UBM_GLOBAL;
        o->isw = (ip->op == OP_St || ip->op == OP_Stg);
        break;

    case OP_Atom: case OP_Atoms: case OP_AtomCas: case OP_AtomsCas:
    case OP_Red: case OP_Membar: case OP_Bar: case OP_Depbar:
    case OP_Cctl: case OP_Cctll: case OP_Cctlt:
    case OP_Suld: case OP_SuldB: case OP_SuldD: case OP_SuldDB:
    case OP_Sust: case OP_SustB: case OP_SustD: case OP_SustDB:
    case OP_Sured: case OP_SuredB:
    case OP_Suatom: case OP_SuatomB: case OP_SuatomB2:
    case OP_SuatomCas: case OP_SuatomCasB:
    case OP_Out: case OP_Isberd: case OP_Al2p: case OP_Pixld:
        o->cls = UBM_ALL; o->isw = 1; break;
    default: break;
    }
}

static int ubm_alias(const UbMemRef *a, const UbMemRef *b) {
    if (!a->cls || !b->cls) return 0;
    if (!a->isw && !b->isw) return 0;
    if (a->cls == UBM_ALL || b->cls == UBM_ALL) return 1;
    if (a->cls != b->cls) return 0;
    if (!a->refine || !b->refine) return 1;
    if (a->ra != b->ra) return 1;
    if (a->off + a->size <= b->off) return 0;
    if (b->off + b->size <= a->off) return 0;
    return 1;
}

static int ub_add_mem_deps(const PBInst *blk, int m, PBDepList *dep) {
    UbMemRef *r;
    int *idx;
    int nm = 0, added = 0, i, a, b;
    r = (UbMemRef *)malloc(sizeof(UbMemRef) * (size_t)(m > 0 ? m : 1));
    idx = (int *)malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    if (!r || !idx) { free(r); free(idx); return -1; }
    for (i = 0; i < m; i++) {
        ubm_ref(&blk[i], &r[i]);
        if (r[i].cls) idx[nm++] = i;
    }
    for (a = 0; a < nm; a++)
        for (b = a + 1; b < nm; b++)
            if (ubm_alias(&r[idx[a]], &r[idx[b]])) {
                pbd_add(&dep[idx[a]], idx[b], PBD_ANTI);
                added++;
            }
    free(r); free(idx);
    return added;
}

static const int *_ub_wuse = 0, *_ub_wdef = 0;
static int _ub_wstride = 0;
static long long _ub_fe_seen[3], _ub_fe_false[3];

void ub_set_webs(const int *wuse, const int *wdef, int stride) {
    _ub_wuse = wuse; _ub_wdef = wdef; _ub_wstride = stride;
}
void ub_fe_reset(void) {
    int k; for (k = 0; k < 3; k++) { _ub_fe_seen[k] = 0; _ub_fe_false[k] = 0; }
}
void ub_fe_get(long long *seen, long long *fals) {
    int k; for (k = 0; k < 3; k++) { seen[k] = _ub_fe_seen[k]; fals[k] = _ub_fe_false[k]; }
}
int _ub_nofalse = 0;
int _ub_docp = 1;
static long long _ub_cp_all, _ub_cp_nofalse;
void ub_cp_reset(void) { _ub_cp_all = 0; _ub_cp_nofalse = 0; }
void ub_cp_get(long long *all, long long *nofalse) { *all = _ub_cp_all; *nofalse = _ub_cp_nofalse; }

static int ub_edge_false(const PBInst *blk, int base, int from, int to, int type)
{
    short ru[PB_MAX_USES];
    int nru, k, j, njust = 0;
    const int *A, *B;
    if (!_ub_wuse || !_ub_wdef) return 0;
    if (type == PBD_FLOW) return 0;

    if (type == PBD_ANTI) {

        A = _ub_wuse + (size_t)(base + from) * _ub_wstride;
        B = _ub_wdef + (size_t)(base + to)   * _ub_wstride;
        nru = pb_real_uses(&blk[from], ru);
        for (k = 0; k < nru; k++) {
            int r = ru[k];
            if (r < 0 || r >= _ub_wstride) return 0;
            for (j = 0; j < blk[to].n_defs; j++) {
                int d = blk[to].defs[j];
                if (d != r) continue;
                if (A[r] < 0 || B[r] < 0) return 0;
                njust++;
                if (A[r] == B[r]) return 0;
            }
        }
        return njust > 0;
    }
    if (type == PBD_OUTPUT) {
        A = _ub_wdef + (size_t)(base + from) * _ub_wstride;
        B = _ub_wdef + (size_t)(base + to)   * _ub_wstride;
        for (k = 0; k < blk[from].n_defs; k++) {
            int r = blk[from].defs[k];
            if (r < 0 || r >= _ub_wstride) return 0;
            for (j = 0; j < blk[to].n_defs; j++) {
                if (blk[to].defs[j] != r) continue;
                if (A[r] < 0 || B[r] < 0) return 0;
                njust++;
                if (A[r] == B[r]) return 0;
            }
        }
        return njust > 0;
    }
    return 0;
}

static long long ub_crit_path(const PBInst *blk, int m, const PBDepList *dep,
                              int base, int skip_false)
{
    long long best = 0;
    int i, k;
    long long *h = (long long *)malloc(sizeof(long long) * (size_t)(m > 0 ? m : 1));
    if (!h) return 0;
    for (i = m - 1; i >= 0; i--) {
        long long v = 1;
        for (k = 0; k < dep[i].n; k++) {
            int to = dep[i].d[k].to, ty = dep[i].d[k].type;
            long long lat;
            if (to <= i || to >= m) continue;
            if (skip_false && ty <= 2 && ub_edge_false(blk, base, i, to, ty)) continue;
            lat = pb_dep_latency(&blk[i], &blk[to], ty);
            if (lat < 1) lat = 1;
            if (lat + h[to] > v) v = lat + h[to];
        }
        h[i] = v;
        if (v > best) best = v;
    }
    free(h);
    return best;
}

static void ub_false_edges(const PBInst *blk, int m, PBDepList *dep, int base,
                           int drop)
{
    int i, k, w;
    for (i = 0; i < m; i++) {
        w = 0;
        for (k = 0; k < dep[i].n; k++) {
            int ty = dep[i].d[k].type, to = dep[i].d[k].to;
            int bad;
            if (ty > 2) { if (drop) dep[i].d[w++] = dep[i].d[k]; continue; }
            bad = ub_edge_false(blk, base, i, to, ty);
            _ub_fe_seen[ty]++;
            if (bad) _ub_fe_false[ty]++;
            if (drop && !bad) dep[i].d[w++] = dep[i].d[k];
        }
        if (drop) dep[i].n = w;
    }
}

int ub_inst_class(const unsigned char *bc, unsigned int constOff, int nreal,
                  unsigned char *cls, unsigned short *rsb, unsigned short *wsb,
                  int *nslots)
{
    int n = 0, i;
    PBInst *insts = pb_build((const u8 *)bc, constOff, &n);
    if (!insts) return -1;
    *nslots = n;
    for (i = 0; i < n; i++) {
        PBInst *ip = &insts[i];
        unsigned char f = 0;
        if (i >= nreal) { cls[i] = 0; rsb[i] = 0; wsb[i] = 0; continue; }
        if (ip->coupled == PBC_DECOUPLED) f |= 1;
        if (ip->needs_rsb) f |= 2;
        if (ip->needs_wsb) f |= 4;
        if (ip->singleton) f |= 8;
        if (ip->coupled == PBC_REDIRECTED) f |= 16;
        cls[i] = f;
        rsb[i] = (unsigned short)pb_read_sb_latency(ip);
        wsb[i] = (unsigned short)pb_write_sb_latency(ip);
    }
    free(insts);
    return n;
}

int ub_slot_du(const unsigned char *bc, unsigned int constOff,
               unsigned char *out, int stride, int *opout, int maxn)
{
    int n = 0, i, k;
    PBInst *insts;
    insts = pb_build((const u8 *)bc, constOff, &n);
    if (!insts) return -1;
    if (n > maxn) n = maxn;
    for (i = 0; i < n; i++) {
        unsigned char *row = out + (size_t)i * (size_t)stride;
        PBInst *ip = &insts[i];
        memset(row, 0, (size_t)stride);
        if (opout) opout[i] = ip->op;
        for (k = 0; k < ip->n_defs; k++)
            if (ip->defs[k] >= 0 && ip->defs[k] < stride) row[ip->defs[k]] |= 1;
        for (k = 0; k < ip->n_uses; k++)
            if (ip->uses[k] >= 0 && ip->uses[k] < stride) row[ip->uses[k]] |= 2;
        for (k = 0; k < ip->n_suses; k++)
            if (ip->suses[k] >= 0 && ip->suses[k] < stride) row[ip->suses[k]] |= 4;
    }
    free(insts);
    return n;
}

static void ub_fix_extra_du(PBInst *ip) {
    int rd, pd, k, w;
    if (ip->op != OP_Vote) return;
    rd = (int)(ip->q & 0xFF);
    pd = (int)((ip->q >> 45) & 7);

    w = 0;
    for (k = 0; k < ip->n_uses; k++)
        if (!(ip->uses[k] == (short)rd || ip->uses[k] == (short)PB_P(pd)))
            ip->uses[w++] = ip->uses[k];
    ip->n_uses = (u8)w;
    w = 0;
    for (k = 0; k < ip->n_suses; k++)
        if (!(ip->suses[k] == (short)rd || ip->suses[k] == (short)PB_P(pd)))
            ip->suses[w++] = ip->suses[k];
    ip->n_suses = (u8)w;

    if (rd < 255 && ip->n_defs < PB_MAX_DEFS) {
        int have = 0;
        for (k = 0; k < ip->n_defs; k++) if (ip->defs[k] == (short)rd) have = 1;
        if (!have) ip->defs[ip->n_defs++] = (short)rd;
    }
    if (pd != 7 && ip->n_defs < PB_MAX_DEFS) {
        int have = 0;
        for (k = 0; k < ip->n_defs; k++) if (ip->defs[k] == (short)PB_P(pd)) have = 1;
        if (!have) ip->defs[ip->n_defs++] = (short)PB_P(pd);
    }

    ip->defs_ccp = 0;
    for (k = 0; k < ip->n_defs; k++)
        if ((ip->defs[k] >= 300 && ip->defs[k] <= 306) || ip->defs[k] == 320)
            ip->defs_ccp = 1;
    { int bl = pb_base_latency(ip);
      ip->lat_full = (unsigned short)(bl + (ip->defs_ccp ? 7 : 0)); }
}

static void ub_union_pred(PBInst *ip, unsigned char pdefs, unsigned char puses) {
    int p, k, have;
    for (p = 0; p < 7; p++) {
        if (!((pdefs >> p) & 1)) continue;
        have = 0;
        for (k = 0; k < ip->n_defs; k++) if (ip->defs[k] == PB_P(p)) have = 1;
        if (!have && ip->n_defs < PB_MAX_DEFS) ip->defs[ip->n_defs++] = (short)PB_P(p);
    }
    for (p = 0; p < 7; p++) {
        if (!((puses >> p) & 1)) continue;
        have = 0;
        for (k = 0; k < ip->n_suses; k++) if (ip->suses[k] == PB_P(p)) have = 1;
        if (!have && ip->n_suses < PB_MAX_USES) ip->suses[ip->n_suses++] = (short)PB_P(p);
        have = 0;
        for (k = 0; k < ip->n_uses; k++) if (ip->uses[k] == PB_P(p)) have = 1;
        if (!have && ip->n_uses < PB_MAX_USES) ip->uses[ip->n_uses++] = (short)PB_P(p);
    }
    ip->defs_ccp = 0;
    for (k = 0; k < ip->n_defs; k++)
        if ((ip->defs[k] >= 300 && ip->defs[k] <= 306) || ip->defs[k] == 320)
            ip->defs_ccp = 1;
    { int bl = pb_base_latency(ip);
      ip->lat_full = (unsigned short)(bl + (ip->defs_ccp ? 7 : 0)); }
}

int ubf_pick_last = 0;
static int ubf_is_fc(int op) {
    return pb_is_bb_ender(op) || pb_is_branch_addr_op(op) ||
           op == OP_Ssy || op == OP_Pbk || op == OP_Pcnt || op == OP_Kil ||
           op == OP_Sync || op == OP_Brk || op == OP_Cont || op == OP_Exit;
}

int uber_fill_bubbles(const unsigned char *bc, unsigned int constOff, int nreal,
                      int *perm, unsigned char *leader, int *nslots, int memdeps,
                      const unsigned char *pdefs, const unsigned char *puses)
{
    int n = 0, nbb = 0, bi, i, k, moved = 0;
    PBInst *insts;
    PBBlock *bbs;
    int *wait;

    insts = pb_build((const u8 *)bc, constOff, &n);
    if (!insts) return -1;
    bbs = pb_basic_blocks(insts, n, &nbb);
    if (!bbs) { free(insts); return -1; }
    *nslots = n;
    for (i = 0; i < n; i++) { perm[i] = i; leader[i] = 0; }
    for (bi = 0; bi < nbb; bi++)
        if (bbs[bi].start >= 0 && bbs[bi].start < n) leader[bbs[bi].start] = 1;

    wait = (int *)calloc((size_t)(n > 0 ? n : 1), sizeof(int));
    if (!wait) { free(bbs); free(insts); return -1; }
    { int idx = 0; unsigned int off;
      for (off = INSTR_START; off + 32 <= constOff; off += 32) {
          u64 w; int s; memcpy(&w, bc + off, 8);
          for (s = 0; s < 3; s++, idx++)
              if (idx < n)
                  wait[idx] = insts[idx].q ? SCHED_WAIT_DEC[sched_wait_code(w, s)] : 0;
      } }

    for (bi = 0; bi < nbb; bi++) {
        int s = bbs[bi].start, e = bbs[bi].end, m = e - s, t, fc_stop;
        PBInst *blk; PBDepList *dep; int *cyc; int *ord; unsigned char *isfc;
        if (m <= 2) continue;
        if (s + m > nreal) continue;
        blk = (PBInst *)malloc(sizeof(PBInst) * (size_t)m);
        dep = (PBDepList *)malloc(sizeof(PBDepList) * (size_t)m);
        cyc = (int *)calloc((size_t)m, sizeof(int));
        ord = (int *)malloc(sizeof(int) * (size_t)m);
        isfc = (unsigned char *)calloc((size_t)m, 1);
        if (!blk || !dep || !cyc || !ord || !isfc) {
            free(blk); free(dep); free(cyc); free(ord); free(isfc);
            free(wait); free(bbs); free(insts); return -1;
        }
        for (i = 0; i < m; i++) {
            blk[i] = insts[s + i];
            ub_fix_extra_du(&blk[i]);
            if (pdefs || puses)
                ub_union_pred(&blk[i], pdefs ? pdefs[s + i] : 0,
                              puses ? puses[s + i] : 0);
            isfc[i] = (unsigned char)(blk[i].q ? ubf_is_fc(blk[i].op) : 1);
            ord[i] = i;
        }
        { int sv = _pb_tav_mode;
          if (_pa_suses) _pb_tav_mode |= 64;
          _pb_drop_guard = _pa_noguard;
          _pb_anti_pclass = _pa_antip;
          pb_calc_deps(blk, m, dep);
          _pb_anti_pclass = 0;
          _pb_drop_guard = 0;
          _pb_tav_mode = sv;
          if (_pa_syncpush) pa_add_sync_push_deps(blk, m, dep);
          if (memdeps && ub_add_mem_deps(blk, m, dep) < 0) {
              free(blk); free(dep); free(cyc); free(ord); free(isfc);
              free(wait); free(bbs); free(insts); return -1;
          } }
        for (i = 1; i < m; i++) cyc[i] = cyc[i - 1] + wait[s + i - 1];

        {
        int *in_cnt, *in_off, *in_src; signed char *in_ty; int tot = 0, e2;
        int *pos;
        in_cnt = (int *)calloc((size_t)m, sizeof(int));
        pos = (int *)malloc(sizeof(int) * (size_t)m);
        if (!in_cnt || !pos) {
            free(in_cnt); free(pos);
            for (i = 0; i < m; i++) pbd_free(&dep[i]);
            free(blk); free(dep); free(cyc); free(ord); free(isfc);
            free(wait); free(bbs); free(insts); return -1;
        }
        for (i = 0; i < m; i++)
            for (k = 0; k < dep[i].n; k++) {
                int to = dep[i].d[k].to;
                if (to >= 0 && to < m) { in_cnt[to]++; tot++; }
            }
        in_off = (int *)malloc(sizeof(int) * (size_t)(m + 1));
        in_src = (int *)malloc(sizeof(int) * (size_t)(tot > 0 ? tot : 1));
        in_ty = (signed char *)malloc((size_t)(tot > 0 ? tot : 1));
        if (!in_off || !in_src || !in_ty) {
            free(in_cnt); free(in_off); free(in_src); free(in_ty); free(pos);
            for (i = 0; i < m; i++) pbd_free(&dep[i]);
            free(blk); free(dep); free(cyc); free(ord); free(isfc);
            free(wait); free(bbs); free(insts); return -1;
        }
        in_off[0] = 0;
        for (i = 0; i < m; i++) in_off[i + 1] = in_off[i] + in_cnt[i];
        for (i = 0; i < m; i++) in_cnt[i] = in_off[i];
        for (i = 0; i < m; i++)
            for (k = 0; k < dep[i].n; k++) {
                int to = dep[i].d[k].to;
                if (to >= 0 && to < m) {
                    in_src[in_cnt[to]] = i;
                    in_ty[in_cnt[to]] = (signed char)dep[i].d[k].type;
                    in_cnt[to]++;
                }
            }
        for (i = 0; i < m; i++) pos[ord[i]] = i;

        fc_stop = 0;
        for (t = 1; t < m; t++) {
            int stall, j, pick = -1;
            if (isfc[ord[t]]) continue;

            for (fc_stop = t + 1; fc_stop < m; fc_stop++)
                if (isfc[ord[fc_stop]]) break;
            stall = cyc[t] - cyc[t - 1];
            if (stall <= 1) continue;
            for (j = t + 1; j < fc_stop; j++) {
                int ok = 1, cand = ord[j];
                if (!blk[cand].q) continue;
                for (e2 = in_off[cand]; e2 < in_off[cand + 1] && ok; e2++) {
                    int u = in_src[e2], p, lat;
                    if (!blk[u].q) continue;
                    p = pos[u];
                    if (p >= j) continue;
                    if (p >= t) { ok = 0; break; }
                    lat = pb_dep_latency(&blk[u], &blk[cand], (int)in_ty[e2]);
                    if (cyc[p] + lat > cyc[t - 1] + 1) { ok = 0; break; }
                }
                if (ok) { pick = j; if (!ubf_pick_last) break; }
            }
            if (pick < 0) continue;
            { int v = ord[pick];
              for (j = pick; j > t; j--) ord[j] = ord[j - 1];
              ord[t] = v;
              for (j = t; j <= pick; j++) pos[ord[j]] = j; }
            moved++;

            for (j = pick; j > t; j--) cyc[j] = cyc[j - 1];
            cyc[t] = cyc[t - 1] + 1;
        }
        free(in_cnt); free(in_off); free(in_src); free(in_ty); free(pos);
        }
        for (i = 0; i < m; i++) perm[s + i] = s + ord[i];
        for (i = 0; i < m; i++) pbd_free(&dep[i]);
        free(blk); free(dep); free(cyc); free(ord); free(isfc);
    }
    free(wait); free(bbs); free(insts);
    return moved;
}

int ubh_class = 1;
int ubh_thresh = 6;

int ubh_cap = 0;
int ubh_latency = 0;

static int ubh_wanted(const PBInst *ip) {
    int op = ip->op;
    if ((ubh_class & 1) && (op == OP_Ipa)) return 1;
    if ((ubh_class & 2) && (op == OP_Mufu || op == OP_Rro)) return 1;
    if ((ubh_class & 4) && ip->is_longlat) return 1;
    return 0;
}

int uber_hoist_ll(const unsigned char *bc, unsigned int constOff, int nreal,
                  int *perm, unsigned char *leader, int *nslots, int memdeps,
                  const unsigned char *pdefs, const unsigned char *puses)
{
    int n = 0, nbb = 0, bi, i, k, moved = 0;
    PBInst *insts;
    PBBlock *bbs;
    int *wait;

    insts = pb_build((const u8 *)bc, constOff, &n);
    if (!insts) return -1;
    bbs = pb_basic_blocks(insts, n, &nbb);
    if (!bbs) { free(insts); return -1; }
    *nslots = n;
    for (i = 0; i < n; i++) { perm[i] = i; leader[i] = 0; }
    for (bi = 0; bi < nbb; bi++)
        if (bbs[bi].start >= 0 && bbs[bi].start < n) leader[bbs[bi].start] = 1;

    wait = (int *)calloc((size_t)(n > 0 ? n : 1), sizeof(int));
    if (!wait) { free(bbs); free(insts); return -1; }
    { int idx = 0; unsigned int off;
      for (off = INSTR_START; off + 32 <= constOff; off += 32) {
          u64 w; int s; memcpy(&w, bc + off, 8);
          for (s = 0; s < 3; s++, idx++)
              if (idx < n)
                  wait[idx] = insts[idx].q ? SCHED_WAIT_DEC[sched_wait_code(w, s)] : 0;
      } }

    for (bi = 0; bi < nbb; bi++) {
        int s = bbs[bi].start, e = bbs[bi].end, m = e - s, j;
        PBInst *blk; PBDepList *dep; int *ord; unsigned char *isfc; int *cyc;
        if (m <= 2) continue;
        if (s + m > nreal) continue;
        blk = (PBInst *)malloc(sizeof(PBInst) * (size_t)m);
        dep = (PBDepList *)malloc(sizeof(PBDepList) * (size_t)m);
        ord = (int *)malloc(sizeof(int) * (size_t)m);
        cyc = (int *)calloc((size_t)m, sizeof(int));
        isfc = (unsigned char *)calloc((size_t)m, 1);
        if (!blk || !dep || !ord || !isfc || !cyc) {
            free(blk); free(dep); free(ord); free(isfc); free(cyc);
            free(wait); free(bbs); free(insts); return -1;
        }
        for (i = 0; i < m; i++) {
            blk[i] = insts[s + i];
            ub_fix_extra_du(&blk[i]);
            if (pdefs || puses)
                ub_union_pred(&blk[i], pdefs ? pdefs[s + i] : 0,
                              puses ? puses[s + i] : 0);
            isfc[i] = (unsigned char)(blk[i].q ? ubf_is_fc(blk[i].op) : 1);
            ord[i] = i;
        }
        { int sv = _pb_tav_mode;
          if (_pa_suses) _pb_tav_mode |= 64;
          _pb_drop_guard = _pa_noguard;
          _pb_anti_pclass = _pa_antip;
          pb_calc_deps(blk, m, dep);
          _pb_anti_pclass = 0;
          _pb_drop_guard = 0;
          _pb_tav_mode = sv;
          if (_pa_syncpush) pa_add_sync_push_deps(blk, m, dep);
          if (memdeps && ub_add_mem_deps(blk, m, dep) < 0) {
              free(blk); free(dep); free(ord); free(isfc); free(cyc);
              free(wait); free(bbs); free(insts); return -1;
          } }
        for (i = 1; i < m; i++) cyc[i] = cyc[i - 1] + wait[s + i - 1];

        for (j = 1; j < m; j++) {
            int v = ord[j], t, lo, best = j, stall, feeds, dist;
            if (!blk[v].q || isfc[v]) continue;
            if (!ubh_wanted(&blk[v])) continue;

            stall = wait[s + v];
            if (stall < ubh_thresh) continue;
            if (j + 1 >= m) continue;
            feeds = 0;
            for (k = 0; k < dep[v].n; k++)
                if (dep[v].d[k].to == ord[j + 1] &&
                    dep[v].d[k].type == PBD_FLOW) { feeds = 1; break; }
            if (!feeds) continue;

            for (lo = j - 1; lo >= 0; lo--) if (isfc[ord[lo]]) break;
            lo++;

            dist = ubh_cap > 0 ? ubh_cap : stall;
            if (j - dist > lo) lo = j - dist;

            for (t = j - 1; t >= lo; t--) {
                int pi = ord[t], blocked = 0, p;
                if (blk[pi].q)
                    for (k = 0; k < dep[pi].n; k++)
                        if (dep[pi].d[k].to == v) { blocked = 1; break; }
                if (blocked) break;
                if (ubh_latency) {
                    for (p = 0; p < t && !blocked; p++) {
                        int qi = ord[p];
                        if (!blk[qi].q) continue;
                        for (k = 0; k < dep[qi].n; k++) {
                            int lat;
                            if (dep[qi].d[k].to != v) continue;
                            lat = pb_dep_latency(&blk[qi], &blk[v],
                                                 dep[qi].d[k].type);
                            if (cyc[p] + lat > cyc[t]) { blocked = 1; break; }
                        }
                    }
                    if (blocked) break;
                }
                best = t;
            }
            if (best == j) continue;
            for (t = j; t > best; t--) ord[t] = ord[t - 1];
            ord[best] = v;
            for (t = j; t > best; t--) cyc[t] = cyc[t - 1];
            cyc[best] = best ? cyc[best - 1] + 1 : 0;
            moved++;
        }
        for (i = 0; i < m; i++) perm[s + i] = s + ord[i];
        for (i = 0; i < m; i++) pbd_free(&dep[i]);
        free(blk); free(dep); free(ord); free(isfc); free(cyc);
    }
    free(wait); free(bbs); free(insts);
    return moved;
}

int uber_phase_a(const unsigned char *bc, unsigned int constOff, int nreal,
                 int *perm, unsigned char *leader, int *nslots, int memdeps,
                 const unsigned char *pdefs, const unsigned char *puses)
{
    int n = 0, nbb = 0, bi, i, moved = 0, maxn = 0;
    PBInst *insts;
    PBBlock *bbs;
    PAArena ar;

    insts = pb_build((const u8 *)bc, constOff, &n);
    if (!insts) return -1;
    bbs = pb_basic_blocks(insts, n, &nbb);
    if (!bbs) { free(insts); return -1; }
    *nslots = n;
    for (i = 0; i < n; i++) { perm[i] = i; leader[i] = 0; }
    for (bi = 0; bi < nbb; bi++) {
        int m = bbs[bi].end - bbs[bi].start;
        if (m > maxn) maxn = m;
        if (bbs[bi].start >= 0 && bbs[bi].start < n) leader[bbs[bi].start] = 1;
    }
    if (!pa_arena_init(&ar, (size_t)(maxn + 8) *
            (sizeof(PBInst) + sizeof(PBDepList) + sizeof(PASI) + 4 * sizeof(int))
            + 8192)) {
        free(bbs); free(insts); return -1;
    }

    for (bi = 0; bi < nbb; bi++) {
        int s = bbs[bi].start, e = bbs[bi].end, m = e - s;
        PBInst *blk; PBDepList *dep; PASI *si; int *out;
        PAB B; int nout, ok;
        if (m <= 0) continue;
        if (s + m > nreal) continue;
        pa_arena_reset(&ar);
        blk = (PBInst *)pa_alloc(&ar, sizeof(PBInst) * (size_t)m);
        dep = (PBDepList *)pa_alloc(&ar, sizeof(PBDepList) * (size_t)m);
        si  = (PASI *)pa_calloc(&ar, sizeof(PASI) * (size_t)m);
        out = (int *)pa_alloc(&ar, sizeof(int) * (size_t)m);
        if (!blk || !dep || !si || !out) {
            pa_arena_free(&ar); free(bbs); free(insts); return -1;
        }
        for (i = 0; i < m; i++) {
            blk[i] = insts[s + i];
            ub_fix_extra_du(&blk[i]);
            if (pdefs || puses)
                ub_union_pred(&blk[i], pdefs ? pdefs[s + i] : 0,
                              puses ? puses[s + i] : 0);
            si[i].isTex = (u8)pb_is_tex_batch_op(blk[i].op);
            si[i].resToUse = -1;
            si[i].anext = si[i].aprev = -1;
        }
        { int sv = _pb_tav_mode;
          if (_pa_suses) _pb_tav_mode |= 64;
          _pb_drop_guard = _pa_noguard;
          _pb_anti_pclass = _pa_antip;
          pb_calc_deps(blk, m, dep);
          _pb_anti_pclass = 0;
          _pb_drop_guard = 0;
          _pb_tav_mode = sv;
          if (_pa_syncpush) pa_add_sync_push_deps(blk, m, dep);
          if (memdeps && ub_add_mem_deps(blk, m, dep) < 0) {
              pa_arena_free(&ar); free(bbs); free(insts); return -1;
          } }
        if (_ub_wuse) {
            if (_ub_docp) {
                _ub_cp_all     += ub_crit_path(blk, m, dep, s, 0);
                _ub_cp_nofalse += ub_crit_path(blk, m, dep, s, 1);
            }
            ub_false_edges(blk, m, dep, s, _ub_nofalse);
        }
        if (!_pa_ccp)
            for (i = 0; i < m; i++)
                blk[i].lat_full = (unsigned short)pb_base_latency(&blk[i]);
        memset(&B, 0, sizeof(B));
        B.blk = blk; B.dep = dep; B.si = si; B.n = m;
        B.ipInBundle = -1; B.ipPriorTex = -1; B.ipPriorAvail = -1;
        B.ipLastSched = -1;
        B.lastTexSchedTime = -9999;
        for (i = 0; i < m; i++) if (si[i].isTex) B.numTexRemaining++;
        nout = pa_schedule_block(&B, out);
        ok = (nout == m);
        if (ok) {
            int *seen = (int *)pa_calloc(&ar, sizeof(int) * (size_t)m);
            if (!seen) ok = 0;
            for (i = 0; ok && i < m; i++) {
                if (out[i] < 0 || out[i] >= m || seen[out[i]]) ok = 0;
                else seen[out[i]] = 1;
            }
        }
        if (ok)
            for (i = 0; i < m; i++) {
                perm[s + i] = s + out[i];
                if (out[i] != i) moved++;
            }
        for (i = 0; i < m; i++) pbd_free(&dep[i]);
    }
    pa_arena_free(&ar);
    free(bbs); free(insts);
    return moved;
}

#define UBT_MB(n) ((u64)1 << ((n) - 39))

#define UBT_ADD 1
#define UBT_MUL 2
#define UBT_FMA 3




#define UBT_NOUT 40

