
#ifndef UB_SM86_SCHED_PHASE_B_H
#define UB_SM86_SCHED_PHASE_B_H

#include <functional>
#include <string>
#include <vector>

#include "deps.h"
#include "sb.h"

namespace ub {
namespace sm86 {
namespace sched {

struct Cfg {
    std::vector<int> starts;
    std::vector<int> funcs;
    std::vector<int> rel;
    std::vector<std::vector<int>> jmx;
    bool compute = false;
    bool shared_isb = false;
};

void pa_times(SbProg &p, DepsCtx ctx);

void phase_b_prog(SbProg &p, const DepsCtx &ctx, int shader_type, SbStats *stats);

bool sb_from_words(const Word *in, int n, const Cfg &cfg, int shader_type, SbProg *p);

int phase_b(const Word *in, int n, const Cfg &cfg, int shader_type, std::vector<Word> &out, std::vector<int> &map,
            SbStats *stats = nullptr);

bool strip_phase_b(const Word *code, int n, const std::string &consts, std::vector<Word> *in, Cfg *cfg,
                   std::vector<int> *keep);

std::vector<int> jump_table(const SInst *code, int at, const std::string &consts, const std::function<bool(int)> &ok);

}
}
}

#endif
