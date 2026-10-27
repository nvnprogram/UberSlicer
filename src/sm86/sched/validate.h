
#ifndef UB_SM86_SCHED_VALIDATE_H
#define UB_SM86_SCHED_VALIDATE_H

#include <string>
#include <vector>

#include "prog.h"

namespace ub {
namespace sm86 {
namespace sched {

enum HazardKind {
    HZ_DECODE,
    HZ_CTL_ROW,
    HZ_EG_STALL,
    HZ_SB_INDEX,
    HZ_REUSE_EG,
    HZ_MIN_NEXT,
    HZ_RAW_FIXED,
    HZ_WAW_FIXED,
    HZ_WAR_FIXED,
    HZ_RAW_SB,
    HZ_WAW_SB,
    HZ_WAR_SB,
    HZ_SB_DELAY,
    HZ_COUNT
};

struct Hazard {
    int at;
    int from;
    int kind;
    int need;
    int have;
};

int validate(const Word *code, int n, const std::string &consts, int shader_type, std::vector<Hazard> *out);

}
}
}

#endif
