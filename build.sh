#!/bin/sh
# uberspec build.  One line, from anywhere:  ./build.sh
#
#   src/    ->  build/*.o  ->  out/uberspec  (out/uberspec.exe on Windows)
#
# No dependencies beyond a C99 + C++17 toolchain.  Every object is named
# explicitly and all of them are always built, so the binary can only be made
# of the sources in src/.
set -e
cd "$(dirname "$0")"

CXXFLAGS="-O3 -std=c++17 -Wall -Wextra -Wno-array-bounds"
CFLAGS="-O3 -std=c11 -w"

case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) EXE=out/uberspec.exe ;;
  *)                    EXE=out/uberspec ;;
esac

mkdir -p build out

CXX_SRC="fastalloc xxh3 decode spec sm86/spec86 alloc emit reorder passes sm86/isa_sm86 sm86/sched86 main"
OBJS="build/scheduler.o"

gcc $CFLAGS -iquote src/sm50 -c src/sm50/sched/scheduler.c -o build/scheduler.o
for f in $CXX_SRC; do
  o="build/$(basename "$f").o"
  g++ $CXXFLAGS -c "src/$f.cpp" -o "$o"
  OBJS="$OBJS $o"
done
for f in sm86; do
  g++ -O2 -std=c++17 -Wall -Wextra -Wno-array-bounds -c "src/sm86/$f.cpp" -o "build/$f.o"
  OBJS="$OBJS build/$f.o"
done
for f in classify deps ext issue machine opex owo phase_a phase_b prog sb sb_cfg validate varying; do
  o="build/sched_$f.o"
  g++ -O2 -std=c++17 -Wall -Wextra -c "src/sm86/sched/$f.cpp" -o "$o"
  OBJS="$OBJS $o"
done
g++ -O3 -static -o "$EXE" $OBJS

echo "built $EXE"
