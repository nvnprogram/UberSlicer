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

CXXFLAGS="-O2 -std=c++17 -Wall -Wextra -Wno-array-bounds"
CFLAGS="-O2 -std=c11 -w"

case "$(uname -s)" in
  MINGW*|MSYS*|CYGWIN*) EXE=out/uberspec.exe ;;
  *)                    EXE=out/uberspec ;;
esac

mkdir -p build out

CXX_SRC="xxh3 decode spec alloc emit reorder passes main"
OBJS="build/scheduler.o"

gcc $CFLAGS -c src/scheduler.c -o build/scheduler.o
for f in $CXX_SRC; do
  g++ $CXXFLAGS -c "src/$f.cpp" -o "build/$f.o"
  OBJS="$OBJS build/$f.o"
done
g++ -O2 -static -o "$EXE" $OBJS

echo "built $EXE"
