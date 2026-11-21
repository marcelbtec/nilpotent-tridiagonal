#!/bin/bash
# Reruns every program of this directory and stores the outputs, without the timings, in out_*.txt.
#
#   computations/run_all.sh
#
# Needs python3 with numpy and sympy, and a C compiler with OpenMP. Environment:
#   PYTHON  the Python interpreter (default python3)
#   CC      the C compiler (default gcc; on macOS use a Homebrew gcc, e.g. CC=gcc-15)
#   NEXH    largest size for the exhaustive search of check_folds.py (default 27)
# Run time: about 3 minutes on 14 cores, about 15 minutes on 2 cores.
# The script exits with status 1 if a program fails or prints a FAIL line.
set -uo pipefail
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
CC=${CC:-gcc}
NEXH=${NEXH:-27}
mkdir -p bin
status=0

strip_timings() { sed -E 's/ +\([0-9]+ s\)$//'; }

run() {  # run <name> <command ...>: output to out_<name>.txt
  local name=$1; shift
  echo "== $*"
  if ! "$@" | strip_timings > "out_$name.txt"; then
    echo "   the program exited with an error"; status=1
  fi
  if grep -q "FAIL" "out_$name.txt"; then
    echo "   FAIL line in out_$name.txt"; status=1
  fi
}

run check_folds        "$PY" check_folds.py "$NEXH"
run check_proof        "$PY" check_proof.py
run check_newproofs    "$PY" check_newproofs.py
run check_revision     "$PY" check_revision.py
run fullfamily         "$PY" fullfamily.py 12
run check_multiplicity "$PY" check_multiplicity.py
run ep_fold            "$PY" ep_fold.py

for prog in valuation mult lowsym; do
  if ! "$CC" -O3 -march=native -fopenmp -o "bin/$prog" "$prog.c"; then
    echo "   could not compile $prog.c with $CC"; status=1
  fi
done
if [ -x bin/valuation ]; then run valuation bin/valuation 21; fi
if [ -x bin/mult ]; then
  echo "== bin/mult 15 ; bin/mult 31"
  { bin/mult 15 && bin/mult 31; } > out_mult.txt || status=1
fi
if [ -x bin/lowsym ]; then
  # the two masks are printed by: python3 twists.py 6 3
  masks=$("$PY" twists.py 6 3 | awk '{print $3, $4}')
  echo "== bin/lowsym 6 3 $masks"
  # shellcheck disable=SC2086
  bin/lowsym 6 3 $masks > out_lowsym.txt || status=1
fi

if [ "$status" -eq 0 ]; then echo "all programs passed"; else echo "SOME PROGRAMS FAILED"; fi
exit "$status"
