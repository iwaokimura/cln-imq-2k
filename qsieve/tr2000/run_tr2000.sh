#!/bin/bash
# h <= 2000 sieve on a many-core workstation (written for a Threadripper PRO 7995WX, 96 cores / 192 threads).
# Usage:  bash run_tr2000.sh STEP        (run the steps in order; each one checks its own result)
#   env     record the machine and software (env.txt)
#   build   compile qsieve with -march=native, run the self-test (-V), check AVX-512
#   pptest  run postproc_test.gp (PARI/GP check of the post-processing)
#   pilot   short calibration runs (-U), prints the predicted wall time of gap and main
#   gap     N = 2000 on [6*2^28, 2^40], then postproc
#   main    N = 2000 on [2^40, 1.65e15], then postproc
#   pack    collect logs and results into tr2000_results.tar.xz (to bring back)
# Environment: J = number of worker processes (default 188), WORK = working directory (default ~/qsieve-tr2000).
# Needs: gcc (>= 12 for znver4), PARI/GP (gp), coreutils, xz. No Sage, no Python, no Lean.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src=$(cd "$here/.." && pwd)            # qsieve.c and postproc*.gp live one level up
WORK=${WORK:-$HOME/qsieve-tr2000}   # outside the repo, so that the clone stays clean
J=${J:-188}
N=2000
GAP_LO=${GAP_LO:-1610612736}          # 6*2^28 (Mosunov-Jacobson tables cover |d| < 6*2^28)
GAP_HI=${GAP_HI:-1099511627776}       # 2^40
MAIN_LO=${MAIN_LO:-1099511627776}      # 2^40 (closed intervals: overlap at one point is harmless)
MAIN_HI=${MAIN_HI:-1650000000000000}   # 1.65e15 > e^{T_2000} = 1.6069e15 (Lean threshold, T_2000 = 35.0131)
mkdir -p "$WORK"; cd "$WORK"
mkdir -p runs
# PARI/GP: the apt default stack (8 MB) is too small for reading the residual / test files; -f ignores ~/.gprc
GP=${GP:-gp}
gpq() { "$GP" -q -f -D parisize=2000000000 -D parisizemax=16000000000 "$@"; }

die() { echo "FAILED: $*" >&2; exit 1; }

# check the qsieve stdout (failed workers 0) and the postproc summary line (residual handled)
check_run() {  # $1 = run name
  local out=runs/$1.stdout
  grep -q "all workers finished in .* failed workers: 0" "$out" || die "$1: workers failed or did not finish (see $out)"
  ! grep -q "bound-check failures [1-9]" runs/$1/log.*.txt || die "$1: bound-check failures (see runs/$1/log.*.txt)"
  grep -q "POSTPROC DONE" runs/$1.post || die "$1: postproc did not finish (see runs/$1.post)"
  echo "$1: $(grep 'all workers finished' "$out")"
  echo "$1: $(grep 'POSTPROC DONE' runs/$1.post)"
}

run_range() {  # $1 = name, $2 = lo, $3 = hi
  [ -x ./qsieve ] || die "run 'build' first"
  [ ! -e runs/$1 ] || die "runs/$1 exists; move it away before re-running"
  echo "== $1: N = $N, d in [$2, $3], $J processes, start $(date)"
  nice -n 10 ./qsieve -N $N -a $2 -b $3 -j $J -i 600 -o runs/$1 > runs/$1.stdout 2>&1 || die "qsieve exit code $?"
  echo "== $1: sieve done $(date); postproc"
  QS_DIR=runs/$1 QS_N=$N QS_NPROC=$J gpq "$src/postproc.gp" < /dev/null > runs/$1.post 2>&1
  echo "== $1: postproc done $(date)"
  check_run $1
}

case "${1:-}" in
  env)
    { echo "date: $(date)"; echo "host: $(hostname)"; uname -a; lscpu; free -g; gcc --version | head -1;
      echo "gp: $(echo 'print(version())' | gpq)"; echo "J = $J"; } > env.txt 2>&1
    grep -E "Model name|^CPU\(s\)|avx512f" env.txt | cut -c1-120 | sed 's/Flags:.*avx512f.*/Flags: avx512f present/'
    echo "env.txt written" ;;
  build)
    gcc -O3 -march=native -Wall -Wextra -o qsieve "$src/qsieve.c" -lm
    md5sum qsieve "$src/qsieve.c" | tee build.txt
    ./qsieve -V | tee -a build.txt
    grep -q "PASS" build.txt || die "self-test did not PASS"
    grep -q "SIMD=AVX-512" build.txt || echo "WARNING: not built with AVX-512 (check -march=native); slower but correct"
    echo "BUILD OK" ;;
  pptest)
    (cd "$src" && gpq postproc_test.gp < /dev/null) | tee pptest.txt
    grep -q "POSTPROC TEST PASS" pptest.txt || die "postproc_test did not pass"
    echo "PPTEST OK" ;;
  pilot)
    [ -x ./qsieve ] || die "run 'build' first"
    rm -rf runs/pilot_gap runs/pilot_main
    # gap: the range [2^39, 2^39 + 2^34] (1/32 of the most expensive dyadic segment, class mode)
    t0=$(date +%s); ./qsieve -N $N -a 549755813888 -b 566935683072 -j $J -i 600 -o runs/pilot_gap > runs/pilot_gap.stdout 2>&1; t1=$(date +%s)
    # main: U of 667 chunks of every segment of [2^40, 1.65e15]. The range has about 11 segments, so -U U
    # gives about 11*U work units; U >= 2J/11 keeps all J workers busy (with -U 6 and J = 188 only ~66
    # units exist, most workers idle, and the prediction was ~4x too pessimistic: first Threadripper try).
    U=$(( (2 * J + 10) / 11 )); [ $U -lt 6 ] && U=6
    ./qsieve -N $N -a $MAIN_LO -b $MAIN_HI -j $J -i 600 -U $U -o runs/pilot_main > runs/pilot_main.stdout 2>&1; t2=$(date +%s)
    g=$((t1 - t0)); m=$((t2 - t1))
    echo "pilot gap window: $g s (6-core reference machine, 12 processes: 277 s)"
    echo "pilot main -U $U: $m s (reference machine, -U 6, 12 processes: 817 s)"
    # gap total on the reference machine was 36,984 s for 1/32-windows summing to 1156 s; scale by the top window
    echo "predicted gap  ~ $(( g * 36984 / 277 / 3600 )) h $(( (g * 36984 / 277 % 3600) / 60 )) min (upper estimate)"
    echo "predicted main ~ $(( m * 667 / U / 3600 )) h $(( (m * 667 / U % 3600) / 60 )) min (the N = 1000 analogue overestimated by ~30%)"
    grep -h "failed workers" runs/pilot_gap.stdout runs/pilot_main.stdout ;;
  gap)  run_range gap2000  $GAP_LO  $GAP_HI ;;
  main) run_range main2000 $MAIN_LO $MAIN_HI ;;
  pack)
    files=(env.txt build.txt)
    [ -e pptest.txt ] && files+=(pptest.txt)
    for r in gap2000 main2000 pilot_gap pilot_main; do
      for f in runs/$r.stdout runs/$r.post runs/$r; do [ -e "$f" ] && files+=("$f"); done
    done
    tar -cJf tr2000_results.tar.xz "${files[@]}"
    sha256sum tr2000_results.tar.xz | tee tr2000_results.sha256
    echo "PACK OK: bring back tr2000_results.tar.xz and tr2000_results.sha256" ;;
  *) sed -n '2,13p' "$0"; exit 2 ;;
esac
