# h ≤ 2000 sieve on the Threadripper workstation (runbook, 2026-10-10)

Goal: no imaginary quadratic field with 6·2^28 ≤ |d| ≤ 1.65·10^15 has h(−d) ≤ 2000, except those listed
by the post-processing (`found.txt`). Together with the Lean theorem for h > 2000 above
e^{T_2000} = 1.6069·10^15 (T_2000 = 35.0131, to be added to `lean/`) and the Mosunov–Jacobson tables below
6·2^28, this gives the complete list for h ≤ 2000. Estimates: `../TESTING.md`, "Pilot for N = 2000"
(30–36 h on the 6-core reference machine; about 2–3.5 h expected with 96 cores).

## Software (on the Threadripper machine)

| needed | why | Ubuntu package |
|---|---|---|
| gcc ≥ 12 (13 recommended) | compiles `qsieve.c` with `-march=native` (AVX-512 on Zen 4) | `build-essential` |
| PARI/GP ≥ 2.15 | `postproc.gp` (exact class numbers of residual d) and `postproc_test.gp` | `pari-gp` |
| git, xz-utils, coreutils | pull the repo, pack the results | usually present |

Not needed: SageMath, Python, Lean.

```
sudo apt install build-essential pari-gp xz-utils
```

## Steps

```
cd <clone of the repo> && git pull
cd qsieve/tr2000
S=$PWD/run_tr2000.sh
bash $S env       # writes ~/qsieve-tr2000/env.txt; check that the CPU and avx512f are listed
bash $S build     # compiles, self-test; must print "BUILD OK" (and SIMD=AVX-512)
bash $S pptest    # PARI/GP check, ~2 min; must print "PPTEST OK"
bash $S pilot     # ~5-15 min; prints the predicted wall times of gap and main
bash $S gap       # main run 1: [6*2^28, 2^40]
bash $S main      # main run 2: [2^40, 1.65e15]
bash $S pack      # ~/qsieve-tr2000/tr2000_results.tar.xz + .sha256
```

- All work files go to `~/qsieve-tr2000` (`WORK=...` to change); the clone stays clean.
- Worker count: `J=188` by default (192 threads, 4 left for the system). Change with `J=... bash $S ...`;
  use the same `J` for a run and its postproc (the script does this).
- `gap` and `main` are long: run them inside `tmux` or with `nohup bash $S main > main.out 2>&1 &`.
  Progress: `tail ~/qsieve-tr2000/runs/main2000/log.0.txt` (every 600 s, with an ETA).
- Each step checks itself and stops with `FAILED: ...` on a problem (failed worker, bound-check failure,
  postproc not finished). A run directory that already exists is not overwritten.

## Expected results

- `gap`: `failed workers: 0`; the postproc line lists the residuals and `found h <= 2000: k`.
  k may be positive if some field with h ≤ 2000 has |d| ≥ 6·2^28 (then these are new list entries).
- `main`: `failed workers: 0`, `residual 0` expected, `found h <= 2000: 0`.

## Bring back

Copy `tr2000_results.tar.xz` and `tr2000_results.sha256` to the main machine (or tell Claude where
they are). Then, on the main machine: the logs go to `qsieve/logs/`, the list for h ≤ 2000 is extracted
from the Mosunov–Jacobson tables (`computations/mj_extract.py ... 2000 ...`) plus `found.txt`, and the Lean
side adds `zero_gap_for_h2000`, `class_bound_h2000` and `classNumber_gt_2000` (with a Comparator rerun).

## Dry run (2026-10-10, reference machine, 12 processes)

All steps on small ranges with `WORK` in the scratchpad: `build` (SIMD=AVX-512, PASS), `pptest` (PASS,
2 min), `gap` on [2^28, 2^28 + 2^24] (a range with known fields: 135,648 residuals, 95,845 found with
h ≤ 2000), `main` on [2^40, 1.1·10^12] (residual 0), `pack`: all OK.

Fix (2026-10-10, after the first try on the Threadripper): `pptest` failed with "readstr: the PARI stack
overflows" (apt gp 2.15 default parisize 8 MB). All gp calls now run as
`gp -q -f -D parisize=2000000000 -D parisizemax=16000000000` (`-f`: ignore ~/.gprc; `GP=...` selects the
binary). Re-tested on the reference machine with the apt gp 2.15.4 and no gprc: `pptest` PASS, and the
small `gap` run gives the same 95,845 fields as with gp 2.17.4.
