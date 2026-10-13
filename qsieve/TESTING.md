# qsieve: build, tests, measurements

Results are conditional on [SZ] only through the choice of the range bound D(N). The sieve and the
post-processing themselves are unconditional.

Notation of the paper (Section "The sieve") versus this file and the code: the blocks of 35 primes are
G_j in the paper; the set of primes P, P_0 is \mathcal P, \mathcal P_0; the bound B of the closed-form
test (iii) is b^*, its split primes q_i are p_i, and their number k is t.

## Build

```
gcc -O3 -march=native -Wall -Wextra -o qsieve qsieve.c -lm   # from 2026-10-09; before: -O2
./qsieve -V                                  # self-test of all symbol tables and mask implementations (must print PASS)
./qsieve -N 200 -a LO -b HI [-j 12] [-i 1200] [-o outdir]
QS_DIR=outdir QS_N=200 QS_NPROC=12 gp -q postproc.gp < /dev/null
```

Each worker `w` writes `outdir/log.w.txt` every `-i` seconds (default 1200 = 20 min). A log line
gives the units done, the number of d examined, exact passes, residuals, elapsed time and ETA.
Uncertified d go to `outdir/residual.w.txt`; `postproc.gp` writes `outdir/found.txt`.

## Tests (2026-10-08)

| test | what | result |
|---|---|---|
| A | direct mode, N = 100, 3 ≤ d ≤ 2.5·10^6, then postproc; compared with `../computations/watkins_h100_list.txt` | identical (42,272 fields), PASS |
| B | class mode with `-T` (every class examined), 2^40 ≤ d ≤ 2^40 + Q + 12345; counts of d, classes and two-d classes against exact counts | 51,757,549,955 / 51,757,545,840 / 4,115: PASS |
| V | `-V`: symbol tables versus direct Kronecker symbols on 666,511 random valid d < 2^62 | 0 mismatches, PASS |
| ASan | `-fsanitize=address,undefined`, small direct run | no errors |

**Bug found by test B and fixed.** `compsym[NSMALL][16]` was too short for the moduli 17–29: the
writes overflowed into the next rows and corrupted the small-prime symbols. Such corruption could
make certification unsound. Test A did not catch it, because at small d almost everything goes to the
exact path. Test B (class counts) caught it. The fix is `compsym[NSMALL][32]`. The new `-V`
self-test detects the old bug (167,299 mismatches, exit code 4).

## Test C: throughput (normal mode, 12 processes, 2^40 ≤ d ≤ 2^40 + 2Q, length 3.1·10^11)

| N | wall | user | d examined individually | exact passes | residual |
|---|---|---|---|---|---|
| 200 | 154 s | 1775 s | 8.46·10^9 (8.2% of valid d) | 2.40·10^7 | 0 |
| 1000 | 2080 s | 24054 s | 3.00·10^10 | 2.87·10^9 | 0 |

- **Residuals.** No residuals in either run, so `postproc.gp` (GP reduced-form counting for
  d ≥ 2·10^10) is not a bottleneck. No change is needed there.
- **Extrapolation with the current code** (rate at 2^40, which is an upper bound since the work per
  d decreases with d):
  - N = 200 up to D_A(200) = 2.55·10^15: about 1.3·10^6 s, roughly 2 weeks wall on 12 processes.
  - N = 1000 up to D_A(1000) = 7.1·10^16: about 4.8·10^8 s. Infeasible.
- **Where the time goes, measured.**
  1. The exact pass (phase 3) takes about 8 µs each. It uses Jacobi symbols over all primes ≤ X and
     repeated DFS counting. For N = 1000 it accounts for about 92% of the CPU time; for N = 200,
     about 10–15%.
  2. Phase 2 set checks take about 0.2 µs per examined d (a 64-bit modulus per prime).
  3. Class enumeration takes about 5·10^10 iterations per segment.
- **Optimizations justified by these measurements (not yet done).**
  - (a) A cheap closed-form lower bound before the exact pass. If k split primes q ≤ B are found and
    W0 is the weighted count of pattern products ≤ X/B², then h ≥ W0(2k² + 1).
  - (b) Table lookups instead of Jacobi symbols in the exact pass.
  - (c) Incremental residues d mod p along a class at large d.

## Optimizations 1 and 2 (2026-10-08)

1. **Phase 2b, closed-form bound.**
   - Count the split primes q among the 1400 sieving-set primes (31 to about 11,800), at thresholds
     8, 16, …, 1024, 1400 primes.
   - With W0 = the weighted count of pattern products m ≤ X/B², precomputed per segment and per
     pattern, the products m, m·q_i and m·q_i·q_j are distinct minima ≤ X. Hence
     h ≥ W0·(2k² + 1).
2. **Faster exact pass.**
   - Table lookups replace Jacobi symbols for the sieving-set primes.
   - The DFS recount happens only when the number of split primes grows by a factor of 1.5.

**Checks.**
- `-V` self-test, now also covering `sym()`: 0 mismatches.
- Test A: identical (42,272 fields).
- `-C` (each bound certification re-verified by the exact count), N = 1000:
  - d ≈ 10^11: 79,104 bound certifications, 0 failures;
  - d ≈ 10^9: the bound is never used because X is too small, as expected.
- ASan with `-C`: no errors.

**Test C again** (2^40 ≤ d ≤ 2^40 + 2Q, 12 processes):

| N | wall (before → after) | user | bound certifications | exact passes (before → after) | residual |
|---|---|---|---|---|---|
| 200 | 154 s → 148 s | 1709 s | 2.40·10^7 | 2.40·10^7 → 0 | 0 |
| 1000 | 2080 s → 677 s | 7937 s | 2.86·10^9 | 2.87·10^9 → 1.6·10^7 | 0 |

**Where the time goes now.**
- Almost all of it is phase-2 set checks, about 0.2 µs per examined d (a 64-bit modulus per prime).
- Extrapolating the 2^40 rate (an upper bound, since the examined fraction falls with d):
  - N = 200: about 9–14 days;
  - N = 1000: years.
- Most of the volume lies in the top segments (d ≈ 2^50–2^56), where each class mod Q contains
  10^3–10^5 values of d.

**Next optimization, justified by these numbers: bit-parallel sieving along each class (Watkins).**
- Along a class r + kQ, the symbol (−d|p) is periodic in k with period p.
- So a bitmask over k of "some prime of set j splits" costs about K/64 word operations per prime.
  Today it costs one modulus per d per prime.
- The expected gain is 10–100× in the top segments.

## Optimization 3: bit-parallel sieving along classes (2026-10-08)

**Method.** For each table prime p, the periodic bit pattern S_p[k] = [k·(Q mod p) mod p is a split
residue] is stored. Along a class d_k = d0 + kQ, the split bits are S_p shifted by
c = (d0 mod p)·(Q mod p)^(−1) mod p. So 64 consecutive d cost two word reads and shifts. The masks for
the sets are ORs over their 35 primes; certification is the AND over the needed sets. Uncertified bits
go to phases 2b and 3. Classes with K ≥ 32 values of d use this path (`-K`); shorter classes stay scalar
(`-S` forces scalar).

**Checks.**
- `-V`: the bit-parallel mask agrees with direct per-d checks on 3,066,497 (d, sets) cases.
- Scalar versus bit-parallel (`-K 2`, N = 1000, 2^40 + [0, 2Q]): all counters identical
  (d 30,026,860,180; bound 2,856,885,072; exact 16,260,611; residual 0).
- Test A: identical. Test B: identical.
- ASan/UBSan on the bit-parallel path: 5 minutes, 38M classes, 0 errors.

**Cost model.**
- A bit-parallel class costs about need·35·(setup + W word operations), with no early exit.
- A scalar class costs about K·need·2 modular operations, exiting early at the first split prime.
- Break-even is around K ≈ 20. With K = 2 the bit-parallel path is about 6× slower (3897 s against
  677 s), which is expected and is why the threshold is K ≥ 32.

**Measurement at d ≈ 2^50** (12 processes):

| run | range | d examined | user | per examined d | wall |
|---|---|---|---|---|---|
| scalar, N = 1000 | 2^50 + [0, 2Q] | 1.79·10^10 | 2877 s | 0.160 µs | 248 s |
| bit-parallel, N = 1000 | 2^50 + [0, 200Q] (K = 200) | 1.79·10^12 | 24870 s | 0.0139 µs (11.5×) | 2148 s |
| bit-parallel, N = 200 | 2^50 + [0, 200Q] | 5.31·10^11 | 5332 s | 0.0100 µs | 471 s |

No residuals, no exact passes, and almost no bound fallbacks (230 and 44).

**Projected wall time on 12 processes for the full runs** (2^40 < d ≤ D_A(N)):
- Segments below 2^43 (K < 32) run scalar, at about 2·10^9 d per second: about 1 h.
- N = 200 (to 2.55·10^15) runs at ≥ 6.6·10^10 per second: **about 10–12 h**.
- N = 500 (to 1.7·10^16), at about 3·10^10 per second: about 1 week.
- N = 1000 (to 7.1·10^16), at 1.45·10^10 per second: about 1–2 months.

**Possible further gains, not needed for N = 200.**
- AVX2/AVX-512 words (4–8×).
- An early exit once a set mask is full.
- Sharper per-pattern set requirements using actual set primes rather than the set maximum.

**Update (2026-10-08, revised constant).** With the Mertens-route constant,
D_A(200) = 8.19·10^12 and D_A(1000) = 2.57·10^14. The ranges and times
above refer to the first version's D(N) and are now upper bounds.

## Main run N = 200 (2026-10-08)

```
./qsieve -V                                                     # PASS
nice -n 10 ./qsieve -N 200 -a 1099511627776 -b 2560000000000000 -o runs/main200
QS_DIR=runs/main200 QS_N=200 QS_NPROC=12 gp -q postproc.gp < /dev/null
```

- Range: 2^40 ≤ d ≤ 2.56·10^15, which is the first version's D_A(200), about 300 times the revised D_A(200) = 8.19·10^12.
- Work: 8004 units, 12 workers, all finished; wall time 17,528 s (4.9 h, 14:36–19:28 JST).
- Totals over the workers:
  - 4.52·10^13 d examined individually;
  - 3.95·10^10 classes;
  - 2.54·10^8 bound certifications (phase 2b).
- Exact passes 0, residual 0, bound-check failures 0. `postproc.gp`: **found h ≤ 200: 0**.
- **Result** (unconditional, as a computation): no imaginary quadratic field with discriminant −d,
  2^40 ≤ d ≤ 2.56·10^15, has h(−d) ≤ 200.
- **Combined with [SZ]**: D_A(200) = 8.19·10^12 lies in this range, so, conditional on [SZ], every
  field with h ≤ 200 has d < 2^40.

## Gap run N = 200 below 2^40 (2026-10-08)

- Command: `qsieve -N 200 -a 1610612736 -b 1099511627776 -i 600 -o runs/gap200`. The range is
  6·2^28 ≤ d ≤ 2^40; below 6·2^28 the Mosunov–Jacobson files are used (`../computations/mj_extract.py`).
- Run: 2103 units, 12 workers, all finished in 1007 s.
- Totals:
  - 1.16·10^11 d examined;
  - 3.72·10^8 bound certifications;
  - 1.45·10^7 exact passes.
- Residual 0. **found h ≤ 200: 0.**

## Regression against Mosunov–Jacobson, N = 2000 (2026-10-08)

- Command: `qsieve -N 2000 -a 268435456 -b 1610612735 -o runs/reg2000`, then `postproc.gp`.
- Range: 2^28 ≤ d < 6·2^28, i.e. the LMFDB files `cl{3,7}mod8.{1..5}` and `cl{4,8}mod16.{1..5}`.
- Run: 288 units, 541 s for the sieve, then about 90 s of postproc.
- Counters:
  - 4.47·10^8 d examined;
  - 3.28·10^8 exact passes;
  - 821,461 residuals, of which 773,558 are fundamental. These go to PARI `qfbclassno`, which is
    unconditional below 2·10^10.
  - At this size and N the closed-form bound (phase 2b) never applies, because X = √(d/4) is small.
- **Result: `found.txt` (537,404 pairs (d, h) with h ≤ 2000) is identical to the pairs with h ≤ 2000
  extracted from the data.** This tests completeness and soundness at once, with about 5·10^5 positive
  cases.
- Data checks:
  - the file format was decoded by us;
  - 160 random entries agree with `qfbclassno`;
  - the k = 0 files reproduce Watkins' h ≤ 100 list exactly (42,272 fields).

## Experiment: AVX-512 for the bit-parallel class mask (2026-10-08)

Benchmark copies are in the session scratchpad; `qsieve.c` is **not changed yet**.

**Setup.** `-N 1000`, one work unit (chunk 0) of a dyadic segment, selected with a test-only
environment variable `QS_MAXCHUNK`.

**Where the time goes now** (rdtsc instrumentation, segment [2^46, 2^47)):
- `class_sets_mask` takes about 97% of the time. Per call: need ≈ 4.3 sets × 35 primes, W = 8 words.
- It is dominated by the two 64-bit `%` per prime (d0 mod p, then ·Binv mod p), not by the word loop.
- perf is unavailable (`perf_event_paranoid` = 4).

**Variants.**
1. *Division-free*: Barrett reduction for d0 mod p and Lemire fastmod for the second reduction.
   The patterns are extended by 64 words, so no window wraps.
2. Variant 1 compiled with SSE / AVX2 / AVX-512 auto-vectorization.
3. *AVX2 registers*: the masks are kept in four ymm registers (W ≤ 16) and loaded with masked loads.
4. *AVX-512 registers*: the masks are kept in two zmm registers. A shift count of 64 gives 0, so
   off = 0 needs no branch. The offsets for 8 primes at a time are computed in double precision,
   which is exact for d0 < 2^52.

**Results.**
- Every variant passes `-V` (3,066,497 bit-parallel cases, 0 mismatches).
- Every variant gives counters identical to the current build.

| build | [2^46, 2^47), 1 chunk, 1 proc | same, 12 chunks, 12 procs | [2^47, 2.6·10^14], 1 chunk, 1 proc |
|---|---|---|---|
| current (`-O2 -march=native`) | 62.9 s | 132.6 s | 75.7 s |
| 1 at `-O2` (any ISA) | 23.5 s | — | — |
| 2: SSE / AVX2 / AVX-512 at `-O3` | 20.0 / 15.7 / 15.1–15.5 s | 43.8 s (native) | — |
| 3: AVX2 registers | 15.3 s | 38.2 s | 16.4 s |
| 4: AVX-512 registers | **12.6 s** | **34.5 s** | **11.2 s** |

**Reading.**
- Most of the gain (about 2.7–3×) comes from removing the divisions, and is independent of the ISA.
- AVX-512 over AVX2 with the same register scheme is 1.2–1.45× on one process. It is 1.1× with 12
  processes on the 6 hyperthreaded cores of the Xeon w3-2425, which share the vector units.
- Overall versus the current build: 3.8× (12 processes, 2^46) and 6.8× (1 process, top segment).
- After the change, the class enumeration loop (`i128 % Q` per class) is a visible part of the remaining
  time: about 40% at 2^46.
- The cheaper bit-parallel path moves the break-even point K_min (`-K`, currently 32) down. This
  would also shorten the scalar segments [2^40, 2^43], estimated at about 5 h for N = 1000. This
  has not been measured.

**To adopt.**
- Merge variant 4, with variant 3 as fallback when AVX-512 is absent and `class_sets_mask_old` when
  W > 16 or d0 ≥ 2^52.
- Re-run `-V`, Test A/B, and the N = 2000 regression.
- Re-measure K_min.

## Adopted: division-free / SIMD class mask (2026-10-09)

**Code changes.**
- `class_sets_mask` dispatches to one of three implementations:
  - the AVX-512 version (or AVX2, chosen at compile time) for W ≤ 16 and d0 < 2^52;
  - the division-free scalar version otherwise (W ≤ 64);
  - the original version for W > 64.
- `-M 1` / `-M 2` force the original / division-free version, for cross-checks.
- `-U n` processes only class chunks < n. It is for benchmarking only, and is flagged in the banner.
- `-V` now tests all three implementations.
- Build: `-O3 -march=native`.

**Tests.**
- `-V`: 9,199,491 bit-parallel (d, sets) cases, 0 mismatches, PASS. The same holds for builds with
  AVX-512, with AVX2 only (`-mno-avx512f`), and with `-march=x86-64` (no SIMD).
- T1, `-N 1000 -K 2` on 2^40 + [0, 2Q] (mask-heavy, W = 1): d 30,026,860,180, bound 2,856,885,072,
  exact 16,260,611, residual 0. This is identical to the scalar run recorded above. Wall time
  1751 s (before: 3897 s); scalar `-S`: 677 s.
- T2, top segment [2^47, 2.6·10^14], 12 chunks, 12 processes:
  - counters identical to the pre-change binary (d 158,427,365,854; bound 418,083,771;
    classes 206,262,928);
  - **160 s → 34 s**.
- T3, d0 ≥ 2^52 (2^52 + [0, 200Q], 12 chunks): `-M 0/1/2` give identical counters.
- Test A: identical to Watkins' list (42,272).
- Regression N = 2000 on [2^28, 6·2^28): identical (537,404).
  - Test A and this regression use direct mode, so they do not exercise the mask. They are run only
    as a no-regression check.

## Scalar range [2^40, 2^43]: division-free scalar path and K_min (2026-10-09)

**Changes.**
- Every `d % p` for the table primes now uses Barrett reduction (`modp_t`). This covers `handle_d`,
  `bound_certify` (up to 1400 primes per d) and `sym`.
- Default `-K` (K_min) changed from 32 to 10.

**Measurements.** N = 1000, 12 chunks of 667, 12 processes. Within each column the counters are
identical across all K and both builds.

| segment (d per class) | before, K=32 | before, K=16 / 8 / 4 | div-free scalar, K=32 | div-free, K=4 | final, K=10 |
|---|---|---|---|---|---|
| [2^40, 2^41) (7–8) | 46.8 s | 46.4 / 49.3 / 41.2 s | 34.6 s | 41.6 s | **34.8 s** |
| [2^41, 2^42) (14–15) | 71.9 s | 71.7 / 36.0 / 35.9 s | 52.3 s | 35.2 s | **34.9 s** |
| [2^42, 2^43) (28–29) | 121.7 s | 34.2 / 34.3 / 34.2 s | 88.2 s | 32.5 s | ≈ 32.5 s |

- Classes of 7–8 d are cheaper on the scalar path. Classes of 14 or more d are cheaper bit-parallel.
  K_min = 10 separates the two.
- The class enumeration itself (about 7.7·10^10 iterations per segment) costs about 40 s of wall time
  per segment. It is negligible.

**Tests (final build).**
- `-V`: PASS.
- Test A: identical (42,272).
- Regression N = 2000: identical (537,404). Sieve wall time 478 s, before 541 s.
- The mask tests T1–T3 above are unaffected, since the bit-parallel code is unchanged.

**Projected N = 1000 main run** (2^40 ≤ d ≤ 2.6·10^14, 12 processes): about 1900 s per dyadic
segment, i.e. 12 chunks at about 34 s, scaled by 667/12.
- This rate is measured at 2^40, 2^41, 2^42, 2^46 and the top segment; 2^43–2^45 are assumed similar.
- Eight segments give **about 4–4.5 h**, against about 12 h with the code of 2026-10-08.

## postproc.gp: subgroup algorithm replaces the O(d) count (2026-10-09)

**Method.** For residuals with d ≥ 2·10^10, `classno_upto(d, N)` builds the subgroup generated by the
reduced prime forms of the split and ramified primes p ≤ √(d/3).
- It stops at N+1 elements, which proves h > N.
- If the primes run out first, the subgroup is the whole class group, so h equals its order.
- Both outcomes are unconditional. The argument is in the file header.
- Coset disjointness is checked at run time.
- d < 2·10^10 still goes to `qfbclassno`.

**Bug found by the test and fixed before adoption.**
- `qfbprimeform` need not return a reduced form, so its key could miss a class already in the group.
- This added duplicate cosets and over-counted, i.e. a false "h > N". It showed up as a 50 GB runaway.
- Fix: `qfbred` on every prime form, plus the disjointness check.

**Test file.** `postproc_test.gp` (`gp -q postproc_test.gp < /dev/null`, about 2 min) checks against
`qfbclassno`, with 0 mismatches:
- all 6,077 fundamental d ≤ 20,000;
- 300 random d ≤ 2·10^10, both the full value and N = h−1, h, 1000;
- 300 random entries of `mj_h200_list.txt`.

Result: **POSTPROC TEST PASS**.

**Timing at d ≈ 2.6·10^14.**
- 3 ms per typical residual (h > 1000).
- About 0.5 s for the full prime loop up to 9.3·10^6, which is the worst case of a genuine candidate.
- gp2c is not needed: the time goes to library calls.

## Pilot for N = 1000 (2026-10-09)

**Gap range.** For each dyadic segment between 6·2^28 and 2^40, a window of 1/32 of the segment was run
with 12 processes, followed by postproc.

| segment | sieve | d | bound | exact | residual |
|---|---|---|---|---|---|
| [6·2^28, 2^31) | 5.0 s | 1.12·10^7 | 0 | 4.42·10^6 | 0 |
| 2^31 | 7.9 s | 2.24·10^7 | 3,269 | 8.15·10^6 | 0 |
| 2^32 | 11.9 s | 4.47·10^7 | 1.36·10^5 | 1.31·10^7 | 0 |
| 2^33 | 18.4 s | 8.95·10^7 | 2.64·10^5 | 2.07·10^7 | 0 |
| 2^34 | 24.1 s | 1.79·10^8 | 6.01·10^6 | 2.60·10^7 | 0 |
| 2^35 | 35.7 s | 3.58·10^8 | 8.79·10^6 | 3.89·10^7 | 0 |
| 2^36 | 46.8 s | 7.16·10^8 | 2.08·10^7 | 4.77·10^7 | 0 |
| 2^37 | 12.6 s | 1.43·10^9 | 9.73·10^7 | 9.81·10^5 | 0 |
| 2^38 | 22.0 s | 2.86·10^9 | 1.37·10^8 | 1.33·10^6 | 0 |
| 2^39 | 38.1 s | 5.73·10^9 | 2.10·10^8 | 1.51·10^6 | 0 |

- Total 222.5 s, so the **full gap run takes about 2.0 h**.
- There are no residuals, so `postproc.gp` has nothing to do in these windows.
- Segments below 2^37.2 (shorter than Q) run in direct mode, which is dominated by exact passes.
  From 2^37 on, class mode is faster per d.

**Main range.** 12 of 667 chunks, 12 processes:

| segment | time | d |
|---|---|---|
| 2^43 | 31.6 s | 1.39·10^10 |
| 2^44 | 30.6 s | 2.67·10^10 |
| 2^45 | 29.9 s | 5.08·10^10 |

There are no residuals and no exact passes. Together with the measurements above for 2^40–2^42, 2^46
and the top segment, **the full main run [2^40, 2.6·10^14] takes about 4.1 h** (≈ 1700–1940 s per
segment).

## Regression with positive cases, N = 1000 on [2^24, 2^28) (2026-10-09)

- Command: `qsieve -N 1000 -a 16777216 -b 268435455 -j 11`, then `postproc.gp`.
- Time: sieve 73 s; postproc 194 s for 1,924,044 residuals, all below 2·10^10, so `qfbclassno` is used.
- Counters: d 83,886,081; exact passes 59,757,770; bound certifications 0 (X is too small).
- **Result: `found.txt` is identical to the Mosunov–Jacobson pairs with h ≤ 1000 in this range
  (1,490,910 fields).**
- All fields with h ≤ 1000 lie below 2^28, so this is the positive test that the [2^28, 6·2^28)
  regression cannot provide at N = 1000. It complements the N = 2000 regression.

## Production runs N = 1000 (2026-10-09)

```
./qsieve -V                                                     # PASS
nice -n 10 ./qsieve -N 1000 -a 1610612736 -b 1099511627776 -j 11 -i 600 -o runs/gap1000
QS_DIR=runs/gap1000 QS_N=1000 QS_NPROC=11 gp -q postproc.gp < /dev/null
nice -n 10 ./qsieve -N 1000 -a 1099511627776 -b 260000000000000 -j 12 -i 600 -o runs/main1000
QS_DIR=runs/main1000 QS_N=1000 QS_NPROC=12 gp -q postproc.gp < /dev/null
```

Mask implementation AVX-512 in both runs. Worker logs are in `logs/gap1000/` and `logs/main1000/`.

| run | range | units / workers | wall time | d | bound cert. | exact | classes | residual | found |
|---|---|---|---|---|---|---|---|---|---|
| gap | [6·2^28, 2^40] | 2039 / 11 | 6711 s (02:24–04:16 JST) | 1.77·10^11 | 1.54·10^10 | 5.14·10^9 | 3.29·10^10 | 0 | 0 |
| main | [2^40, 2.6·10^14] | 5336 / 12 | 11,118 s (04:16–07:21 JST) | 1.80·10^13 | 2.28·10^11 | 5.75·10^7 | 9.92·10^10 | 0 | 0 |

- Bound-check failures 0 and failed workers 0 in both runs. The pilot estimates (2.0 h and 4.1 h)
  were accurate (1.86 h and 3.09 h).
- **Result (unconditional, as a computation):** no imaginary quadratic field with
  6·2^28 ≤ d ≤ 2.6·10^14 has h(−d) ≤ 1000. Since D_A(1000) = 2.574·10^14, together with [SZ]
  and the tables this gave the list for h ≤ 1000, conditional on [SZ]. (The paper replaces [SZ]
  by the Lean theorem.)
- Final list: `../computations/mj_extract.py DATADIR 1000 5 OUT` gives 4,115,897 fields (identical to
  the preliminary extraction), largest |d| = 227,932,027 (h = 996). Its h ≤ 100 part equals
  `watkins_h100_list.txt`, and its h ≤ 200 part equals `mj_h200_list.txt`. 2000 random entries with
  200 < h ≤ 1000 agree with `qfbclassno` (d < 2^28, so unconditional).
- Stored as `../lists/imq_h1000.txt.xz` (10.5 MB); `../lists/SHA256SUMS` has the SHA-256 of the
  uncompressed file.

## Extension N = 1000 to 3.2·10^14 (2026-10-09)

Purpose: with elementary inputs only, D(1000) = 2.911·10^14, above the main run's endpoint 2.6·10^14.

```
gcc -O3 -march=native -Wall -Wextra -o qsieve qsieve.c -lm   # rebuilt from 705ea5570: md5 872f6a06... = binary of main1000
./qsieve -V                                                    # PASS (9,199,491 mask cases, 666,511 symbols)
nice -n 10 ./qsieve -N 1000 -a 260000000000000 -b 320000000000000 -j 8 -i 600 -o runs/ext1000
QS_DIR=runs/ext1000 QS_N=1000 QS_NPROC=8 gp -q postproc.gp < /dev/null
```

| run | range | units / workers | wall time | d | bound cert. | exact | classes | residual | found |
|---|---|---|---|---|---|---|---|---|---|
| ext | [2.6·10^14, 3.2·10^14] | 1334 / 8 | 1738 s (19:38–20:07 JST) | 3.77·10^12 | 4.63·10^9 | 0 | 1.95·10^10 | 0 | 0 |

- Failed workers 0, bound-check failures 0. Mask AVX-512. A Lean build ran concurrently (8 of 12 cores
  for the sieve). Worker logs in `logs/ext1000/`.
- **Result (unconditional, as a computation):** no imaginary quadratic field with
  2.6·10^14 ≤ d ≤ 3.2·10^14 has h(−d) ≤ 1000. With the runs above: none with 6·2^28 ≤ d ≤ 3.2·10^14.
- This covers D(1000) = 2.911·10^14 of the elementary-input constant (with the step from the zero gap to h unchanged).

## Extension N = 1000 to 3.5·10^14 (2026-10-09)

Purpose: the combination that is formalized in Lean (upstream pivot bounds + elementary inputs,
`../computations/certify_c2_lean.txt`) needs D(1000) ≈ 3.44·10^14, above 3.2·10^14.

```
# same binary as main1000 / ext1000 (md5 872f6a06...)
nice -n 10 ./qsieve -N 1000 -a 320000000000000 -b 350000000000000 -j 8 -i 600 -o runs/ext1000b
QS_DIR=runs/ext1000b QS_N=1000 QS_NPROC=8 gp -q postproc.gp < /dev/null
```

| run | range | units / workers | wall time | d | bound cert. | exact | classes | residual | found |
|---|---|---|---|---|---|---|---|---|---|
| ext b | [3.2·10^14, 3.5·10^14] | 667 / 8 | 794 s (23:18–23:31 JST) | 1.86·10^12 | 2.31·10^9 | 0 | 9.61·10^9 | 0 | 0 |

- Failed workers 0, bound-check failures 0. Mask AVX-512. Lean builds ran concurrently. Worker logs in
  `logs/ext1000b/`.
- **Result (unconditional, as a computation):** no imaginary quadratic field with
  3.2·10^14 ≤ d ≤ 3.5·10^14 has h(−d) ≤ 1000; with the runs above, none with 6·2^28 ≤ d ≤ 3.5·10^14.

## Pilot for N = 2000 (2026-10-10)

Purpose: cost of h ≤ 2000. The Lean grid gives T_2000 = 350131/10000 (e^T = 1.6069·10^15, zero gap
c = 1193/200000, chain index 148; `computations/lean_grid.gp` with N = 2000 added). Proposition 9 of the paper then holds
with log margin 0.072 (`lean_h_cert.gp` with N = 2000 added). Machine: Xeon w3-2425 (6 cores, 12 threads),
12 processes, AVX-512 mask, binary md5 872f6a06 (`-V` PASS).

| part | method | N = 1000 | N = 2000 |
|---|---|---|---|
| gap [6·2^28, 2^40] | 1/32 window of each dyadic segment, ×32 | 223 s → 7134 s (actual run: 6711 s) | 1156 s → 36,984 s |
| main [2^40, 1.607·10^15] | `-U 6` (6 of 667 chunks), ×667/6 | — | 817 s → 90,858 s |

- Per-segment ratio N = 2000 / N = 1000 in the gap range: 2.0 (direct mode, below 2^37) to 12 (class mode).
- The N = 1000 pilots overestimated the actual runs by 6% (gap) and 33% (main), so on this machine
  N = 2000 needs about 10 h (gap) + 19–25 h (main), i.e. 30–36 h in total.
- On a 96-core / 192-thread Threadripper PRO 7995WX (Zen 4, AVX-512), with 16 times the cores and
  similar per-core speed, expect a speed-up of 11–16, i.e. about 2–3.5 h in total. To be calibrated by a
  short `-U` pilot on that machine (rebuild with `-march=native`, run `-V` first).
- No residuals in the main sample (bound-check failures 0, failed workers 0).

## Production runs N = 2000 on the Threadripper (2026-10-10)

Machine: AMD Ryzen Threadripper PRO 7995WX (96 cores / 192 threads), gcc 15.2.0, PARI/GP 2.17.3;
188 processes, mask AVX-512. Run with `tr2000/run_tr2000.sh` (`env`, `build`, `pptest`, `pilot`, `gap`,
`main`, `pack`) from a clone with the gp stack fix d1af33ec7 (qsieve.c md5 cc322d85, the same file as in this
repo; self-test `-V` PASS, `postproc_test.gp` PASS). The results came back as `tr2000_results.tar.xz`
(SHA-256 eefd479f…afaf, checked; the file is kept in `logs/tr2000/tr2000_results.sha256`, the tarball
is not committed). Worker logs: `logs/gap2000/`, `logs/main2000/` (with `stdout.txt` and the postproc
output `post.txt`); machine and build records: `logs/tr2000/`.

| run | range | units / workers | wall time | d | bound cert. | exact | classes | residual | found |
|---|---|---|---|---|---|---|---|---|---|
| gap | [6·2^28, 2^40] | 13367 / 188 | 3778 s (16:37–17:40 JST) | 2.20·10^11 | 3.15·10^10 | 3.13·10^10 | 4.89·10^10 | 0 | 0 |
| main | [2^40, 1.65·10^15] | 7337 / 188 | 10,142 s (17:40–20:29 JST) | 1.55·10^14 | 2.81·10^12 | 7.41·10^9 | 1.94·10^11 | 0 | 0 |

- All 188 workers of each run finished all their units (13367/13367 and 7337/7337); bound-check
  failures 0 and failed workers 0; the residual files are empty and `found.txt` is empty in both runs.
- The pilot in `logs/tr2000/` is the first one, with `-U 6` (383 s; it underfilled the 188 workers and
  predicted 11 h 49 min for main). The actual main run took 2.8 h, within the 2–3.5 h estimate above;
  gap took 1.05 h (reference-machine estimate 10 h).
- **Result (as a computation):** no imaginary quadratic field with 6·2^28 ≤ d ≤ 1.65·10^15 has
  h(−d) ≤ 2000. Since e^{T_2000} = 1.6069·10^15 < 1.65·10^15 (`classNumber_gt_2000`;
  `../computations/lean_threshold_match.txt`), together with the tables this gives the complete list for
  h ≤ 2000 (Theorem 2 of the paper): 16,453,493 fields, largest |d| = 1,062,350,083.
