# Map from the paper to the Lean files

This document is for a reader of the paper "Imaginary quadratic fields of class number at most 2000"
(I. Kimura) who wants to find the Lean counterpart of a numbered statement. It lists, in the order of
the paper, the declarations that formalize each statement, where they are, and where the Lean form
differs from the paper.

Paths are relative to this directory (`lean/`). `B4*.lean` are our files; `vendor/` holds the upstream
files they import (openai/math commit 301488868, directory `OAI/NumberTheory/SiegelZeros`;
PrimeNumberTheoremAnd; TauCeti; AINTLIB, module `BernoulliRegular`); Mathlib (commit d13f23b) is
fetched by Lake into `.lake/packages/mathlib`. Line numbers are those of the `theorem`/`lemma`/`def`
keyword. `B4Replay.lean` (kernel replay) is a tool, not part of the proof.

## Building

    lake build

in this directory builds the default target `B4` (the 20 files listed in `lakefile.lean`) and its
dependencies.

## What has to be trusted

Every proof below is checked by the Lean kernel. What a reader has to check by hand are the statements
of the final theorems, which use only Mathlib notions:

| Statement | Paper | Location |
|---|---|---|
| `B4.ClassNumber.classNumber_gt_100` | Theorem 10, N = 100 | `B4ClassNumber.lean:232` |
| `B4.ClassNumber.classNumber_gt_200` | Theorem 10, N = 200 | `B4ClassNumber.lean:238` |
| `B4.ClassNumber.classNumber_gt_500` | Theorem 10, N = 500 | `B4ClassNumber.lean:244` |
| `B4.ClassNumber.classNumber_gt_1000` | Theorem 10, N = 1000 | `B4ClassNumber.lean:250` |
| `B4.ClassNumber.classNumber_gt_2000` | Theorem 10, N = 2000 | `B4ClassNumber.lean:256` |
| `B4.Chi8.zero_gap_all` | Theorem 1, first bound | `B4Chi8.lean:198` |
| `B4.Chi8.zero_gap_large` | Theorem 1, second bound | `B4Chi8.lean:227` |
| `B4.Chi8.re_LFunction_pos` | Lemma 3 | `B4Chi8.lean:156` |

The same statements, with `sorry` and importing only Mathlib, are the Comparator challenge files
`Challenge/B4ClassNumber.lean` and `Challenge/B4ZeroGap.lean` (see `comparator/README.md`). The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Section 1 (Introduction) and Notation

| Paper | Lean | Location | Proof in | Remarks |
|---|---|---|---|---|
| Theorem 1 (`thm:gap`), first bound | `B4.Chi8.zero_gap_all` | `B4Chi8.lean:198` | B4 | χ is a `DirichletCharacter ℂ q` with real values, `IsPrimitive`, `≠ 1`; `q` is the modulus (= conductor, by primitivity); L is Mathlib's `DirichletCharacter.LFunction`. The case q ≠ 8 is `B4.Cert.zero_gap_all` (`B4Certificates.lean:3156`); q = 8 is excluded by Lemma 3. |
| Theorem 1, second bound | `B4.Chi8.zero_gap_large` | `B4Chi8.lean:227` | B4 | Same as `B4.Chi8.zero_gap_for_h2000` (`B4Chi8.lean:223`) with `GapFromAll` unfolded. |
| Theorem 2 (`thm:main`) | not formalized | — | — | See "Not formalized" below. |
| Zero gap (c, T) (Notation) | `B4.Chi8.GapFromAll` | `B4Chi8.lean:208` | B4 | Exactly the Notation. |
| Zero gap with q ≠ 8 | `B4.GapFrom` | `B4Chain.lean:27` | B4 | Like `GapFromAll` with the extra hypothesis `q ≠ 8`; all certificates are stated for it. `B4.GapOn` (`B4Chain.lean:20`) adds an upper bound `log q ≤ l1`. `B4.Chi8.gapFromAll_of_gapFrom` (`B4Chi8.lean:215`) removes `q ≠ 8`. |

## Section 2 (An explicit zero gap)

| Paper | Lean | Location | Proof in | Remarks |
|---|---|---|---|---|
| Lemma 3 (`lem:chi8`) | `B4.Chi8.re_LFunction_pos`; `B4.Chi8.LFunction_ne_zero` | `B4Chi8.lean:156`; `B4Chi8.lean:190` | B4 | Stronger: for every nontrivial character mod 8 (no primitivity or reality assumed) and every σ > 0, `0 < Re L(σ, χ)`. The proof groups the series in blocks of 8 terms (`B4.Chi8.block_pos`, `B4Chi8.lean:57`), using the convergence of the partial sums from `B4LSeriesCont.lean`. |
| (1) `eq:upper` (Hadamard) | conjunct `harch` of `OAI.SiegelZeros.WeightedTorusJets.source_character_global_greedy_determinant_master_bounds`; proved by `OAI.SiegelZeros.WeightedTorusJets.archimedean_bound_of_integral_jet_determinant` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Characters/CharacterGlobalGreedyDeterminantMasterBounds.lean:19`; `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Determinants/NormSqReal.lean:163` | openai/math | Used unmodified in `b4_explicit_zero_gap`. Lean's `N` is the paper's B, `M = N^4`; Δ lies in the ring of integers of F = ℚ(√d₀, √2), realized inside a cyclotomic field. |
| (2) `eq:lower` | conjunct `hraw` of the same theorem; proved by `OAI.SiegelZeros.WeightedTorusJets.finite_place_bounds_of_source_determinant`, from the divisibility in `OAI.SiegelZeros.WeightedTorusJets.source_character_global_greedy_determinant_divisibility` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Determinants/NormSqReal.lean:282`; `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Selection/RestrictWeightSortedEquiv.lean:367` | openai/math | The prime set is `H < p ≤ U`, `χ(p) = -1`, `p ∤ 2q` (the last condition is implied by the others); θ(U) appears as `∑_{p ≤ ⌊U⌋} log p`. |
| (3) `eq:pivot` | conjunct for `18818 ≤ N` of the same theorem; proved by `OAI.SiegelZeros.WeightedTorusJets.global_source_rectangle_pivot_bounds` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Selection/GlobalRectanglePivotBounds.lean:13` | openai/math | Same constants (4·97², 192). The span hypothesis it needs is the departure from [SZ] described below. |
| M rows retained, Δ ≠ 0 (Section 2.1) | `OAI.SiegelZeros.WeightedTorusJets.jet_weight_ball_span_eq_top` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Selection/WeightedJetIndices.lean:464` | openai/math | Vandermonde argument; see below. |
| Lemma 4 (`lem:bias`) | `B4.explicit_split_mass` | `B4ExplicitBias.lean:65` | B4, on openai/math | Stated with two hypotheses `hzeta` (`-ζ'/ζ(s) ≤ 1/(s-1) + Z`) and `hgamma` (`½ Re ψ((s+ε)/2) ≤ ½ log π + G`), for any set of split primes `p ≤ X`. They are discharged with `Z = 2(s-1)e⁻¹/s`, `G = 0` by `B4.neg_logDeriv_zeta_le` (`B4Analytic.lean:292`) and `B4.gamma_term_le` (`B4Analytic.lean:52`, from `B4.gamma_logDeriv_re_le_log`, `B4Analytic.lean:22`, which uses Mathlib's `Real.convexOn_log_Gamma`); the combination is made inside `b4_elementary_zero_gap`. The formula for `-L'/L` is upstream: `OAI.SiegelZeros.WeightedTorusJets.W63.hadamardFormulaAt_of_actual_character` (`vendor/openai-math/OAI/NumberTheory/SiegelZeros/Characters/UnconditionalPrimeBias.lean:27`) and `OAI.SiegelZeros.WeightedTorusJets.W63.L_logDerivative_upper_of_hadamard` (`vendor/openai-math/OAI/NumberTheory/SiegelZeros/Characters/ConditionalPrimeBias.lean:123`); the Euler sum identity is `OAI.SiegelZeros.WeightedTorusJets.W05.real_eulerSum_eq_logDerivatives` (`vendor/openai-math/OAI/NumberTheory/SiegelZeros/Structure/RealBridge.lean:45`). |
| Lemma 5(a) | `B4.theta_le` | `B4PrimeMass.lean:160` | Mathlib | Wrapper of Mathlib's `Chebyshev.theta_le_log4_mul_x` (`.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:194`). |
| Lemma 5(b) | `B4.mertens_upper`; `B4.mass_le_of_le` | `B4PrimeMass.lean:34`; `B4PrimeMass.lean:82` | B4 | `mertens_upper` is for integers n ≥ 1; `mass_le_of_le` gives the bound `log y + log 4` for any set of primes `≤ y`, y ≥ 1 real. The step `A₋ − I ≤ log(4H)` of Proposition 6 is `B4.small_mass_le` (`B4PrimeMass.lean:98`). |
| Lemma 5(c) | `B4.total_mass_lower` | `B4PrimeMass.lean:166` | B4, on openai/math and PrimeNumberTheoremAnd | Stated with `κ_U = 1 + (5 log 2 + 3)/4 + 1/⌊U⌋`, U ≥ 1. Inputs: `OAI.SiegelZeros.Result.W54.sum_vonMangoldt_div_lower` (∑Λ(m)/m ≥ log n − 1; `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Characters/MangoldtMass.lean:43`), `Mertens.E₁.le` and `Mertens.E₁Λ.le_E₁p_add_E₁` (`vendor/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/IEANTN/Mertens.lean:743`, `:786`). |
| Lemma 5(d) | `B4.ramified_mass_le`; `B4.ramified_mass_le_log` | `B4PrimeMass.lean:116`; `B4PrimeMass.lean:155` | B4 (the bound by ℓ via upstream `OAI.SiegelZeros.W07.zero_value_mass_le_log`, `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Structure/RamifiedMass.lean:38`) | Stated for the primes `p ≤ n` with χ(p) = 0, i.e. `p ∣ q`; the minimum is taken in `b4_elementary_zero_gap`. |
| Proposition 6 (`prop:master`) | `OAI.SiegelZeros.WeightedTorusJets.b4_elementary_zero_gap` | `B4ElementaryGap.lean:27` | B4 | Same statement with B written `N`, `λ` written `L`, `ℓ = log q`, and `κ_U`, `r`, `log(4H)`, `ν`, `w` written out (`K`, `R`, `LH`, `ρ`, `W`); hypothesis `q ≠ 8`. It specializes `OAI.SiegelZeros.WeightedTorusJets.b4_explicit_zero_gap` (`B4ZeroGap.lean:28`), which takes the analytic inputs as hypotheses and combines (1)–(3) with the algebraic step `B4.master_algebra` (`B4MasterAlgebra.lean:27`; `1/(s−1) − 1/(s−β) ≤ (1−β)/(s−1)²` is `B4.reciprocal_gap_sq`, `B4MasterAlgebra.lean:18`). The partition of the prime mass is upstream `OAI.SiegelZeros.W07.prime_mass_partition` (`vendor/openai-math/OAI/NumberTheory/SiegelZeros/Characters/CharacterMaster.lean:50`). |
| Remark 7 | not formalized | — | — | Asymptotic and numerical comparison; not used in any proof. |
| Proof of Theorem 1: one interval | `B4.interval_gap`; `B4.core_gap`; `B4.certProp`; `B4.gapOn_of_cert` | `B4Interval.lean:198`; `B4Interval.lean:71`; `B4Interval.lean:28`; `B4Chain.lean:40` | B4 | Proposition 6 with `B = 2^k` (k ≥ 15), `H = 2^(3j)`, `y = 2^m` or `r ≤ ℓ`, and the monotonicity in ℓ. `certProp` is the closed inequality, in `log 2`, `exp(±η)`, `exp(−1)` and rationals, written without division. |
| Proof of Theorem 1: ℓ ≥ 10⁴ | `B4.tail_gap`; `B4.certTail` | `B4Chain.lean:61`; `B4Chain.lean:50` | B4 | k = ⌈τℓ⌉. |
| Proof of Theorem 1: joining | `B4.gapFrom_join`; `B4.Cert.chain_1`; `B4.Cert.log_three_ge` | `B4Chain.lean:33`; `B4Certificates.lean:3150`; `B4Certificates.lean:3153` | B4 | `chain_i : GapFrom (min of the constants from interval i on) l_i`; `log 3 ≥ 5493/5000 = 1.0986`. |
| Table 1 (`tab:TN`), zero gaps (c_N, T_N) | `B4.Cert.zero_gap_for_h100`, `_h200`, `_h500`, `_h1000`, `_h2000` | `B4Certificates.lean:3164`, `:3167`, `:3170`, `:3173`, `:3176` | B4 | `GapFrom c_N T_N` (q ≠ 8) with c_N = 2753/500000, 2811/500000, 5759/1000000, 5861/1000000, 1193/200000 and T_N = 286787/10000, 150729/5000, 160029/5000, 334757/10000, 350131/10000. |

## Section 3 (From the zero gap to class numbers)

| Paper | Lean | Location | Proof in | Remarks |
|---|---|---|---|---|
| Lemma 8 (`lem:L1`) | `B4.L1_elementary` | `B4L1.lean:211` | B4 | Hypotheses weaker than in the paper: χ is any nontrivial character mod q with real values and χ² = 1 (primitivity is not used; q is the modulus). Conclusion with `Re L(1, χ)`; X, Y natural numbers; `(Y+1)^(-1)` for `1/(Y+1)`. |
| Lemma 8, fact (i) | `B4.zeta_EM_real`; `B4.zeta_nonpos` | `B4ZetaEM.lean:128`; `B4ZetaEM.lean:101` | B4, on PrimeNumberTheoremAnd | The error is bounded by `4 t^(-σ)` (the paper notes this after the proof). Integral representation: `Zeta0EqZeta` (`vendor/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/ZetaBounds.lean:1393`), used in `B4.zeta_EM_nat` (`B4ZetaEM.lean:50`). |
| Lemma 8, fact (ii) | `B4.LFunction_sub_partial_le_q`; `B4.norm_psum_le` | `B4LSeriesCont.lean:351`; `B4LSeriesCont.lean:315` | B4 | `B4.LFunction_eq_contL` (`B4LSeriesCont.lean:191`) identifies Mathlib's `LFunction` with the series continued by partial summation on Re s > 0. |
| Lemma 8, fact (iii) | `B4.LFunction_nonneg_of_zero_free`; `B4.LFunction_im_eq_zero` | `B4Sign.lean:58`; `B4Sign.lean:20` | B4 | |
| Lemma 8, hyperbola identity and S ≥ 1 | `B4.hyperbola`; `B4.one_le_re_S` | `B4Hyperbola.lean:35`; `B4Hyperbola.lean:111` | B4 | The error terms: `B4.A_bound`, `B4.B_eq`, `B4.B_tail_bound` (`B4L1.lean:76`, `:138`, `:169`). |
| Proposition 9 (`prop:L1`) | `B4.h_bound_of_gap`; `B4.classP`; `B4.classEps` | `B4ClassBound.lean:64`; `B4ClassBound.lean:20`; `B4ClassBound.lean:23` | B4 | Assumes `GapFrom c T` (q ≠ 8) and concludes for q ≠ 8. It is combined with the final comparison: under the extra hypothesis `N π < (1−ε) c e^(−P) e^(T/2)/T` it concludes `N π < √q · Re L(1, χ)`, instead of stating `√q L(1, χ) ≥ (1−ε) c e^(−P) e^(T/2)/T`. `classP` is P, `classEps` is ε. |
| (4) `eq:cnf` | `B4.CNF.classNumber_ge`; `B4.CNF.classNumber_formula` | `B4ClassNumber.lean:168`; `B4ClassNumber.lean:152` | B4, on Mathlib, TauCeti, AINTLIB | For `K = ℚ(θ)`, θ² = d squarefree, with `|D| = (Dd d).natAbs` and `Lchi d hsf 1 = L(1, χ_D)`. `classNumber_formula` is `2π h = w √|D| L(1, χ_D)`. See "Class number formula" below. |
| Theorem 10 (`thm:lean`) | `B4.ClassNumber.classNumber_gt_100`, `_200`, `_500`, `_1000`, `_2000`; `B4.ClassNumber.classNumber_gt_of` | `B4ClassNumber.lean:232`, `:238`, `:244`, `:250`, `:256`; `B4ClassNumber.lean:190` | B4 | `K` is a number field with `IsTotallyComplex K` and `finrank ℚ K = 2`; hypothesis `T_N ≤ log |discr K|`; conclusion `N < classNumber K`. `classNumber_gt_of` derives q > 8 from T ≥ 3 and applies (4). |
| Proof of Theorem 10: numerical step | `B4.ClassCert.main_N`, `B4.ClassCert.eps_lt_N`, `B4.ClassCert.class_bound_hN` (N = 100, 200, 500, 1000, 2000) | `B4ClassCert.lean:67`/`64`/`79` (100), `:135`/`132`/`147` (200), `:203`/`200`/`215` (500), `:271`/`268`/`283` (1000), `:339`/`336`/`351` (2000) | B4 | A = 10⁶, V = 10⁴. `class_bound_hN` is `h_bound_of_gap` applied to `B4.Cert.zero_gap_for_hN`. |

### Class number formula

| Step | Lean | Location | Proof in |
|---|---|---|---|
| ζ_K(s) = ζ(s) L(s, χ_D), Re s > 1 | `B4.CNF.dedekindZeta_eq` | `B4QuadZeta.lean:253` | B4, on TauCeti and AINTLIB |
| ideal counts: `#{I : N(I) = n} = ∑_{m∣n} χ_D(m)` | `B4.CNF.multA_eq`; `B4.CNF.mult_prime_pow` | `B4QuadZeta.lean:242`; `B4QuadZeta.lean:124` | B4 (with `B4QuadSplit.lean`) |
| splitting of primes | `NumberField.ncard_primesOver_quadratic_iff`; `NumberField.ncard_primesOver_two_of_mod_four_eq_one` | `vendor/TauCeti/TauCeti/NumberTheory/NumberField/Quadratic/Splitting.lean:193`, `:265` | TauCeti |
| χ_D and disc K = D | `TauCeti.Multiquadratic.fundamentalDiscriminantChar`; `TauCeti.Multiquadratic.isPrimitive_fundamentalDiscriminantChar`; `TauCeti.Multiquadratic.discr_eq_fundamentalDiscriminant` | `vendor/TauCeti/TauCeti/NumberTheory/Multiquadratic/FundamentalDiscriminant/Character.lean:34`, `:87`; `vendor/TauCeti/TauCeti/NumberTheory/Multiquadratic/Quadratic/Discriminant.lean:50` | TauCeti |
| Euler product of ζ_K | `BernoulliRegular.dedekindZeta_eq_tsum_idealNormMultiplicity`; `BernoulliRegular.idealNormMultiplicity_mul` | `vendor/AINTLIB/BernoulliRegular/NumberFieldEulerProduct.lean:239`, `:47` | AINTLIB |
| Res_{s=1} ζ_K = L(1, χ_D) | `B4.CNF.residue_eq` | `B4ClassNumber.lean:83` | B4, on Mathlib (`riemannZeta_residue_one`, `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) |
| residue in terms of h, w, regulator | `NumberField.dedekindZeta_residue_def` | `.lake/packages/mathlib/Mathlib/NumberTheory/NumberField/DedekindZeta.lean:60` | Mathlib |

## Not formalized

| Paper | Where it is checked instead |
|---|---|
| Theorem 2 (`thm:main`, the list) | Theorem 10 (Lean) together with the computations of Sections 4 and 5 below; the count and the largest discriminant are read from the Mosunov–Jacobson tables. |
| Section 4 (Mosunov–Jacobson tables) | The tables of Mosunov and Jacobson, whose correctness is established in their paper; cross-checks against Cremona–Sutherland and HJKMP are described in Section 6. |
| Lemma 11 (`lem:minima`) | Proved in the paper (after Watkins); used by the sieve program `../qsieve/qsieve.c`. |
| (5) `eq:mu` | Proved in the paper; implemented in the sieve program. |
| Lemma 12 (`lem:certified`) | Proved in the paper; the tests (i)–(iv) are implemented in the sieve program, which is checked as described in `../qsieve/TESTING.md`. |
| Proposition 13 (`prop:sieve`) | The runs of the sieve program (logs in `../qsieve/logs/gap2000` and `../qsieve/logs/main2000`). |
| Remark 7 | Numerical comparison (`../computations/certify_c2.txt`, `../computations/certify_c2_lean.txt`); not used in any proof. |

(`../qsieve` and `../computations` are directories of the code repository, next to `lean/`.)

## The departure from [SZ] at the interpolation step

[SZ] proves the interpolation step by its Lemma 3 (a supporting face of a lattice polytope and Lagrange
interpolation) and Corollary 4. The upstream formalization does not formalize Lemma 3. It proves the
conclusion of Corollary 4 for the box used here, and our proof uses that conclusion only through the
pivot bounds (3).

| Role | Lean | Location |
|---|---|---|
| The rows R_α with `α₁ ≤ 32 H^(2/3) U`, `α₂, α₃ ≤ 32 H^(−1/3) U` span (U = N^(4/3), N = B) | `OAI.SiegelZeros.WeightedTorusJets.actual_biquadratic_rectangle_span` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Structure/InvariantJetLinearMap.lean:471` |
| Dual statement: a nonzero polynomial supported on `{0,…,N−1}^4` cannot vanish at (1,1,1,1) to these orders along the three invariant derivations (multiplicity estimate) | `OAI.SiegelZeros.WeightedTorusJets.Geometry.uniform_rectangular_multiplicity` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Differentials/TorusQuotientDimensionPosCotangentFinrankThree.lean:205` |
| Pivot bounds (3), from the span | `OAI.SiegelZeros.WeightedTorusJets.global_source_rectangle_pivot_bounds` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Selection/GlobalRectanglePivotBounds.lean:13` |
| M = B⁴ rows retained and Δ ≠ 0, without the above: the rows with α₂ = α₃ = 0, α₁ < M span (Vandermonde) | `OAI.SiegelZeros.WeightedTorusJets.jet_weight_ball_span_eq_top` | `vendor/openai-math/OAI/NumberTheory/SiegelZeros/Selection/WeightedJetIndices.lean:464` |

`actual_biquadratic_rectangle_span` is applied, and its result passed to
`global_source_rectangle_pivot_bounds`, in
`source_character_global_greedy_determinant_master_bounds`
(`vendor/openai-math/OAI/NumberTheory/SiegelZeros/Characters/CharacterGlobalGreedyDeterminantMasterBounds.lean:19`).
`jet_weight_ball_span_eq_top` is used in `source_character_global_greedy_determinant_divisibility`
(`vendor/openai-math/OAI/NumberTheory/SiegelZeros/Selection/RestrictWeightSortedEquiv.lean:367`).

## Numerical certificates

All numerical inequalities are proved by LeanCert with `leancert (trust := kernel)`, so that the Lean
kernel checks the evaluation. The two certificate files are generated; the generators play no role in
their correctness.

| Paper | File | Declarations | Generator |
|---|---|---|---|
| The 314 inequalities in the proof of Theorem 1 | `B4Certificates.lean` | `B4.Cert.cert_1` … `B4.Cert.cert_313` (`B4.certProp` on the 313 intervals of [1.0986, 10⁴]; `cert_1` at line 15, `cert_313` at line 2199) and `B4.Cert.cert_tail` (`B4.certTail` for ℓ ≥ 10⁴, line 2206); each `cert_i` gives `gap_i : GapOn` via `B4.gapOn_of_cert`, and `tail` (line 2209) via `B4.tail_gap`. The file also proves `B4.Cert.log_three_ge` (line 3153) by LeanCert. | `../computations/lean_grid.gp` (parameters and constants in `../computations/lean_grid.txt`) |
| `(1−ε) c_N e^(−P) e^(T_N/2)/T_N > Nπ` in the proof of Theorem 10 | `B4ClassCert.lean` | for each N: the atomic bounds `lg_N`, `lgat_N`, `u1_N`–`u6_N`, `l1_N`, `l2_N` (LeanCert), combined into `eps_N`, `eps_lt_N` (ε < 1) and `main_N` | `../computations/lean_h_cert.gp` (output `../computations/lean_h_cert.txt`) |
