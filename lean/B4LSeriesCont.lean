/-
B-4, Lemma L1 (elementary version), part 2 (2026-10-10): Mathlib's `LFunction χ` agrees on `Re s > 0`
with the continuation by partial summation, and for real `σ > 0` the partial sums converge to it with
an explicit tail bound
  ‖L(σ, χ) − ∑_{n ≤ N} χ(n) n^{-σ}‖ ≤ 2 M (N + 1)^{-σ},   M = sup_n ‖∑_{m ≤ n} χ(m)‖.
(Used in the proof of Lemma 8 of the paper.)
Method: for any `f : ℕ → ℂ` with bounded partial sums `B`, summation by parts gives
  ∑_{n ≤ N} f(n) n^{-s} = B(N) (N+1)^{-s} + ∑_{n ≤ N} B(n) (n^{-s} − (n+1)^{-s});
the series `G(s) = ∑ B(n) (n^{-s} − (n+1)^{-s})` is holomorphic on `Re s > 0` (mean value inequality
and locally uniform convergence), equals the L-series on `Re s > 1`, hence equals `LFunction χ` on
`Re s > 0` by the identity theorem.
Build: see README.md.
-/
import Mathlib

namespace B4

open Complex Filter Topology Finset

/-- `B n = ∑_{1 ≤ m ≤ n} f m` -/
def psum (f : ℕ → ℂ) (n : ℕ) : ℂ := ∑ m ∈ range n, f (m + 1)

/-- the terms of the continuation -/
noncomputable def gterm (f : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  psum f (n + 1) * (((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s))

/-- the continuation `G(s)` -/
noncomputable def contL (f : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n, gterm f s n

/-- Summation by parts. -/
theorem abel_sum (f : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    ∑ n ∈ range N, f (n + 1) * ((n : ℂ) + 1) ^ (-s) =
      psum f N * ((N : ℂ) + 1) ^ (-s) + ∑ n ∈ range N, gterm f s n := by
  induction N with
  | zero => simp [psum]
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [gterm, psum, sum_range_succ]
    push_cast
    ring_nf

/-- `‖(n+1)^{-s} − (n+2)^{-s}‖ ≤ ‖s‖ (n+1)^{-Re s - 1}` (mean value inequality). -/
theorem norm_cpow_sub_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    ‖((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)‖ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by positivity
  set g : ℝ → ℂ := fun u => ((u : ℂ)) ^ (-s)
  have hderiv : ∀ u ∈ Set.Icc a (a + 1),
      HasDerivWithinAt g (-s * ((u : ℂ)) ^ (-s - 1)) (Set.Icc a (a + 1)) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    have h := (Complex.hasStrictDerivAt_cpow_const (c := -s)
      (ofReal_mem_slitPlane.mpr hu0)).hasDerivAt.comp_ofReal
    exact h.hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Ico a (a + 1), ‖-s * ((u : ℂ)) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ha0 hu.1
    rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu0]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    simp only [sub_re, neg_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos ha0 hu.1 (by linarith)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound (a + 1)
    ⟨by linarith, le_rfl⟩
  have e1 : g (a + 1) = ((n : ℂ) + 2) ^ (-s) := by
    simp only [g, ha]; push_cast; ring_nf
  have e2 : g a = ((n : ℂ) + 1) ^ (-s) := by simp only [g, ha]; push_cast; ring_nf
  rw [e1, e2, norm_sub_rev] at h
  simpa using h

/-- `G` is holomorphic on `Re s > 0` when the partial sums are bounded. -/
theorem differentiableOn_contL (f : ℕ → ℂ) (M : ℝ) (hM : ∀ n, ‖psum f n‖ ≤ M) :
    DifferentiableOn ℂ (contL f) {s | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀ : 0 < s₀.re := hs₀
  set ε := s₀.re / 2
  set R := ‖s₀‖ + 1
  set U := {s : ℂ | ε < s.re} ∩ Metric.ball (0 : ℂ) R
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := ⟨by show ε < s₀.re; simp only [ε]; linarith,
    by simp [R, Metric.mem_ball]⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hε : 0 < ε := by simp only [ε]; linarith
  have hd : DifferentiableOn ℂ (contL f) U := by
    apply differentiableOn_tsum_of_summable_norm
      (u := fun n : ℕ => M * R * ((n : ℝ) + 1) ^ (-ε - 1))
    · apply Summable.mul_left
      have := (Real.summable_nat_rpow (p := -ε - 1)).mpr (by linarith)
      exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring_nf
    · intro n
      apply DifferentiableOn.const_mul
      apply DifferentiableOn.sub
      · intro s _
        exact (DifferentiableAt.const_cpow (differentiableAt_id.neg)
          (Or.inl (Nat.cast_add_one_ne_zero n))).differentiableWithinAt
      · intro s _
        exact (DifferentiableAt.const_cpow (differentiableAt_id.neg)
          (Or.inl (by exact_mod_cast (show n + 2 ≠ 0 by omega)))).differentiableWithinAt
    · exact hU
    · intro n s hs
      obtain ⟨hsε, hsR⟩ := hs
      have hsε : ε < s.re := hsε
      have hsR : ‖s‖ < R := by simpa [Metric.mem_ball] using hsR
      have hspos : 0 < s.re := by linarith
      simp only [gterm, norm_mul]
      have h1 := norm_cpow_sub_le s hspos n
      have h2 : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-ε - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
          (by linarith)
      calc ‖psum f (n + 1)‖ * ‖((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)‖
          ≤ M * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
            mul_le_mul (hM _) h1 (norm_nonneg _) hM0
        _ ≤ M * (R * ((n : ℝ) + 1) ^ (-ε - 1)) := by
            apply mul_le_mul_of_nonneg_left _ hM0
            exact mul_le_mul hsR.le h2 (by positivity) (by positivity)
        _ = _ := by ring
  exact ((hd s₀ hs₀U).differentiableAt (hU.mem_nhds hs₀U)).differentiableWithinAt

#print axioms differentiableOn_contL

/-- the terms of `G` are dominated by `M ‖s‖ (n+1)^{-Re s - 1}` -/
theorem norm_gterm_le (f : ℕ → ℂ) (M : ℝ) (hM : ∀ n, ‖psum f n‖ ≤ M) (s : ℂ) (hs : 0 < s.re)
    (n : ℕ) : ‖gterm f s n‖ ≤ M * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  simp only [gterm, norm_mul]
  calc ‖psum f (n + 1)‖ * ‖((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)‖
      ≤ M * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
        mul_le_mul (hM _) (norm_cpow_sub_le s hs n) (norm_nonneg _) hM0
    _ = _ := by ring

theorem summable_gterm (f : ℕ → ℂ) (M : ℝ) (hM : ∀ n, ‖psum f n‖ ≤ M) (s : ℂ) (hs : 0 < s.re) :
    Summable (gterm f s) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => M * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1))
  · apply Summable.mul_left
    have := (Real.summable_nat_rpow (p := -s.re - 1)).mpr (by linarith)
    exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring_nf
  · exact norm_gterm_le f M hM s hs

/-- the partial sums of the L-series tend to `G(s)` for `Re s > 0` -/
theorem tendsto_partial_contL (f : ℕ → ℂ) (M : ℝ) (hM : ∀ n, ‖psum f n‖ ≤ M) (s : ℂ)
    (hs : 0 < s.re) :
    Tendsto (fun N => ∑ n ∈ range N, f (n + 1) * ((n : ℂ) + 1) ^ (-s)) atTop (𝓝 (contL f s)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  simp_rw [abel_sum]
  rw [show contL f s = 0 + contL f s by ring]
  apply Tendsto.add
  · -- ‖B(N) (N+1)^{-s}‖ ≤ M (N+1)^{-Re s} → 0
    apply squeeze_zero_norm (a := fun N : ℕ => M * ((N : ℝ) + 1) ^ (-s.re))
    · intro N
      rw [norm_mul]
      have : ‖((N : ℂ) + 1) ^ (-s)‖ = ((N : ℝ) + 1) ^ (-s.re) := by
        have h := norm_natCast_cpow_of_pos (n := N + 1) (by omega) (-s)
        push_cast at h; simpa using h
      rw [this]
      exact mul_le_mul_of_nonneg_right (hM N) (by positivity)
    · rw [show (0 : ℝ) = M * 0 by ring]
      apply Tendsto.const_mul
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      exact (tendsto_rpow_neg_atTop hs).comp h1
  · exact (summable_gterm f M hM s hs).hasSum.tendsto_sum_nat

/-- `G(s)` is the L-series for `Re s > 1` (for `f` with bounded partial sums). -/
theorem contL_eq_LSeries (f : ℕ → ℂ) (M : ℝ) (hM : ∀ n, ‖psum f n‖ ≤ M) (s : ℂ) (hs : 1 < s.re) :
    contL f s = LSeries f s := by
  have hs0 : 0 < s.re := by linarith
  -- f is bounded by 2M
  have hf : ∀ n, ‖f (n + 1)‖ ≤ 2 * M := by
    intro n
    have : f (n + 1) = psum f (n + 1) - psum f n := by simp [psum, sum_range_succ]
    rw [this]
    calc ‖psum f (n + 1) - psum f n‖ ≤ ‖psum f (n + 1)‖ + ‖psum f n‖ := norm_sub_le _ _
      _ ≤ 2 * M := by linarith [hM (n + 1), hM n]
  have hsum : LSeriesSummable f s := by
    apply LSeriesSummable_of_le_const_mul_rpow (x := 1) hs
    refine ⟨2 * M, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa using hf m
  have hhas : HasSum (fun n => LSeries.term f s (n + 1)) (LSeries f s) := by
    have h := (hasSum_nat_add_iff' 1).mpr hsum.LSeriesHasSum
    simpa using h
  have hlim := hhas.tendsto_sum_nat
  have hterm : ∀ n : ℕ, LSeries.term f s (n + 1) = f (n + 1) * ((n : ℂ) + 1) ^ (-s) := by
    intro n
    rw [LSeries.term_of_ne_zero (by omega), cpow_neg, div_eq_mul_inv]
    push_cast; rfl
  simp_rw [hterm] at hlim
  exact tendsto_nhds_unique (tendsto_partial_contL f M hM s hs0) hlim

/-- **Part 2.** For a nontrivial Dirichlet character, `LFunction χ = G` on `Re s > 0`. -/
theorem LFunction_eq_contL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℝ) (hM : ∀ n, ‖psum (fun n => χ n) n‖ ≤ M) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = contL (fun n => χ n) s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (contL (fun n => χ n)) {s : ℂ | 0 < s.re} :=
    (differentiableOn_contL _ M hM).analyticOnNhd hU
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] contL (fun n => χ n) := by
    have hV : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hV.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz, contL_eq_LSeries _ M hM z hz]
  exact h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (show (0 : ℝ) < (2 : ℂ).re by norm_num) hev hs

/-- **Tail bound.** For real `σ > 0`:
`‖L(σ, χ) − ∑_{n ≤ N} χ(n) n^{-σ}‖ ≤ 2 M (N+1)^{-σ}`. -/
theorem LFunction_sub_partial_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℝ) (hM : ∀ n, ‖psum (fun n => χ n) n‖ ≤ M) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    ‖DirichletCharacter.LFunction χ σ -
        ∑ n ∈ range N, χ ((n + 1 : ℕ) : ZMod q) * ((n : ℂ) + 1) ^ (-(σ : ℂ))‖
      ≤ 2 * M * ((N : ℝ) + 1) ^ (-σ) := by
  set f : ℕ → ℂ := fun n => χ n
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  rw [LFunction_eq_contL χ hχ M hM hs]
  have habel := abel_sum f σ N
  simp only [f] at habel
  rw [habel]
  have hsum := summable_gterm f M hM σ hs
  rw [contL, ← hsum.sum_add_tsum_nat_add N]
  -- remaining: ∑' gterm (n+N) − B(N)(N+1)^{-σ}
  set a : ℕ → ℝ := fun k => ((k : ℝ) + 1) ^ (-σ)
  have hcpow : ∀ k : ℕ, ((k : ℂ) + 1) ^ (-(σ : ℂ)) = ((a k : ℝ) : ℂ) := by
    intro k
    simp only [a]
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  have hcpow2 : ∀ k : ℕ, ((k : ℂ) + 2) ^ (-(σ : ℂ)) = ((a (k + 1) : ℝ) : ℂ) := by
    intro k
    simp only [a]
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  have ha_anti : ∀ k, a (k + 1) ≤ a k := by
    intro k
    simp only [a]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  have hg : ∀ n, ‖gterm f σ (n + N)‖ ≤ M * (a (n + N) - a (n + N + 1)) := by
    intro n
    simp only [gterm, norm_mul]
    rw [hcpow, hcpow2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [ha_anti (n + N)])]
    exact mul_le_mul_of_nonneg_right (hM _) (by linarith [ha_anti (n + N)])
  have htail : ‖∑' n, gterm f σ (n + N)‖ ≤ M * a N := by
    refine (norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hsum).norm).trans ?_
    apply Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    intro K
    calc ∑ n ∈ range K, ‖gterm f σ (n + N)‖ ≤ ∑ n ∈ range K, M * (a (n + N) - a (n + N + 1)) :=
          sum_le_sum fun n _ => hg n
      _ = M * (a N - a (K + N)) := by
          rw [← mul_sum]
          congr 1
          have := sum_range_sub' (fun n => a (n + N)) K
          simp only [zero_add] at this
          rw [← this]
          refine sum_congr rfl fun n _ => ?_
          ring_nf
      _ ≤ M * a N := by
          apply mul_le_mul_of_nonneg_left _ hM0
          have : 0 ≤ a (K + N) := by simp only [a]; positivity
          linarith
  have hB : ‖psum f N * ((N : ℂ) + 1) ^ (-(σ : ℂ))‖ ≤ M * a N := by
    rw [norm_mul, hcpow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simp only [a]; positivity)]
    exact mul_le_mul_of_nonneg_right (hM N) (by simp only [a]; positivity)
  calc ‖(∑ i ∈ range N, gterm f σ i + ∑' n, gterm f σ (n + N)) -
        (psum f N * ((N : ℂ) + 1) ^ (-(σ : ℂ)) + ∑ n ∈ range N, gterm f σ n)‖
      = ‖∑' n, gterm f σ (n + N) - psum f N * ((N : ℂ) + 1) ^ (-(σ : ℂ))‖ := by
        congr 1; ring
    _ ≤ ‖∑' n, gterm f σ (n + N)‖ + ‖psum f N * ((N : ℂ) + 1) ^ (-(σ : ℂ))‖ := norm_sub_le _ _
    _ ≤ M * a N + M * a N := add_le_add htail hB
    _ = 2 * M * ((N : ℝ) + 1) ^ (-σ) := by simp only [a]; ring

#print axioms LFunction_eq_contL
#print axioms LFunction_sub_partial_le

/-! ### The character-sum bound `‖∑_{m ≤ n} χ(m)‖ ≤ q/2` -/

theorem sum_range_zmod {q : ℕ} [NeZero q] (g : ZMod q → ℂ) :
    ∑ m ∈ range q, g (m : ZMod q) = ∑ a : ZMod q, g a := by
  apply Finset.sum_nbij' (i := fun m : ℕ => (m : ZMod q)) (j := fun a : ZMod q => a.val)
  · intro m _; simp
  · intro a _; simp [ZMod.val_lt]
  · intro m hm
    simp only [mem_range] at hm
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt hm]
  · intro a _; simp
  · intro m _; rfl

theorem sum_period_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ m ∈ range q, χ ((n + m + 1 : ℕ) : ZMod q) = 0 := by
  have h := sum_range_zmod (q := q) (fun a => χ (((n + 1 : ℕ) : ZMod q) + a))
  have e : ∀ m : ℕ, χ ((n + m + 1 : ℕ) : ZMod q) = χ (((n + 1 : ℕ) : ZMod q) + (m : ZMod q)) := by
    intro m; congr 1; push_cast; ring
  simp_rw [e]
  rw [h, Fintype.sum_equiv (Equiv.addLeft (((n + 1 : ℕ) : ZMod q)))
    (fun a => χ (((n + 1 : ℕ) : ZMod q) + a)) (fun a => χ a) (fun _ => rfl)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

theorem psum_add_q {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    psum (fun n => χ n) (n + q) = psum (fun n => χ n) n := by
  simp only [psum]
  rw [sum_range_add]
  have := sum_period_eq_zero χ hχ n
  simp only [add_assoc] at this ⊢
  rw [this, add_zero]

theorem psum_mod {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    psum (fun n => χ n) n = psum (fun n => χ n) (n % q) := by
  conv_lhs => rw [← Nat.mod_add_div n q]
  induction n / q with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, psum_add_q χ hχ, ih]

/-- `‖∑_{1 ≤ m ≤ n} χ(m)‖ ≤ q/2` for a nontrivial character mod `q`. -/
theorem norm_psum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖psum (fun n => χ n) n‖ ≤ (q : ℝ) / 2 := by
  rw [psum_mod χ hχ n]
  set r := n % q
  have hr : r < q := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))
  -- ≤ r
  have h1 : ‖psum (fun n => χ n) r‖ ≤ r := by
    simp only [psum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m ∈ range r, ‖χ ((m + 1 : ℕ) : ZMod q)‖ ≤ ∑ m ∈ range r, (1 : ℝ) :=
          sum_le_sum fun m _ => DirichletCharacter.norm_le_one χ _
      _ = r := by simp
  -- ≤ q − r, since the sum over a full period vanishes
  have h2 : ‖psum (fun n => χ n) r‖ ≤ (q : ℝ) - r := by
    have hq0 : psum (fun n => χ n) q = 0 := by
      have := psum_add_q χ hχ 0
      simpa [psum] using this
    have hsplit : psum (fun n => χ n) q = psum (fun n => χ n) r +
        ∑ m ∈ range (q - r), χ ((r + m + 1 : ℕ) : ZMod q) := by
      simp only [psum]
      rw [← sum_range_add, Nat.add_sub_cancel' hr.le]
    have : psum (fun n => χ n) r = -∑ m ∈ range (q - r), χ ((r + m + 1 : ℕ) : ZMod q) := by
      rw [hq0] at hsplit; linear_combination -hsplit
    rw [this, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ m ∈ range (q - r), ‖χ ((r + m + 1 : ℕ) : ZMod q)‖ ≤ ∑ m ∈ range (q - r), (1 : ℝ) :=
          sum_le_sum fun m _ => DirichletCharacter.norm_le_one χ _
      _ = (q : ℝ) - r := by simp [Nat.cast_sub hr.le]
  have : (min (r : ℝ) ((q : ℝ) - r)) ≤ (q : ℝ) / 2 := by
    rcases le_total (r : ℝ) ((q : ℝ) - r) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  exact (le_min h1 h2).trans this

/-- **Part 2, final form**, with `M = q/2`: for real `σ > 0`,
`‖L(σ, χ) − ∑_{n ≤ N} χ(n) n^{-σ}‖ ≤ q (N+1)^{-σ}`. -/
theorem LFunction_sub_partial_le_q {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    ‖DirichletCharacter.LFunction χ σ -
        ∑ n ∈ range N, χ ((n + 1 : ℕ) : ZMod q) * ((n : ℂ) + 1) ^ (-(σ : ℂ))‖
      ≤ q * ((N : ℝ) + 1) ^ (-σ) := by
  have h := LFunction_sub_partial_le χ hχ ((q : ℝ) / 2) (norm_psum_le χ hχ) hσ N
  calc _ ≤ 2 * ((q : ℝ) / 2) * ((N : ℝ) + 1) ^ (-σ) := h
    _ = _ := by ring

#print axioms LFunction_sub_partial_le_q

end B4
