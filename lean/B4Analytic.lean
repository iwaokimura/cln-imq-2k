/-
B-4 (ii), part 2 (2026-10-09): the analytic hypotheses `hzeta` and `hgamma` of
`b4_explicit_zero_gap`, with explicit constants.
  * `gamma_logDeriv_re_le_log`: ψ(x) ≤ log x for x > 0 (log Γ is convex, and the slope of log Γ on
    [x, x+1] is log x). Hence the Gamma term is ≤ ½ log π, i.e. G = 0, as long as (s+1)/2 ≤ π.
  * `neg_logDeriv_zeta_le`: -ζ'/ζ(s) ≤ 1/(s-1) + 2(s-1)/(e s) for real s > 1.
    -ζ'(s) = ∑ log n · n^{-s}: the terms n = 2, 3 are ≤ max (log x · x^{-s}) = 1/(e s), and for n ≥ 4
    the function is decreasing, so the rest is ≤ ∫_3^∞ ≤ 1/(s-1)²; and ζ(s) ≥ ∫_1^∞ x^{-s} = 1/(s-1).
    (This is the bound in the proof of Lemma 4 of the paper; the factor 2 costs nothing visible,
    since s - 1 = η/log U is small.)
Build: see README.md.
-/
import Mathlib
import OAI.NumberTheory.SiegelZeros.EntireFunctions.GammaBound

namespace B4

open Real Set Filter Topology OAI.SiegelZeros

/-! ### The Gamma term -/

theorem gamma_logDeriv_re_le_log {x : ℝ} (hx : 0 < x) :
    (SiegelZerosAwei.W52.gammaLogDerivative (x : ℂ)).re ≤ Real.log x := by
  have hd : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  set g' := deriv Complex.Gamma (x : ℂ)
  have hr : HasDerivAt Real.Gamma g'.re x := by
    have h := hd.hasDerivAt.real_of_complex
    have hfun : (fun r : ℝ => (Complex.Gamma (r : ℂ)).re) = Real.Gamma := by
      funext r; rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rwa [hfun] at h
  have hG : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hlog : HasDerivAt (Real.log ∘ Real.Gamma) (g'.re / Real.Gamma x) x := hr.log hG.ne'
  have hslope := Real.convexOn_log_Gamma.le_slope_of_hasDerivAt (x := x) (y := x + 1)
    hx (show (0 : ℝ) < x + 1 by linarith) (by linarith) hlog
  rw [slope_def_field] at hslope
  simp only [Function.comp, Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' hG.ne'] at hslope
  have hre : (SiegelZerosAwei.W52.gammaLogDerivative (x : ℂ)).re = g'.re / Real.Gamma x := by
    simp only [SiegelZerosAwei.W52.gammaLogDerivative, Complex.Gamma_ofReal]
    rw [Complex.div_ofReal_re]
  rw [hre]
  have : x + 1 - x = 1 := by ring
  rw [this, div_one] at hslope
  linarith

/-- (hgamma) with `G = 0`, for `0 < s` and `s + 1 ≤ 2π`, any parity `a ∈ {0, 1}`. -/
theorem gamma_term_le {s a : ℝ} (hs : 0 < s) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hsπ : s + 1 ≤ 2 * π) :
    (1 / 2 : ℝ) * (SiegelZerosAwei.W52.gammaLogDerivative (((s + a) / 2 : ℝ) : ℂ)).re ≤
      (1 / 2 : ℝ) * Real.log π + 0 := by
  have hx : 0 < (s + a) / 2 := by linarith
  have h := gamma_logDeriv_re_le_log hx
  have h2 : Real.log ((s + a) / 2) ≤ Real.log π := Real.log_le_log hx (by linarith)
  linarith

/-! ### The zeta term -/

/-- `log x · x^{-s} ≤ 1/(e s)` for `x > 0`, `s > 0`. -/
theorem log_mul_rpow_neg_le {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    Real.log x * x ^ (-s) ≤ Real.exp (-1) / s := by
  set t := s * Real.log x
  have hxs : x ^ (-s) = Real.exp (-t) := by
    rw [Real.rpow_def_of_pos hx]; congr 1; simp only [t]; ring
  have hte : t ≤ Real.exp (t - 1) := by linarith [Real.add_one_le_exp (t - 1)]
  have hkey : t * Real.exp (-t) ≤ Real.exp (-1) := by
    have h1 : Real.exp (t - 1) * Real.exp (-t) = Real.exp (-1) := by
      rw [← Real.exp_add]; ring_nf
    calc t * Real.exp (-t) ≤ Real.exp (t - 1) * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right hte (Real.exp_pos _).le
      _ = _ := h1
  rw [hxs, le_div_iff₀ hs]
  calc Real.log x * Real.exp (-t) * s = t * Real.exp (-t) := by simp only [t]; ring
    _ ≤ _ := hkey

/-- derivative of `log x · x^{-s}` -/
theorem hasDerivAt_log_mul_rpow {x s : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => Real.log y * y ^ (-s))
      (x⁻¹ * x ^ (-s) + Real.log x * (-s * x ^ (-s - 1))) x := by
  have h1 := Real.hasDerivAt_log hx.ne'
  have h2 := Real.hasDerivAt_rpow_const (x := x) (p := -s) (Or.inl hx.ne')
  exact h1.mul h2

theorem one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

theorem antitoneOn_log_mul_rpow {s : ℝ} (hs : 1 ≤ s) :
    AntitoneOn (fun y => Real.log y * y ^ (-s)) (Ici 3) := by
  have hcont : ContinuousOn (fun y => Real.log y * y ^ (-s)) (Ici 3) := fun x hx =>
    (hasDerivAt_log_mul_rpow (s := s) (show (0 : ℝ) < x by
      have : (3 : ℝ) ≤ x := hx; linarith)).continuousAt.continuousWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 3) hcont
    (f' := fun x => x⁻¹ * x ^ (-s) + Real.log x * (-s * x ^ (-s - 1)))
  · intro x hx
    rw [interior_Ici] at hx
    have : (0 : ℝ) < x := by have : (3 : ℝ) < x := hx; linarith
    exact (hasDerivAt_log_mul_rpow this).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx3 : (3 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have hpow : x ^ (-s - 1) = x ^ (-s) * x⁻¹ := by
      rw [Real.rpow_sub_one hx0.ne', div_eq_mul_inv]
    have hlog : 1 < Real.log x :=
      lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hx3.le)
    have hp : 0 < x ^ (-s) * x⁻¹ := by positivity
    rw [hpow]
    have : x⁻¹ * x ^ (-s) + Real.log x * (-s * (x ^ (-s) * x⁻¹)) =
        (x ^ (-s) * x⁻¹) * (1 - s * Real.log x) := by ring
    rw [this]
    apply mul_nonpos_of_nonneg_of_nonpos hp.le
    nlinarith

/-- `∫_3^b log x · x^{-s} ≤ 1/(s-1)²` -/
theorem integral_log_mul_rpow_le {s b : ℝ} (hs : 1 < s) (hb : 3 ≤ b) :
    ∫ x in (3 : ℝ)..b, Real.log x * x ^ (-s) ≤ 1 / (s - 1) ^ 2 := by
  have hs1 : 0 < s - 1 := by linarith
  set F : ℝ → ℝ := fun x => -(x ^ (1 - s) * (Real.log x / (s - 1) + 1 / (s - 1) ^ 2))
  have hF : ∀ x ∈ uIcc (3 : ℝ) b, HasDerivAt F (Real.log x * x ^ (-s)) x := by
    intro x hx
    rw [uIcc_of_le hb] at hx
    have hx0 : 0 < x := by linarith [hx.1]
    have ha := Real.hasDerivAt_rpow_const (x := x) (p := 1 - s) (Or.inl hx0.ne')
    have hl := ((Real.hasDerivAt_log hx0.ne').div_const (s - 1)).add_const (1 / (s - 1) ^ 2)
    have h := (ha.mul hl).neg
    convert h using 1
    have hsub : (1 - s - 1) = -s := by ring
    rw [hsub]
    have hx1 : x ^ (1 - s) = x * x ^ (-s) := by
      rw [show (1 - s) = 1 + -s by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [hx1]
    field_simp
    ring
  have hint : IntervalIntegrable (fun x => Real.log x * x ^ (-s)) MeasureTheory.volume 3 b := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hb]
    exact (antitoneOn_log_mul_rpow hs.le).mono (Icc_subset_Ici_self)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  -- F b ≤ 0 and -F 3 ≤ 1/(s-1)²
  have hb0 : 0 < b := by linarith
  have hFb : F b ≤ 0 := by
    simp only [F, neg_nonpos]
    apply mul_nonneg (Real.rpow_nonneg hb0.le _)
    have : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    positivity
  have hF3 : -F 3 ≤ 1 / (s - 1) ^ 2 := by
    simp only [F, neg_neg]
    set u := (s - 1) * Real.log 3
    have h3 : (3 : ℝ) ^ (1 - s) = Real.exp (-u) := by
      rw [Real.rpow_def_of_pos (by norm_num)]; congr 1; simp only [u]; ring
    have hu : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have heu : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    rw [h3]
    have hexp : 0 < Real.exp (-u) := Real.exp_pos _
    have : Real.exp (-u) * (Real.log 3 / (s - 1) + 1 / (s - 1) ^ 2) =
        Real.exp (-u) * (1 + u) / (s - 1) ^ 2 := by
      simp only [u]; field_simp; ring
    rw [this, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  linarith

/-- the real coefficient sequences -/
noncomputable def aA (s : ℝ) (n : ℕ) : ℝ := Real.log n * (n : ℝ) ^ (-s)
noncomputable def aZ (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-s)

theorem aA_nonneg (s : ℝ) (n : ℕ) : 0 ≤ aA s n :=
  mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem tsum_aA_le {s : ℝ} (hs : 1 < s) :
    ∑' n, aA s n ≤ 2 * (Real.exp (-1) / s) + 1 / (s - 1) ^ 2 := by
  have hs0 : 0 < s := by linarith
  apply Real.tsum_le_of_sum_range_le (aA_nonneg s)
  intro N
  have hmono : ∑ i ∈ Finset.range N, aA s i ≤ ∑ i ∈ Finset.range (4 + N), aA s i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun i _ _ => aA_nonneg s i)
  refine le_trans hmono ?_
  rw [Finset.sum_range_add]
  have h4 : ∑ i ∈ Finset.range 4, aA s i ≤ 2 * (Real.exp (-1) / s) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, aA, Nat.cast_zero, Nat.cast_one,
      Real.log_zero, Real.log_one, zero_mul, zero_add]
    have h2 := log_mul_rpow_neg_le (x := ((2 : ℕ) : ℝ)) (by norm_num) hs0
    have h3 := log_mul_rpow_neg_le (x := ((3 : ℕ) : ℝ)) (by norm_num) hs0
    push_cast at h2 h3 ⊢
    linarith
  have htail : ∑ i ∈ Finset.range N, aA s (4 + i) ≤ 1 / (s - 1) ^ 2 := by
    have h := AntitoneOn.sum_le_integral (x₀ := 3) (a := N)
      (f := fun y => Real.log y * y ^ (-s))
      ((antitoneOn_log_mul_rpow hs.le).mono (Icc_subset_Ici_self))
    have heq : ∑ i ∈ Finset.range N, aA s (4 + i) =
        ∑ i ∈ Finset.range N, (fun y => Real.log y * y ^ (-s)) (3 + ((i + 1 : ℕ) : ℝ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [aA]; push_cast; ring_nf
    rw [heq]
    exact h.trans (integral_log_mul_rpow_le hs (by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith))
  linarith

theorem summable_aZ {s : ℝ} (hs : 1 < s) : Summable (aZ s) :=
  Real.summable_nat_rpow.mpr (by linarith)

theorem tsum_aZ_ge {s : ℝ} (hs : 1 < s) : 1 / (s - 1) ≤ ∑' n, aZ s n := by
  have hs1 : 0 < s - 1 := by linarith
  have hanti : AntitoneOn (fun y : ℝ => y ^ (-s)) (Ici 1) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by have : (1 : ℝ) ≤ x := hx; linarith) hxy (by linarith)
  -- ∫_1^{1+a} x^{-s} = (1 - (1+a)^{1-s})/(s-1) ≤ ∑' aZ
  have hbound : ∀ a : ℕ, (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1) ≤ ∑' n, aZ s n := by
    intro a
    have hint := AntitoneOn.integral_le_sum (x₀ := 1) (a := a) (f := fun y : ℝ => y ^ (-s))
      (hanti.mono Icc_subset_Ici_self)
    have hcalc : ∫ x in (1 : ℝ)..1 + a, x ^ (-s) = (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1) := by
      have hF : ∀ x ∈ uIcc (1 : ℝ) (1 + a), HasDerivAt (fun y : ℝ => y ^ (1 - s) / (1 - s))
          (x ^ (-s)) x := by
        intro x hx
        rw [uIcc_of_le (by have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)] at hx
        have hx0 : 0 < x := by linarith [hx.1]
        have h := (Real.hasDerivAt_rpow_const (x := x) (p := 1 - s) (Or.inl hx0.ne')).div_const
          (1 - s)
        convert h using 1
        rw [show (1 - s - 1) = -s by ring]
        field_simp [show (1 - s) ≠ 0 by linarith]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        ((hanti.mono (by
          rw [uIcc_of_le (by have : (0 : ℝ) ≤ a := Nat.cast_nonneg a; linarith)]
          exact Icc_subset_Ici_self)).intervalIntegrable)]
      rw [Real.one_rpow]
      field_simp [show (1 - s) ≠ 0 by linarith, show (s - 1) ≠ 0 by linarith]
      ring
    have hsum : ∑ i ∈ Finset.range a, (fun y : ℝ => y ^ (-s)) (1 + (i : ℝ)) ≤ ∑' n, aZ s n := by
      calc ∑ i ∈ Finset.range a, (fun y : ℝ => y ^ (-s)) (1 + (i : ℝ))
          = ∑ i ∈ Finset.range a, aZ s (i + 1) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [aZ]; push_cast; ring_nf
        _ ≤ ∑ i ∈ Finset.range (a + 1), aZ s i := by
            rw [Finset.sum_range_succ']
            have : 0 ≤ aZ s 0 := Real.rpow_nonneg (Nat.cast_nonneg 0) _
            linarith
        _ ≤ ∑' n, aZ s n := (summable_aZ hs).sum_le_tsum _
            (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
    rw [← hcalc]
    exact hint.trans hsum
  have hlim : Tendsto (fun a : ℕ => (1 - (1 + (a : ℝ)) ^ (1 - s)) / (s - 1)) atTop
      (𝓝 ((1 - 0) / (s - 1))) := by
    have h1 : Tendsto (fun a : ℕ => (1 + (a : ℝ))) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun a : ℕ => (1 + (a : ℝ)) ^ (1 - s)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hs1).comp h1
      refine this.congr fun a => ?_
      simp only [Function.comp, neg_sub]
    exact (tendsto_const_nhds.sub h2).div_const _
  rw [sub_zero] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall hbound)

/-- `-ζ'/ζ(s)` for real `s > 1` as a ratio of the two real series. -/
theorem neg_logDeriv_zeta_eq {s : ℝ} (hs : 1 < s) :
    -deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ) = ((∑' n, aA s n) / (∑' n, aZ s n) : ℝ) := by
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hs
  have hderiv : deriv riemannZeta (s : ℂ) = deriv (LSeries 1) (s : ℂ) := by
    refine (Filter.EventuallyEq.deriv_eq ?_).symm
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z | 1 < z.re},
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs', fun z hz => ?_⟩
    exact LSeries_one_eq_riemannZeta hz
  rw [hderiv, LSeries_deriv habs, ← LSeries_one_eq_riemannZeta hs', neg_neg]
  have hZ : LSeries 1 (s : ℂ) = ((∑' n, aZ s n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [aZ, Real.zero_rpow (show -s ≠ 0 by linarith)]
    rw [LSeries.term_of_ne_zero hn, aZ, Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    rw [Complex.cpow_neg, Pi.one_apply, one_div]
  have hA : LSeries (LSeries.logMul 1) (s : ℂ) = ((∑' n, aA s n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [aA]
    rw [LSeries.term_of_ne_zero hn, aA, LSeries.logMul, Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_log (Nat.cast_nonneg n)]
    push_cast
    rw [Complex.cpow_neg, Pi.one_apply, mul_one, div_eq_mul_inv]
  rw [hZ, hA, Complex.ofReal_div]

/-- (hzeta) with `Z = 2(s-1)/(e s)`. -/
theorem neg_logDeriv_zeta_le {s : ℝ} (hs : 1 < s) :
    (-deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re ≤
      1 / (s - 1) + 2 * (s - 1) * Real.exp (-1) / s := by
  rw [neg_logDeriv_zeta_eq hs, Complex.ofReal_re]
  have hs1 : 0 < s - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hZ := tsum_aZ_ge hs
  have hA := tsum_aA_le hs
  have hA0 : 0 ≤ ∑' n, aA s n := tsum_nonneg (aA_nonneg s)
  have hZpos : 0 < ∑' n, aZ s n := lt_of_lt_of_le (by positivity) hZ
  rw [div_le_iff₀ hZpos]
  -- A ≤ (1/(s-1) + 2(s-1)e^{-1}/s) · (1/(s-1)) ≤ RHS · Z
  have hR0 : 0 ≤ 1 / (s - 1) + 2 * (s - 1) * Real.exp (-1) / s := by positivity
  have hkey : 2 * (Real.exp (-1) / s) + 1 / (s - 1) ^ 2 =
      (1 / (s - 1) + 2 * (s - 1) * Real.exp (-1) / s) * (1 / (s - 1)) := by
    field_simp; ring
  calc ∑' n, aA s n ≤ _ := hA
    _ = _ := hkey
    _ ≤ _ := mul_le_mul_of_nonneg_left hZ hR0

#print axioms gamma_term_le
#print axioms neg_logDeriv_zeta_le

end B4
