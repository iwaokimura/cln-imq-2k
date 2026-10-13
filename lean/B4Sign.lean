/-
B-4, Lemma L1 (elementary version), part (c) (2026-10-10): the sign of L(σ, χ) on a zero-free interval.
For a real nontrivial character χ mod q:
  * `LFunction_im_eq_zero`: L(σ, χ) is real for real σ > 0 (limit of real partial sums, B4LSeriesCont);
  * `LFunction_re_pos_large`: Re L(q+1, χ) > 0, from the tail bound with N = 1:
    |L(σ, χ) − 1| ≤ q 2^{-σ};
  * `LFunction_nonneg_of_zero_free`: if L(t, χ) ≠ 0 for σ₀ < t < 1, then L(σ₀, χ) ≥ 0
    (intermediate value theorem on [σ₀, q+1]; L(t) ≠ 0 for t ≥ 1 is Mathlib's nonvanishing theorem).
Build: see README.md.
-/
import B4LSeriesCont

namespace B4

open Complex Filter Topology Finset

variable {q : ℕ} [NeZero q]

/-- `L(σ, χ)` is real for real `σ > 0` and real `χ`. -/
theorem LFunction_im_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {σ : ℝ} (hσ : 0 < σ) :
    (DirichletCharacter.LFunction χ σ).im = 0 := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hlim := tendsto_partial_contL (fun n => χ n) ((q : ℝ) / 2) (norm_psum_le χ hχ) σ hs
  rw [← LFunction_eq_contL χ hχ _ (norm_psum_le χ hχ) hs] at hlim
  have hclosed : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  refine hclosed.mem_of_tendsto hlim (Eventually.of_forall fun N => ?_)
  simp only [Set.mem_ofPred_eq, im_sum]
  refine sum_eq_zero fun n _ => ?_
  have hc : ((n : ℂ) + 1) ^ (-(σ : ℂ)) = ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]; push_cast; ring_nf
  rw [hc, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  simp [hreal]

/-- `Re L(q+1, χ) > 0`. -/
theorem LFunction_re_pos_large (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    0 < (DirichletCharacter.LFunction χ (((q : ℝ) + 1 : ℝ) : ℂ)).re := by
  have hT : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have h := LFunction_sub_partial_le_q χ hχ hT 1
  have hsum : (∑ n ∈ range 1, χ ((n + 1 : ℕ) : ZMod q) * ((n : ℂ) + 1) ^ (-((((q : ℝ) + 1 : ℝ)) : ℂ)))
      = 1 := by simp
  rw [hsum] at h
  -- q 2^{-(q+1)} < 1
  have hsmall : (q : ℝ) * (((1 : ℕ) : ℝ) + 1) ^ (-((q : ℝ) + 1)) < 1 := by
    rw [show (((1 : ℕ) : ℝ) + 1 : ℝ) = 2 by norm_num, Real.rpow_neg (by norm_num),
      show (q : ℝ) + 1 = ((q + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      ← div_eq_mul_inv, div_lt_one (by positivity)]
    have : q < 2 ^ (q + 1) := by
      calc q < 2 ^ q := Nat.lt_two_pow_self
        _ ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast this
  have h2 := Complex.re_le_norm (1 - DirichletCharacter.LFunction χ (((q : ℝ) + 1 : ℝ) : ℂ))
  rw [norm_sub_rev] at h2
  simp only [Complex.sub_re, Complex.one_re] at h2
  linarith [h2.trans h]

/-- **Sign.** On a zero-free interval `(σ₀, 1)`, `L(σ₀, χ) ≥ 0`. -/
theorem LFunction_nonneg_of_zero_free (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1)
    (hzf : ∀ t : ℝ, σ₀ < t → t < 1 → DirichletCharacter.LFunction χ t ≠ 0) :
    0 ≤ (DirichletCharacter.LFunction χ σ₀).re := by
  set g : ℝ → ℝ := fun t => (DirichletCharacter.LFunction χ t).re
  have hg : Continuous g :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal)
  set T : ℝ := (q : ℝ) + 1
  have hT : 0 < g T := LFunction_re_pos_large χ hχ
  -- g ≠ 0 on (σ₀, ∞)
  have hne : ∀ t : ℝ, σ₀ < t → g t ≠ 0 := by
    intro t ht hgt
    have him := LFunction_im_eq_zero χ hχ hreal (lt_trans h0 ht)
    have hz : DirichletCharacter.LFunction χ t = 0 := Complex.ext hgt him
    rcases lt_or_ge t 1 with h1 | h1
    · exact hzf t ht h1 hz
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (s := (t : ℂ)) (Or.inl hχ)
        (by simpa using h1) hz
  by_contra hneg
  replace hneg := not_le.mp hneg
  have hσT : σ₀ ≤ T := by
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    simp only [T]; linarith
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hσT hg.continuousOn ⟨hneg.le, hT.le⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h] at hgt; linarith
  · exact hne t h hgt

#print axioms LFunction_nonneg_of_zero_free

end B4
