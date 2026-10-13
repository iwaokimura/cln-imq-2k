/-
Conductor 8 (paper, Lemma `lem:chi8`), 2026-10-11.

For every nontrivial Dirichlet character `χ` mod 8 and every real `σ > 0`, `Re L(σ, χ) > 0`; in particular
`L(s, χ)` has no real zero in `(0, 1)`. No primitivity or reality hypothesis is needed: `(ℤ/8)ˣ` has
exponent 2, so `u = χ 3` and `v = χ 5` lie in `{±1}`, and `χ ≠ 1` means `(u, v) ≠ (1, 1)`.

Proof: by `B4LSeriesCont`, the partial sums of the Dirichlet series converge to `L(σ, χ)`. With
`f(x) = x^{-σ}` and `y = 8i + 1`, the block of the 8 terms `n = 8i + 1, …, 8i + 8` is
  `f(y) + u f(y+2) + v f(y+4) + uv f(y+6)`,
which is positive: for `(u, v) = (1, -1)` and `(-1, 1)` since `f` is decreasing, and for `(-1, -1)`
since `x ↦ f(x) - f(x+2)` is strictly decreasing (its derivative is negative).

Consequently the zero gap `B4.Cert.zero_gap_all` holds for all `q ≥ 3`, without `q ≠ 8`.
-/
import B4LSeriesCont
import B4Certificates

namespace B4.Chi8

open Complex Filter Topology Finset

local instance : Fact (1 < 8) := ⟨by norm_num⟩

/-! ### Real inequalities -/

/-- `f(x) = x^{-σ}` is strictly decreasing on `(0, ∞)`. -/
theorem rpow_neg_lt {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxy : x < y) :
    y ^ (-σ) < x ^ (-σ) :=
  Real.rpow_lt_rpow_of_neg hx hxy (by linarith)

/-- `x ↦ x^{-σ} - (x+2)^{-σ}` is strictly decreasing on `[1, ∞)`. -/
theorem gap_strictAnti {σ : ℝ} (hσ : 0 < σ) :
    StrictAntiOn (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ)) (Set.Ici 1) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => x ^ (-σ) - (x + 2) ^ (-σ))
      (1 * (-σ) * x ^ (-σ - 1) - 1 * (-σ) * (x + 2) ^ (-σ - 1)) x := by
    intro x hx
    have h1 := (hasDerivAt_id' x).rpow_const (p := -σ) (Or.inl hx.ne')
    have h2 := ((hasDerivAt_id' x).add_const 2).rpow_const (p := -σ)
      (Or.inl (by positivity : x + 2 ≠ 0))
    exact h1.sub h2
  apply strictAntiOn_of_deriv_neg (convex_Ici 1)
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    exact (hd x hx0).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := lt_trans one_pos hx
    rw [(hd x hx0).deriv]
    have := Real.rpow_lt_rpow_of_neg hx0 (by linarith : x < x + 2) (by linarith : -σ - 1 < 0)
    nlinarith

/-- The block `f(y) + u f(y+2) + v f(y+4) + uv f(y+6)`. -/
noncomputable def block (σ u v y : ℝ) : ℝ :=
  y ^ (-σ) + u * (y + 2) ^ (-σ) + v * (y + 4) ^ (-σ) + u * v * (y + 6) ^ (-σ)

theorem block_pos {σ : ℝ} (hσ : 0 < σ) {u v : ℝ} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (huv : ¬ (u = 1 ∧ v = 1)) {y : ℝ} (hy : 1 ≤ y) : 0 < block σ u v y := by
  have hy0 : 0 < y := by linarith
  have a1 := rpow_neg_lt hσ hy0 (by linarith : y < y + 2)
  have a2 := rpow_neg_lt hσ (by linarith : 0 < y + 2) (by linarith : y + 2 < y + 4)
  have a3 := rpow_neg_lt hσ (by linarith : 0 < y + 4) (by linarith : y + 4 < y + 6)
  unfold block
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd ⟨rfl, rfl⟩ huv
  · linarith
  · linarith
  · have h := gap_strictAnti hσ (Set.mem_Ici.2 hy) (Set.mem_Ici.2 (by linarith : (1 : ℝ) ≤ y + 4))
      (by linarith : y < y + 4)
    simp only at h
    rw [show y + 4 + 2 = y + 6 by ring] at h
    linarith

/-! ### Characters mod 8 -/

theorem chi_values (χ : DirichletCharacter ℂ 8) :
    χ 0 = 0 ∧ χ 2 = 0 ∧ χ 4 = 0 ∧ χ 6 = 0 ∧ χ 1 = 1 ∧ χ 7 = χ 3 * χ 5 ∧
      (χ 3 = 1 ∨ χ 3 = -1) ∧ (χ 5 = 1 ∨ χ 5 = -1) := by
  have h0 : χ 0 = 0 := MulChar.map_zero χ
  have h2 : χ 2 = 0 := by
    have : χ 2 ^ 3 = 0 := by
      rw [← map_pow, show (2 : ZMod 8) ^ 3 = 0 by decide, h0]
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  have h4 : χ 4 = 0 := by rw [show (4 : ZMod 8) = 2 * 2 by decide, map_mul, h2, zero_mul]
  have h6 : χ 6 = 0 := by rw [show (6 : ZMod 8) = 2 * 3 by decide, map_mul, h2, zero_mul]
  have h7 : χ 7 = χ 3 * χ 5 := by rw [← map_mul, show (3 : ZMod 8) * 5 = 7 by decide]
  have sq : ∀ a : ZMod 8, a * a = 1 → (χ a = 1 ∨ χ a = -1) := by
    intro a ha
    rw [← mul_self_eq_one_iff, ← map_mul, ha, map_one]
  exact ⟨h0, h2, h4, h6, map_one χ, h7, sq 3 (by decide), sq 5 (by decide)⟩

theorem eq_one_of (χ : DirichletCharacter ℂ 8) (h3 : χ 3 = 1) (h5 : χ 5 = 1) : χ = 1 := by
  obtain ⟨a0, a2, a4, a6, a1, a7, -, -⟩ := chi_values χ
  obtain ⟨b0, b2, b4, b6, b1, b7, -, -⟩ := chi_values (1 : DirichletCharacter ℂ 8)
  have b3 : (1 : DirichletCharacter ℂ 8) 3 = 1 :=
    MulChar.one_apply (IsUnit.of_mul_eq_one (a := (3 : ZMod 8)) 3 (by decide))
  have b5 : (1 : DirichletCharacter ℂ 8) 5 = 1 :=
    MulChar.one_apply (IsUnit.of_mul_eq_one (a := (5 : ZMod 8)) 5 (by decide))
  apply MulChar.ext'
  intro a
  have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by revert a; decide
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [h3, b3]
  · rw [a4, b4]
  · rw [h5, b5]
  · rw [a6, b6]
  · rw [a7, b7, h3, h5, b3, b5]

/-! ### The Dirichlet series in blocks of 8 -/

/-- The `n`-th term `χ(n+1) (n+1)^{-σ}`, as in `B4.tendsto_partial_contL`. -/
noncomputable def term (χ : DirichletCharacter ℂ 8) (σ : ℝ) (n : ℕ) : ℂ :=
  χ ((n + 1 : ℕ) : ZMod 8) * ((n : ℂ) + 1) ^ (-(σ : ℂ))

theorem term_eq (χ : DirichletCharacter ℂ 8) (σ : ℝ) (i r : ℕ) :
    term χ σ (8 * i + r) =
      χ ((r + 1 : ℕ) : ZMod 8) * (((8 * i + r + 1 : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold term
  have hc : ((8 * i + r + 1 : ℕ) : ZMod 8) = ((r + 1 : ℕ) : ZMod 8) := by
    push_cast
    rw [show (8 : ZMod 8) = 0 by decide]
    ring
  have hp : ((8 * i + r : ℕ) : ℂ) + 1 = ((8 * i + r + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, hp, Complex.ofReal_cpow (by positivity)]
  push_cast
  ring_nf

theorem block_sum (χ : DirichletCharacter ℂ 8) (σ u v : ℝ) (h3 : χ 3 = u) (h5 : χ 5 = v) (i : ℕ) :
    ∑ r ∈ range 8, term χ σ (8 * i + r) = ((block σ u v (8 * i + 1) : ℝ) : ℂ) := by
  obtain ⟨a0, a2, a4, a6, a1, a7, -, -⟩ := chi_values χ
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, term_eq]
  have a8 : χ 8 = 0 := by rw [show (8 : ZMod 8) = 0 by decide, a0]
  norm_num
  simp only [a2, a4, a6, a7, a8, h3, h5]
  unfold block
  push_cast
  ring_nf

theorem partial_eq (χ : DirichletCharacter ℂ 8) (σ u v : ℝ) (h3 : χ 3 = u) (h5 : χ 5 = v) (J : ℕ) :
    ∑ n ∈ range (8 * J), term χ σ n = ((∑ i ∈ range J, block σ u v (8 * i + 1) : ℝ) : ℂ) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [show 8 * (J + 1) = 8 * J + 8 by ring, Finset.sum_range_add, ih, block_sum χ σ u v h3 h5,
      Finset.sum_range_succ]
    push_cast
    ring

/-! ### Main results -/

/-- **Lemma `lem:chi8`.** For a nontrivial Dirichlet character `χ` mod 8 and `σ > 0`,
`Re L(σ, χ) > 0`. -/
theorem re_LFunction_pos (χ : DirichletCharacter ℂ 8) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    0 < (DirichletCharacter.LFunction χ σ).re := by
  have hs : 0 < (σ : ℂ).re := by simpa using hσ
  have hM := norm_psum_le χ hχ
  have hlim : Tendsto (fun N => ∑ n ∈ range N, term χ σ n) atTop
      (𝓝 (DirichletCharacter.LFunction χ σ)) := by
    rw [LFunction_eq_contL χ hχ _ hM hs]
    exact tendsto_partial_contL (fun n => χ n) _ hM (σ : ℂ) hs
  obtain ⟨-, -, -, -, -, -, h3c, h5c⟩ := chi_values χ
  have key : ∃ u v : ℝ, χ 3 = (u : ℂ) ∧ χ 5 = (v : ℂ) ∧ (u = 1 ∨ u = -1) ∧ (v = 1 ∨ v = -1) ∧
      ¬ (u = 1 ∧ v = 1) := by
    rcases h3c with h3 | h3 <;> rcases h5c with h5 | h5
    · exact absurd (eq_one_of χ h3 h5) hχ
    · exact ⟨1, -1, by simp [h3], by simp [h5], Or.inl rfl, Or.inr rfl, by norm_num⟩
    · exact ⟨-1, 1, by simp [h3], by simp [h5], Or.inr rfl, Or.inl rfl, by norm_num⟩
    · exact ⟨-1, -1, by simp [h3], by simp [h5], Or.inr rfl, Or.inr rfl, by norm_num⟩
  obtain ⟨u, v, h3, h5, hu, hv, huv⟩ := key
  have hsub : Tendsto (fun J => ∑ n ∈ range (8 * J), term χ σ n) atTop
      (𝓝 (DirichletCharacter.LFunction χ σ)) :=
    hlim.comp (tendsto_atTop_mono (fun J => by simp only [id_eq]; omega) tendsto_id)
  have hre : Tendsto (fun J => ∑ i ∈ range J, block σ u v (8 * i + 1)) atTop
      (𝓝 (DirichletCharacter.LFunction χ σ).re) := by
    have := (Complex.continuous_re.tendsto _).comp hsub
    refine this.congr (fun J => ?_)
    simp only [Function.comp_apply, partial_eq χ σ u v h3 h5 J, Complex.ofReal_re]
  have hpos : ∀ i : ℕ, 0 < block σ u v (8 * i + 1) := fun i =>
    block_pos hσ hu hv huv (by have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  have hge : ∀ᶠ J in atTop, block σ u v (8 * (0 : ℕ) + 1) ≤
      ∑ i ∈ range J, block σ u v (8 * i + 1) := by
    filter_upwards [eventually_ge_atTop 1] with J hJ
    exact Finset.single_le_sum (f := fun i : ℕ => block σ u v (8 * i + 1))
      (fun i _ => (hpos i).le) (Finset.mem_range.2 (by omega))
  exact lt_of_lt_of_le (hpos 0) (ge_of_tendsto hre hge)

theorem LFunction_ne_zero (χ : DirichletCharacter ℂ 8) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    DirichletCharacter.LFunction χ σ ≠ 0 := by
  intro h
  have := re_LFunction_pos χ hχ hσ
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

/-- **Theorem `thm:gap`, first bound, for all `q ≥ 3`** (`B4.Cert.zero_gap_all` without `q ≠ 8`). -/
theorem zero_gap_all (q : ℕ) [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hreal : ∀ x : ZMod q, (χ x).im = 0) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (5811/10000000 : ℝ) ≤ (1 - β) * Real.log q := by
  by_cases hq8 : q = 8
  · subst hq8
    exact absurd hzero (LFunction_ne_zero χ hne hβ0)
  · exact B4.Cert.zero_gap_all q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero

/-- The zero gap `(c, l0)` of the paper's Notation, for all `q ≥ 3`. -/
def GapFromAll (c l0 : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ (χ : DirichletCharacter ℂ q),
    (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
    ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
    l0 ≤ Real.log q → c ≤ (1 - β) * Real.log q

/-- `B4.GapFrom` (which assumes `q ≠ 8`) implies the zero gap for all `q ≥ 3`. -/
theorem gapFromAll_of_gapFrom {c l0 : ℝ} (h : B4.GapFrom c l0) : GapFromAll c l0 := by
  intro q _ hq χ hreal hprim hne β hβ0 hβ1 hzero hl
  by_cases hq8 : q = 8
  · subst hq8
    exact absurd hzero (LFunction_ne_zero χ hne hβ0)
  · exact h q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero hl

/-- **Theorem `thm:gap`, second bound, for all `q ≥ 3`.** -/
theorem zero_gap_for_h2000 : GapFromAll (1193/200000 : ℝ) (350131/10000 : ℝ) :=
  gapFromAll_of_gapFrom B4.Cert.zero_gap_for_h2000

/-- **Theorem `thm:gap`, second bound, for all `q ≥ 3`**, with `GapFromAll` unfolded (Mathlib notions only). -/
theorem zero_gap_large (q : ℕ) [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hreal : ∀ x : ZMod q, (χ x).im = 0) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hl : (350131/10000 : ℝ) ≤ Real.log q) :
    (1193/200000 : ℝ) ≤ (1 - β) * Real.log q :=
  zero_gap_for_h2000 q hq χ hreal hprim hne β hβ0 hβ1 hzero hl

end B4.Chi8

#print axioms B4.Chi8.re_LFunction_pos
#print axioms B4.Chi8.zero_gap_all
#print axioms B4.Chi8.zero_gap_for_h2000
#print axioms B4.Chi8.zero_gap_large
