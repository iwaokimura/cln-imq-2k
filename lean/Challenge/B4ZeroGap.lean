import Mathlib

/-! Comparator challenge for the explicit zero gap (paper, Theorem `thm:gap`, all `q ≥ 3`) and for the
conductor-8 lemma (`lem:chi8`), Mathlib only.
Module `Challenge.B4ZeroGap`; the solution is the module `B4Chi8` (see `comparator/README.md`). -/

namespace B4.Chi8

theorem re_LFunction_pos (χ : DirichletCharacter ℂ 8) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    0 < (DirichletCharacter.LFunction χ (σ : ℂ)).re := by
  sorry

theorem zero_gap_all (q : ℕ) [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hreal : ∀ x : ZMod q, (χ x).im = 0) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (5811/10000000 : ℝ) ≤ (1 - β) * Real.log q := by
  sorry

theorem zero_gap_large (q : ℕ) [NeZero q] (hq : 3 ≤ q) (χ : DirichletCharacter ℂ q)
    (hreal : ∀ x : ZMod q, (χ x).im = 0) (hprim : χ.IsPrimitive) (hne : χ ≠ 1) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hl : (350131/10000 : ℝ) ≤ Real.log q) :
    (1193/200000 : ℝ) ≤ (1 - β) * Real.log q := by
  sorry

end B4.Chi8
