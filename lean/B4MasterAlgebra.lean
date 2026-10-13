/-
B-4 (i), step 2 (2026-10-09): the master inequality of the paper
(Proposition 6) as a statement about real numbers.
No number theory here: the hypotheses are exactly the shapes delivered by
  * `harch`  (upstream eq. (4.1)):   A ≤ M/2·log M + (S₁ + S₂)·size,
  * `hraw`   (upstream eq. (4.3)):   S₁·I − Θ·M·U ≤ A,   Θ = log 4 (Mathlib) or 1.01624 (RS),
  * the partition of the prime mass: I ≥ T − Sp − R − Λ_H,
  * the total mass (Mertens / RS (3.21) or elementary):  T ≥ L − K,
  * the explicit prime bias (B4ExplicitBias.explicit_split_mass), with s = 1 + η/L.
Conclusion: δ = (1−β)ℓ ≥ 2η²ℓ e^{−η}/L² · br, with br = 𝔅 and L = λ of Proposition 6.
Build: see README.md.
-/
import Mathlib

namespace B4

/-- `1/(s-1) - 1/(s-β) ≤ (1-β)/(s-1)²` for `β ≤ 1 < s`. -/
theorem reciprocal_gap_sq {s β : ℝ} (hs : 1 < s) (hβ : β ≤ 1) :
    1 / (s - 1) - 1 / (s - β) ≤ (1 - β) / (s - 1) ^ 2 := by
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < s - β := by linarith
  rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), div_le_div_iff₀ (mul_pos h1 h2) (pow_pos h1 2)]
  nlinarith [mul_nonneg (sub_nonneg.2 hβ) (mul_nonneg h1.le (sub_nonneg.2 hβ)),
    mul_nonneg (sub_nonneg.2 hβ) (mul_pos h1 h1).le]

/-- **Master inequality, algebraic form.** -/
theorem master_algebra
    {L ℓ η β M U S₁ S₂ A I T Sp R LH K Z G Θ size : ℝ}
    (hL : 0 < L) (hℓ : 0 < ℓ) (hη : 0 < η) (hβ1 : β < 1)
    (hS₁ : 0 < S₁)
    (harch : A ≤ M / 2 * Real.log M + (S₁ + S₂) * size)
    (hraw : S₁ * I - Θ * M * U ≤ A)
    (hpart : T - Sp - R - LH ≤ I)
    (hT : L - K ≤ T)
    (hbias : 2 * Real.exp (-η) * Sp ≤
      ℓ / 2 + Z + G + (1 / ((1 + η / L) - 1) - 1 / ((1 + η / L) - β))) :
    2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 *
        (L - K - Real.exp η * (ℓ / 4 + (Z + G) / 2) - R - LH - (1 + S₂ / S₁) * size
          - (Θ * M * U + M / 2 * Real.log M) / S₁)
      ≤ (1 - β) * ℓ := by
  -- the zero's penalty
  have hs : 1 < 1 + η / L := by have := div_pos hη hL; linarith
  have hgap := reciprocal_gap_sq hs hβ1.le
  have hsq : ((1 + η / L) - 1) ^ 2 = η ^ 2 / L ^ 2 := by ring
  rw [hsq] at hgap
  have hpen : (1 - β) / (η ^ 2 / L ^ 2) = (1 - β) * L ^ 2 / η ^ 2 := by
    field_simp
  rw [hpen] at hgap
  -- split mass: Sp ≤ e^η/2 · (ℓ/2 + Z + G + (1-β)L²/η²)
  have he : 0 < Real.exp η := Real.exp_pos η
  have heinv : Real.exp (-η) * Real.exp η = 1 := by rw [← Real.exp_add]; simp
  have hSp : Sp ≤ Real.exp η / 2 * (ℓ / 2 + Z + G + (1 - β) * L ^ 2 / η ^ 2) := by
    have h := le_trans hbias (by linarith [hgap] :
      ℓ / 2 + Z + G + (1 / ((1 + η / L) - 1) - 1 / ((1 + η / L) - β)) ≤
        ℓ / 2 + Z + G + (1 - β) * L ^ 2 / η ^ 2)
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ Real.exp η / 2)
    calc Sp = Real.exp η / 2 * (2 * Real.exp (-η) * Sp) := by
            rw [show Real.exp η / 2 * (2 * Real.exp (-η) * Sp) =
              (Real.exp (-η) * Real.exp η) * Sp by ring, heinv, one_mul]
      _ ≤ _ := h2
  -- divide the determinant inequality by S₁
  have hmain : S₁ * (L - K - Sp - R - LH) - Θ * M * U ≤
      M / 2 * Real.log M + (S₁ + S₂) * size := by
    nlinarith [mul_le_mul_of_nonneg_left (le_trans (by linarith [hT] : L - K - Sp - R - LH ≤ T - Sp - R - LH) hpart) hS₁.le]
  have hdiv : L - K - Sp - R - LH - (1 + S₂ / S₁) * size
      - (Θ * M * U + M / 2 * Real.log M) / S₁ ≤ 0 := by
    have hrw : L - K - Sp - R - LH - (1 + S₂ / S₁) * size
        - (Θ * M * U + M / 2 * Real.log M) / S₁ =
        (S₁ * (L - K - Sp - R - LH) - Θ * M * U - (M / 2 * Real.log M + (S₁ + S₂) * size)) / S₁ := by
      field_simp
      ring
    rw [hrw]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hS₁.le
  -- isolate (1-β)
  set br := L - K - Real.exp η * (ℓ / 4 + (Z + G) / 2) - R - LH - (1 + S₂ / S₁) * size
    - (Θ * M * U + M / 2 * Real.log M) / S₁ with hbr
  have hbr_le : br ≤ Real.exp η / 2 * ((1 - β) * L ^ 2 / η ^ 2) := by
    have : br = (L - K - Sp - R - LH - (1 + S₂ / S₁) * size
        - (Θ * M * U + M / 2 * Real.log M) / S₁) + (Sp - Real.exp η / 2 * (ℓ / 2 + Z + G)) := by
      rw [hbr]; ring
    rw [this]
    nlinarith [hdiv, hSp]
  have hcoef : 0 ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 := by positivity
  calc 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 * br
      ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 * (Real.exp η / 2 * ((1 - β) * L ^ 2 / η ^ 2)) :=
        mul_le_mul_of_nonneg_left hbr_le hcoef
    _ = (1 - β) * ℓ * (Real.exp (-η) * Real.exp η) := by
        field_simp
    _ = (1 - β) * ℓ := by rw [heinv, mul_one]

#print axioms master_algebra

end B4
