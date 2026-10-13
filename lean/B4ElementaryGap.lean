/-
B-4 (ii), assembly (2026-10-09): `b4_explicit_zero_gap` with every analytic hypothesis discharged
by the elementary bounds of B4PrimeMass and B4Analytic. The only remaining inputs are numbers:
  K  = 1 + (5 log 2 + 3)/4 + 1/⌊U⌋                total mass (Stirling + IEANTN E₁ bound)
  Θ  = log 4                                       Chebyshev (Mathlib)
  R  = min(log q, log y + log 4 + log q / y)       ramified primes, any y ≥ 1
  LH = log H + log 4                               small primes (Mertens upper bound)
  Z  = 2(s-1)e^{-1}/s,  s = 1 + η/L                -ζ'/ζ(s) ≤ 1/(s-1) + Z
  G  = 0                                           ψ(x) ≤ log x
for 0 < η ≤ L. What is left for B-4 is (iii): show that the bracket is ≥ c'·L²/(2η²e^{-η}) for
suitable (η, N, H) on each ℓ-range (LeanCert), and Lemma L1.
Build: see README.md (needs B4ExplicitBias, B4MasterAlgebra, B4ZeroGap, B4PrimeMass, B4Analytic).
-/
import B4ZeroGap
import B4PrimeMass
import B4Analytic

namespace OAI.SiegelZeros.WeightedTorusJets

open scoped BigOperators

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

/-- **Explicit zero gap from elementary inputs.** With `U = N^{4/3}`, `L = log U`, `ℓ = log q`,
`s = 1 + η/L`: `2η²ℓe^{-η}/L² · br ≤ (1-β)ℓ`, where `br` is the bracket below. -/
theorem b4_elementary_zero_gap
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (N H : ℕ) (hH2 : 2 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (η y : ℝ) (hη : 0 < η) (hηL : η ≤ Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) (hy : 1 ≤ y) :
    let U : ℝ := (N : ℝ) ^ (4 / 3 : ℝ)
    let L : ℝ := Real.log U
    let ℓ : ℝ := Real.log q
    let s : ℝ := 1 + η / L
    let K : ℝ := 1 + (5 * Real.log 2 + 3) / 4 + 1 / (⌊U⌋₊ : ℝ)
    let R : ℝ := min ℓ (Real.log y + Real.log 4 + ℓ / y)
    let LH : ℝ := Real.log H + Real.log 4
    let Z : ℝ := 2 * (s - 1) * Real.exp (-1) / s
    let size : ℝ := Real.log N + 1 / 2 * Real.log q + Real.log 8
    let ρ : ℝ := 192 * (4 * 97 ^ 2) / (H : ℝ)
    let W : ℝ := (4 * 97 ^ 2) / ((H : ℝ) ^ (2 / 3 : ℝ) * U)
    2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 *
        (L - K - Real.exp η * (ℓ / 4 + (Z + 0) / 2) - R - LH - (1 + ρ) * size
          - (Real.log 4 * U + 3 / 2 * L) * W)
      ≤ (1 - β) * ℓ := by
  intro U L ℓ s K R LH Z size ρ W
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hUone : 1 < U := Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hL : 0 < L := Real.log_pos hUone
  have hs : 1 < s := by have := div_pos hη hL; simp only [s]; linarith
  have hqpos : 0 < q := by omega
  -- the six hypotheses
  have hT := B4.total_mass_lower hUone.le
  have hθ := B4.theta_le U (zero_lt_one.trans hUone).le
  have hR : W07.primeMass (W07.valuePrimes χ (Nat.primesLE ⌊U⌋₊) 0) ≤ R :=
    le_min (B4.ramified_mass_le_log hqpos χ _) (B4.ramified_mass_le hqpos χ _ hy)
  have hLH := B4.small_mass_le χ ⌊U⌋₊ H (by omega)
  have hzeta := B4.neg_logDeriv_zeta_le hs
  have hpar : (0 : ℝ) ≤ (W63.parity χ : ℝ) ∧ (W63.parity χ : ℝ) ≤ 1 := by
    rcases W63.parity_cases χ with h | h <;> simp [h]
  have hgamma := B4.gamma_term_le (s := s) (a := (W63.parity χ : ℝ)) (by linarith) hpar.1 hpar.2
    (by
      have h1 : η / L ≤ 1 := (div_le_one hL).mpr hηL
      have := Real.pi_gt_three
      simp only [s]; linarith)
  exact b4_explicit_zero_gap q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero N H hH2 hHN hN
    η K (Real.log 4) R LH Z 0 hη (Real.log_nonneg (by norm_num)) hT hθ hR hLH hzeta hgamma

#print axioms b4_elementary_zero_gap

end OAI.SiegelZeros.WeightedTorusJets
