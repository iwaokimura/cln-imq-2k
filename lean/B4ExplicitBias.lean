/-
B-4 (i), step 1 (2026-10-09): the explicit prime bias (Lemma 4 of the paper,
and the split-mass step built on it), as a theorem conditional on two analytic inputs:
  * `hzeta`:  -ζ'/ζ(s) ≤ 1/(s-1) + Z           (we will prove this with Z = (s-1)/(e s));
  * `hgamma`: ½ Re ψ((s+ε)/2) ≤ ½ log π + G     (G = 0 in the paper).
Everything else is from the upstream Lean proof of [SZ]: the exact Hadamard formula
(`HadamardFormulaAt`), the retention of the real zero, and the Euler-sum identity.
The upstream proof fixes s = 1 + 1/log X (η = 1); here s = 1 + η/log X for any η > 0.
Build: see README.md.
-/
import OAI.NumberTheory.SiegelZeros.Characters.UnconditionalPrimeBias
import OAI.NumberTheory.SiegelZeros.Characters.ConditionalPrimeBias
import OAI.NumberTheory.SiegelZeros.Structure.RealBridge

namespace B4

open OAI.SiegelZeros OAI.SiegelZeros.WeightedTorusJets

/-- `exp(-η)/n ≤ n^{-(1+η/log X)}` for `0 < n ≤ X` and `η ≥ 0`. -/
theorem primeTermComparison_eta {X n η : ℝ} (hX : 1 < X) (hη : 0 ≤ η) (hn : 0 < n)
    (hnX : n ≤ X) :
    Real.exp (-η) / n ≤ n ^ (-(1 + η / Real.log X)) := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hratio : Real.log n / Real.log X ≤ 1 :=
    (div_le_one hlogX).2 (Real.log_le_log hn hnX)
  rw [Real.rpow_def_of_pos hn]
  calc
    Real.exp (-η) / n = Real.exp (-η - Real.log n) := by
      rw [Real.exp_sub, Real.exp_log hn]
    _ ≤ Real.exp (Real.log n * -(1 + η / Real.log X)) := by
      apply Real.exp_le_exp.mpr
      have heq : Real.log n * -(1 + η / Real.log X) =
          -Real.log n - η * (Real.log n / Real.log X) := by
        field_simp
        ring
      rw [heq]
      nlinarith [mul_nonneg hη (sub_nonneg.2 hratio)]

/-- Restriction of the Euler sum at `s = 1 + η/log X` to the split primes `p ≤ X`. -/
theorem prime_restriction_eta {χ : ℕ → ℝ} {X η : ℝ} (hX : 1 < X) (hη : 0 ≤ η)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ χ p = 1)
    (hχ : ∀ n, -1 ≤ χ n)
    (hsum : Summable (W05.eulerTerm χ (1 + η / Real.log X))) :
    2 * Real.exp (-η) * (∑ p ∈ P, Real.log p / p) ≤
      ∑' n, W05.eulerTerm χ (1 + η / Real.log X) n := by
  calc
    2 * Real.exp (-η) * (∑ p ∈ P, Real.log p / p) =
        ∑ p ∈ P, 2 * Real.exp (-η) * (Real.log p / p) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ P, W05.eulerTerm χ (1 + η / Real.log X) p := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hpp, hpX, hpχ⟩ := hP p hp
      have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hpp.pos
      have hterm := mul_le_mul_of_nonneg_left (primeTermComparison_eta hX hη hp0 hpX)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.log_natCast_nonneg p))
      simp only [W05.eulerTerm, ArithmeticFunction.vonMangoldt_apply_prime hpp, hpχ]
      convert hterm using 1 <;> ring
    _ ≤ ∑' n, W05.eulerTerm χ (1 + η / Real.log X) n :=
      hsum.sum_le_tsum P (fun n _ => W05.eulerTerm_nonneg (hχ n))

/-- **Explicit prime bias** (conditional on `hzeta`, `hgamma`). For a real primitive character
`χ ≠ 1` with a real zero `β ∈ (0,1)`, `s = 1 + η/log X`, and any set `P` of split primes `p ≤ X`:
`2 e^{-η} ∑_{p∈P} log p/p ≤ ½ log q + Z + G + (1/(s-1) - 1/(s-β))`. -/
theorem explicit_split_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hnp : χ ≠ 1) (hreal : ∀ a : ZMod q, (χ a).im = 0)
    {β : ℝ} (hβ0 : 0 < β) (hzero : χ.LFunction (β : ℂ) = 0)
    {X η Z G : ℝ} (hX : 1 < X) (hη : 0 < η)
    (hzeta : (-deriv riemannZeta ((1 + η / Real.log X : ℝ) : ℂ) /
        riemannZeta ((1 + η / Real.log X : ℝ) : ℂ)).re ≤
        1 / ((1 + η / Real.log X) - 1) + Z)
    (hgamma : (1 / 2 : ℝ) * (SiegelZerosAwei.W52.gammaLogDerivative
        ((((1 + η / Real.log X) + (W63.parity χ : ℝ)) / 2 : ℝ) : ℂ)).re ≤
        (1 / 2 : ℝ) * Real.log Real.pi + G)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ X ∧ χ p = 1) :
    2 * Real.exp (-η) * (∑ p ∈ P, Real.log p / p) ≤
      (1 / 2 : ℝ) * Real.log q + Z + G +
        (1 / ((1 + η / Real.log X) - 1) - 1 / ((1 + η / Real.log X) - β)) := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hs : 1 < 1 + η / Real.log X := by
    have : 0 < η / Real.log X := div_pos hη hlogX
    linarith
  have hc : ∀ n : ℕ, χ n = ((χ n).re : ℂ) := by
    intro n
    apply Complex.ext
    · rfl
    · simpa using hreal (n : ZMod q)
  have hres := prime_restriction_eta (χ := fun n : ℕ => (χ n).re) hX hη.le P
    (by
      intro p hp
      obtain ⟨hpp, hpX, hpχ⟩ := hP p hp
      exact ⟨hpp, hpX, by simp [hpχ]⟩)
    (by
      intro n
      have hnorm := χ.norm_le_one (n : ZMod q)
      rw [hc n, Complex.norm_real, Real.norm_eq_abs] at hnorm
      exact (abs_le.mp hnorm).1)
    (W05.real_eulerTerm_summable χ _ hc hs)
  rw [W05.real_eulerSum_eq_logDerivatives χ _ hc hs] at hres
  have hhad := (W63.hadamardFormulaAt_of_actual_character χ hprim hnp hreal hs).to_expansion
    hnp hprim hβ0 hzero
  have hl := W63.L_logDerivative_upper_of_hadamard χ hnp hs hhad
  have hq0 : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogdiv : Real.log ((q : ℝ) / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div (ne_of_gt hq0) (ne_of_gt Real.pi_pos)
  simp only [Complex.add_re] at hres
  rw [hlogdiv] at hl
  linarith

#print axioms explicit_split_mass

end B4
