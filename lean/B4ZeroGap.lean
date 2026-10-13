/-
B-4 (i), step 3 (2026-10-09): the explicit zero gap, conditional on the analytic inputs.
We take the upstream determinant data (eq. (4.1) `harch`, eq. (4.3) `hraw`, and the pivot bounds
S₁ ≥ M H^{2/3} U/(4·97²), S₂ ≤ 192 M H^{-1/3} U) exactly as the upstream proof does in
`source_real_zero_uniform_master_bound`, and feed them into `B4.master_algebra` together with
`B4.explicit_split_mass`. The remaining inputs are hypotheses about explicit numbers:
  hT   total prime mass       log U − K ≤ ∑_{p ≤ U} log p / p
  hθ   Chebyshev              ∑_{p ≤ U} log p ≤ Θ U
  hR   ramified mass          ∑_{p ≤ U, p | q} log p / p ≤ R
  hLH  small primes           ∑_{p ≤ U, p ≤ H, χ(p) = −1} log p / p ≤ LH
  hzeta, hgamma               as in B4ExplicitBias.
Build: see README.md (needs B4ExplicitBias and B4MasterAlgebra).
-/
import OAI.NumberTheory.SiegelZeros.EntireFunctions.RealZeroUniformMasterBound
import B4ExplicitBias
import B4MasterAlgebra

namespace OAI.SiegelZeros.WeightedTorusJets

open scoped BigOperators NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

set_option maxHeartbeats 2000000 in
/-- **Explicit zero gap, conditional on the analytic inputs** (variant A with the upstream pivot
bounds). Here `U = N^{4/3}`, `L = log U`, `ℓ = log q`, `size = log N + ℓ/2 + log 8`. -/
theorem b4_explicit_zero_gap
    (q : ℕ) [NeZero q] (hq : 3 ≤ q) (hq8 : q ≠ 8)
    (χ : DirichletCharacter ℂ q) (hreal : ∀ x : ZMod q, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (N H : ℕ) (hH2 : 2 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (η K Θ R LH Z G : ℝ) (hη : 0 < η) (hΘ : 0 ≤ Θ)
    (hT : Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) - K ≤
      W07.primeMass (Nat.primesLE ⌊(N : ℝ) ^ (4 / 3 : ℝ)⌋₊))
    (hθ : (∑ p ∈ Nat.primesLE ⌊(N : ℝ) ^ (4 / 3 : ℝ)⌋₊, Real.log p) ≤ Θ * (N : ℝ) ^ (4 / 3 : ℝ))
    (hR : W07.primeMass (W07.valuePrimes χ (Nat.primesLE ⌊(N : ℝ) ^ (4 / 3 : ℝ)⌋₊) 0) ≤ R)
    (hLH : W07.primeMass ((W07.valuePrimes χ (Nat.primesLE ⌊(N : ℝ) ^ (4 / 3 : ℝ)⌋₊) (-1)).filter
      (fun p => p ≤ H)) ≤ LH)
    (hzeta : (-deriv riemannZeta ((1 + η / Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) : ℝ) : ℂ) /
        riemannZeta ((1 + η / Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) : ℝ) : ℂ)).re ≤
        1 / ((1 + η / Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) - 1) + Z)
    (hgamma : (1 / 2 : ℝ) * (SiegelZerosAwei.W52.gammaLogDerivative
        ((((1 + η / Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) + (W63.parity χ : ℝ)) / 2 : ℝ) : ℂ)).re ≤
        (1 / 2 : ℝ) * Real.log Real.pi + G) :
    let U : ℝ := (N : ℝ) ^ (4 / 3 : ℝ)
    let L : ℝ := Real.log U
    let ℓ : ℝ := Real.log q
    let size : ℝ := Real.log N + 1 / 2 * Real.log q + Real.log 8
    let ρ : ℝ := 192 * (4 * 97 ^ 2) / (H : ℝ)
    let W : ℝ := (4 * 97 ^ 2) / ((H : ℝ) ^ (2 / 3 : ℝ) * U)
    2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 *
        (L - K - Real.exp η * (ℓ / 4 + (Z + G) / 2) - R - LH - (1 + ρ) * size
          - (Θ * U + 3 / 2 * L) * W)
      ≤ (1 - β) * ℓ := by
  classical
  intro U L ℓ size ρ W
  obtain ⟨C, _hC, _hC4, CH, hsource⟩ :=
    source_character_global_greedy_determinant_master_bounds
  have hHpos : 0 < H := by omega
  obtain ⟨e, he⟩ := exists_global_weight_sorted_jet_equiv H hHpos
  have hfield := characterField_ne_sourceSqrtTwoField_of_ne_eight q χ hprim
    (real_character_isQuadratic χ hreal) hne hq8
  obtain ⟨d, a, b, _hd, _hdsize, _hddiv, _hdns, _ha, _hb, _hfield, _hdisc,
    _hfund, _hformula, v, _hv, _hint, _hdegree, σ, τ, _hσa, _hσb, _hτa, _hτb,
    _hcard, _hall, _hcomm, hdata⟩ := hsource q χ hreal hprim hne hfield
  let n : Fin (N ^ 4) ≃ (Fin 4 → Fin N) :=
    (Fintype.equivFinOfCardEq (by simp : Fintype.card (Fin 4 → Fin N) = N ^ 4)).symm
  obtain ⟨g, α, _hg, _hα, hrange, _hmono, _hweight, _hstable,
    Δ, _hΔ, _hΔne, harch, _hdiv, hraw, _hfinite, hlarge⟩ := hdata N H hHpos hHN n e he
  obtain ⟨hpivot₁, hpivot₂, _hSpos, _hmaster⟩ := hlarge hN
  have hS₁eq := sum_embedding_eq_sum_finset_of_range α _ hrange (fun a => (a 0 : ℝ))
  have hS₂eq := sum_embedding_eq_sum_finset_of_range α _ hrange
    (fun a => ((a 1 : ℝ) + a 2))
  rw [← hS₁eq] at hpivot₁
  rw [← hS₂eq] at hpivot₂
  -- basic positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < (N : ℝ) ^ 4 := pow_pos hNpos _
  have hUone : 1 < U := Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) (by norm_num)
  have hUpos : 0 < U := zero_lt_one.trans hUone
  have hL : 0 < L := Real.log_pos hUone
  have hqpos : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hℓ : 0 < ℓ := Real.log_pos hqpos
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  set S₁ := ∑ i, (α i 0 : ℝ) with hS₁def
  set S₂ := ∑ i, ((α i 1 : ℝ) + α i 2) with hS₂def
  have hS₁low : (N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2) ≤ S₁ := hpivot₁
  have hS₁ : 0 < S₁ := lt_of_lt_of_le (by positivity) hS₁low
  -- the prime sets
  set S := Nat.primesLE ⌊U⌋₊ with hSdef
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  -- eq. (4.3), second form, with the Chebyshev hypothesis
  obtain ⟨hraw1, hraw2, _⟩ := hraw U hUpos.le
  have h3 := le_trans hraw2 hraw1
  -- the good primes of hraw are W07.goodPrimes
  have hgood : (S.filter (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1)) =
      W07.goodPrimes χ S H := by
    ext p
    simp only [W07.goodPrimes, W07.valuePrimes, Finset.mem_filter]
    tauto
  -- explicit split mass at s = 1 + η/L for the split primes p ≤ U
  have hsplit := B4.explicit_split_mass χ hprim hne hreal hβ0 hzero hUone hη hzeta hgamma
    (W07.valuePrimes χ S 1) (by
      intro p hp
      obtain ⟨hpS, hpχ⟩ := Finset.mem_filter.mp hp
      refine ⟨hSprime p hpS, ?_, hpχ⟩
      exact (Nat.cast_le.mpr (Nat.mem_primesLE.mp hpS).1).trans (Nat.floor_le hUpos.le))
  -- the mass partition
  have hpart := W07.prime_mass_partition χ (real_character_isQuadratic χ hreal) S
  have hneg := W07.negative_mass_partition χ S H
  rw [W07.discarded_eq_small_negative χ S hSprime hH2] at hneg
  -- apply the algebra
  have hlogM : Real.log ((N : ℝ) ^ 4) = 3 * L := log_degree_four_eq_three_log_scale hNpos
  have hlogN : Real.log (N : ℝ) = 3 / 4 * L := log_eq_three_quarters_log_scale hNpos
  have hcmp : S₁ * W07.primeMass (W07.goodPrimes χ S H) - Θ * (N : ℝ) ^ 4 * U ≤
      S₁ * (∑ p ∈ S.filter (fun p => H < p ∧ ¬p ∣ 2 * q ∧ χ p = -1), Real.log p / (p : ℝ)) -
        (N : ℝ) ^ 4 * (∑ p ∈ S, Real.log p) := by
    rw [hgood]
    simp only [W07.primeMass, W07.primeWeight]
    nlinarith [mul_le_mul_of_nonneg_left hθ hM.le]
  have hbias' : 2 * Real.exp (-η) * W07.primeMass (W07.valuePrimes χ S 1) ≤
      ℓ / 2 + Z + G + (1 / ((1 + η / L) - 1) - 1 / ((1 + η / L) - β)) := by
    have h := hsplit
    simp only [W07.primeMass, W07.primeWeight]
    linarith
  have key := B4.master_algebra (L := L) (ℓ := ℓ) (η := η) (β := β) (M := (N : ℝ) ^ 4) (U := U)
    (S₁ := S₁) (S₂ := S₂)
    (I := W07.primeMass (W07.goodPrimes χ S H)) (T := W07.primeMass S)
    (Sp := W07.primeMass (W07.valuePrimes χ S 1)) (R := R) (LH := LH) (K := K) (Z := Z) (G := G)
    (Θ := Θ) (size := size) hL hℓ hη hβ1 hS₁ harch (le_trans hcmp h3)
    (by linarith [hR, hLH]) hT hbias'
  -- substitute the pivot bounds into the bracket (monotone)
  have hρ : S₂ / S₁ ≤ ρ := by
    rw [div_le_iff₀ hS₁]
    have hH13 : (H : ℝ) ^ (-(1 / 3 : ℝ)) * (H : ℝ) ^ (2 / 3 : ℝ) * (H : ℝ) = (H : ℝ) ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add hHr, ← Real.rpow_add_one (ne_of_gt hHr)]; norm_num
    calc S₂ ≤ 192 * (N : ℝ) ^ 4 * (H : ℝ) ^ (-(1 / 3 : ℝ)) * U := hpivot₂
      _ = ρ * ((N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2)) := by
          simp only [ρ]
          field_simp
          rw [show (H : ℝ) ^ (-(1 / 3 : ℝ)) * (H : ℝ) = (H : ℝ) ^ (2 / 3 : ℝ) by
            rw [← Real.rpow_add_one (ne_of_gt hHr)]; norm_num]
      _ ≤ ρ * S₁ := mul_le_mul_of_nonneg_left hS₁low (by positivity)
  have hW : (N : ℝ) ^ 4 / S₁ ≤ W := by
    rw [div_le_iff₀ hS₁]
    calc (N : ℝ) ^ 4 = W * ((N : ℝ) ^ 4 * (H : ℝ) ^ (2 / 3 : ℝ) * U / (4 * 97 ^ 2)) := by
          simp only [W]; field_simp
      _ ≤ W * S₁ := mul_le_mul_of_nonneg_left hS₁low (by positivity)
  have hsize : 0 ≤ size := by
    simp only [size]
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hextra : (Θ * (N : ℝ) ^ 4 * U + (N : ℝ) ^ 4 / 2 * (3 * L)) / S₁ ≤ (Θ * U + 3 / 2 * L) * W := by
    rw [show (Θ * (N : ℝ) ^ 4 * U + (N : ℝ) ^ 4 / 2 * (3 * L)) / S₁ =
      (Θ * U + 3 / 2 * L) * ((N : ℝ) ^ 4 / S₁) by ring]
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  rw [hlogM] at key
  have hcoef : 0 ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 := by positivity
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hcoef) key
  nlinarith [mul_le_mul_of_nonneg_right hρ hsize]

#print axioms b4_explicit_zero_gap

end OAI.SiegelZeros.WeightedTorusJets
