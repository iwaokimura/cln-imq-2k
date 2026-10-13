/-
B-4 (ii), part 1 (2026-10-09): the prime-mass hypotheses of `b4_explicit_zero_gap` with explicit
elementary constants (Lemma 5 of the paper).
  * `mertens_upper`:  ∑_{p ≤ n} log p / p ≤ log n + log 4, from
      n ∑_{p ≤ n} log p/p − θ(n) ≤ ∑_{p ≤ n} log p ⌊n/p⌋ ≤ log n! ≤ n log n  and  θ(n) ≤ n log 4;
  * `small_mass_le` (hLH):   Λ_H ≤ log H + log 4;
  * `ramified_mass_le` (hR): ∑_{p | q} log p / p ≤ log y + log 4 + log q / y   (y ≥ 1);
  * `total_mass_lower` (hT): ∑_{p ≤ U} log p / p ≥ log U − 1 − (5 log 2 + 3)/4 − 1/⌊U⌋,
      from the upstream Stirling bound ∑_{d ≤ n} Λ(d)/d ≥ log n − 1 and the prime-power bound
      E₁ ≤ (5 log 2 + 3)/4 of PrimeNumberTheoremAnd (IEANTN/Mertens.lean);
  * `theta_le` (hθ): Mathlib's θ(x) ≤ x log 4.
Build: see README.md.
-/
import OAI.NumberTheory.SiegelZeros.Characters.MangoldtMass
import OAI.NumberTheory.SiegelZeros.Structure.RamifiedMass
import PrimeNumberTheoremAnd.IEANTN.Mertens

namespace B4

open Finset OAI.SiegelZeros

theorem primesLE_eq_filter (n : ℕ) : Nat.primesLE n = (Ioc 0 n).filter Nat.Prime := by
  ext p
  simp only [Nat.mem_primesLE, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
  · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, h2⟩

theorem theta_eq (n : ℕ) :
    (∑ p ∈ Nat.primesLE n, Real.log p) = Chebyshev.theta n := by
  rw [primesLE_eq_filter, Chebyshev.theta, Nat.floor_natCast]

/-- `∑_{p ≤ n} log p / p ≤ log n + log 4`. -/
theorem mertens_upper (n : ℕ) (hn : 1 ≤ n) :
    W07.primeMass (Nat.primesLE n) ≤ Real.log n + Real.log 4 := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set P := Nat.primesLE n
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  -- ∑_p log p ⌊n/p⌋ ≤ log n!
  have hfloor : (∑ p ∈ P, Real.log p * ((n / p : ℕ) : ℝ)) ≤ Real.log (n.factorial : ℝ) := by
    rw [Result.W54.log_factorial_eq_sum_vonMangoldt_mul_div]
    calc (∑ p ∈ P, Real.log p * ((n / p : ℕ) : ℝ))
        = ∑ p ∈ P, ArithmeticFunction.vonMangoldt p * ((n / p : ℕ) : ℝ) := by
          refine sum_congr rfl fun p hp => ?_
          rw [ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]
      _ ≤ ∑ d ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt d * ((n / d : ℕ) : ℝ) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            have hp' : p ∈ (Ioc 0 n).filter Nat.Prime := by rw [← primesLE_eq_filter]; exact hp
            exact (mem_filter.mp hp').1
          · intro d _ _
            exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  -- log n! ≤ n log n
  have hfact : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos n)
    exact_mod_cast Nat.factorial_le_pow n
  -- θ(n) ≤ n log 4
  have htheta : (∑ p ∈ P, Real.log p) ≤ Real.log 4 * n := by
    rw [theta_eq]; exact Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)
  -- n/p ≤ ⌊n/p⌋ + 1
  have hcmp : (n : ℝ) * W07.primeMass P ≤
      (∑ p ∈ P, Real.log p * ((n / p : ℕ) : ℝ)) + ∑ p ∈ P, Real.log p := by
    rw [← sum_add_distrib, W07.primeMass, mul_sum]
    apply sum_le_sum
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)
    have hdiv : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp0]
      have h := Nat.lt_div_mul_add (a := n) (hP p hp).pos
      have : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
      nlinarith
    calc (n : ℝ) * W07.primeWeight p = Real.log p * ((n : ℝ) / p) := by
          simp only [W07.primeWeight]; ring
      _ ≤ Real.log p * (((n / p : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hdiv hlog
      _ = _ := by ring
  have : (n : ℝ) * W07.primeMass P ≤ (n : ℝ) * (Real.log n + Real.log 4) := by nlinarith
  exact le_of_mul_le_mul_left this hnr

/-- Any set of primes `≤ y` (with `y ≥ 1` real) has mass `≤ log y + log 4`. -/
theorem mass_le_of_le {S : Finset ℕ} {y : ℝ} (hy : 1 ≤ y)
    (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ y) :
    W07.primeMass S ≤ Real.log y + Real.log 4 := by
  have hn : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  calc W07.primeMass S ≤ W07.primeMass (Nat.primesLE ⌊y⌋₊) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.mpr ⟨Nat.le_floor (hS p hp).2, (hS p hp).1⟩
        · intro p hp _
          exact W07.primeWeight_nonneg (Nat.mem_primesLE.mp hp).2
    _ ≤ Real.log ⌊y⌋₊ + Real.log 4 := mertens_upper _ hn
    _ ≤ Real.log y + Real.log 4 := by
        gcongr
        exact Nat.floor_le (by linarith)

/-- (hLH) the negative small primes. -/
theorem small_mass_le {q : ℕ} (χ : DirichletCharacter ℂ q) (n H : ℕ) (hH : 1 ≤ H) :
    W07.primeMass ((W07.valuePrimes χ (Nat.primesLE n) (-1)).filter (fun p => p ≤ H)) ≤
      Real.log H + Real.log 4 := by
  apply mass_le_of_le (by exact_mod_cast hH)
  intro p hp
  obtain ⟨hv, hpH⟩ := mem_filter.mp hp
  exact ⟨(Nat.mem_primesLE.mp (mem_filter.mp hv).1).2, by exact_mod_cast hpH⟩

/-- `∑_{p | q} log p ≤ log q`. -/
theorem sum_log_primeFactors_le {q : ℕ} (hq : 0 < q) :
    (∑ p ∈ q.primeFactors, Real.log p) ≤ Real.log q := by
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)

/-- (hR) the ramified primes: mass `≤ log y + log 4 + log q / y` for any `y ≥ 1`. -/
theorem ramified_mass_le {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (n : ℕ)
    {y : ℝ} (hy : 1 ≤ y) :
    W07.primeMass (W07.valuePrimes χ (Nat.primesLE n) 0) ≤
      Real.log y + Real.log 4 + Real.log q / y := by
  classical
  set S := W07.valuePrimes χ (Nat.primesLE n) 0
  have hS : ∀ p ∈ S, p.Prime ∧ p ∣ q := by
    intro p hp
    obtain ⟨hs, hz⟩ := mem_filter.mp hp
    have hpp := (Nat.mem_primesLE.mp hs).2
    exact ⟨hpp, (W07.prime_value_zero_iff_dvd χ hpp).mp hz⟩
  have hy0 : 0 < y := by linarith
  rw [W07.primeMass, ← sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ y)]
  have h1 : (∑ p ∈ S.filter (fun p : ℕ => (p : ℝ) ≤ y), W07.primeWeight p) ≤
      Real.log y + Real.log 4 :=
    mass_le_of_le hy fun p hp => ⟨(hS p (mem_filter.mp hp).1).1, (mem_filter.mp hp).2⟩
  have h2 : (∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ y), W07.primeWeight p) ≤ Real.log q / y := by
    calc (∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ y), W07.primeWeight p)
        ≤ ∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ y), Real.log p / y := by
          apply sum_le_sum
          intro p hp
          obtain ⟨hpS, hpy⟩ := mem_filter.mp hp
          have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (hS p hpS).1.one_le)
          exact div_le_div_of_nonneg_left hlog hy0 (le_of_lt (not_le.mp hpy))
      _ = (∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ y), Real.log p) / y := by rw [sum_div]
      _ ≤ Real.log q / y := by
          apply div_le_div_of_nonneg_right _ hy0.le
          calc (∑ p ∈ S.filter (fun p : ℕ => ¬(p : ℝ) ≤ y), Real.log p)
              ≤ ∑ p ∈ q.primeFactors, Real.log p := by
                apply sum_le_sum_of_subset_of_nonneg
                · intro p hp
                  have := hS p (mem_filter.mp hp).1
                  exact Nat.mem_primeFactors.mpr ⟨this.1, this.2, hq.ne'⟩
                · intro p hp _
                  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)
            _ ≤ Real.log q := sum_log_primeFactors_le hq
  linarith

/-- (hR), the other bound: mass `≤ log q`. -/
theorem ramified_mass_le_log {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    W07.primeMass (W07.valuePrimes χ (Nat.primesLE n) 0) ≤ Real.log q :=
  W07.zero_value_mass_le_log χ hq _ fun _ hp => (Nat.mem_primesLE.mp hp).2

/-- (hθ) -/
theorem theta_le (U : ℝ) (hU : 0 ≤ U) :
    (∑ p ∈ Nat.primesLE ⌊U⌋₊, Real.log p) ≤ Real.log 4 * U := by
  rw [theta_eq, Chebyshev.theta, Nat.floor_natCast, ← Chebyshev.theta]
  exact Chebyshev.theta_le_log4_mul_x hU

/-- (hT) the total prime mass, with `K = 1 + (5 log 2 + 3)/4 + 1/⌊U⌋`. -/
theorem total_mass_lower {U : ℝ} (hU : 1 ≤ U) :
    Real.log U - (1 + (5 * Real.log 2 + 3) / 4 + 1 / (⌊U⌋₊ : ℝ)) ≤
      W07.primeMass (Nat.primesLE ⌊U⌋₊) := by
  set n := ⌊U⌋₊
  have hn : 1 ≤ n := Nat.le_floor (by exact_mod_cast hU)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  -- ∑ Λ(d)/d ≤ ∑_p log p/p + E₁ (IEANTN), at x = n
  have hpp := Mertens.E₁Λ.le_E₁p_add_E₁ hnr
  simp only [Mertens.E₁Λ, Mertens.E₁p, Nat.floor_natCast] at hpp
  have hE := Mertens.E₁.le
  have hst := Result.W54.sum_vonMangoldt_div_lower hn
  have hprimes : W07.primeMass (Nat.primesLE n) =
      ∑ p ∈ Ioc 0 n with p.Prime, Real.log p / p := by
    rw [primesLE_eq_filter]; rfl
  -- log U ≤ log n + 1/n
  have hlogU : Real.log U ≤ Real.log n + 1 / n := by
    have hU1 : U ≤ n + 1 := (Nat.lt_floor_add_one U).le
    have h1 : Real.log U ≤ Real.log (n + 1) := Real.log_le_log (by linarith) hU1
    have h2 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      rw [← Real.log_div (by linarith) hn0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
      rw [show ((n : ℝ) + 1) / n - 1 = 1 / n by field_simp; ring] at this
      exact this
    linarith
  rw [hprimes]
  linarith

#print axioms mertens_upper
#print axioms ramified_mass_le
#print axioms total_mass_lower

end B4
