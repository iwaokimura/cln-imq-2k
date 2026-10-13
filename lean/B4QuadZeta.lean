/-
B-4, class number formula, part 2 (2026-10-10): `ζ_K = ζ · L(χ_D)` for a quadratic field.

`K = ℚ(√d)` (`θ² = d`, `d` squarefree, as in TauCeti), `D = fundamentalDiscriminant d = disc K`,
`χ_D` = TauCeti's `fundamentalDiscriminantChar D` (primitive, level `|D|`), viewed in `ℂ`.

* `chiZ_eq_zero_of_dvd`, `chiZ_pm_one`, `ncard_eq_two_iff`: at a prime `p`, `χ_D(p) = 0, 1, -1` according as `p` ramifies, splits, is inert.
  Odd `p`: TauCeti's splitting law `NumberField.ncard_primesOver_quadratic_iff` and
  `fundamentalDiscriminantChar_natCast_eq_legendreSym`. `p = 2`: `χ_D(2) = χ₈(D)` from the
  prime-discriminant factorization and `primeDiscriminantCharFun_two`, against TauCeti's
  `NumberField.ncard_primesOver_two_of_mod_four_eq_one`.
* `mult_prime_pow`: `#{I : N I = p^k} = ∑_{i ≤ k} χ_D(p)^i` (with `B4QuadSplit`).
* `multA_eq`: `#{I : N I = n} = ∑_{m ∣ n} χ_D(m)` (both sides multiplicative; the
  left side by AINTLIB `idealNormMultiplicity_mul`).
* `dedekindZeta_eq`: `ζ_K(s) = ζ(s) L(s, χ_D)` for `Re s > 1`.
-/
import B4QuadSplit
import TauCeti.NumberTheory.NumberField.Quadratic.Splitting
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character

open Ideal Module Polynomial
open scoped NumberField ArithmeticFunction.zeta

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace B4.CNF

open TauCeti.Multiquadratic

/-- The fundamental discriminant of `ℚ(√d)`. -/
abbrev Dd (d : ℤ) : ℤ := fundamentalDiscriminant d

theorem isFD {d : ℤ} (hsf : Squarefree d) : IsFundamentalDiscriminant (Dd d) :=
  isFundamentalDiscriminant_fundamentalDiscriminant hsf

/-- `χ_D`, integer valued, level `|D|`. -/
noncomputable abbrev chiZ (d : ℤ) (hsf : Squarefree d) : DirichletCharacter ℤ (Dd d).natAbs :=
  fundamentalDiscriminantChar (Dd d) (isFD hsf)

/-- `χ_D` with complex values. -/
noncomputable abbrev chi (d : ℤ) (hsf : Squarefree d) : DirichletCharacter ℂ (Dd d).natAbs :=
  (chiZ d hsf).ringHomComp (Int.castRingHom ℂ)

theorem neZero_Dd {d : ℤ} (hsf : Squarefree d) : NeZero (Dd d).natAbs :=
  ⟨Int.natAbs_ne_zero.mpr (isFD hsf).ne_zero⟩

theorem chi_apply {d : ℤ} (hsf : Squarefree d) (a : ZMod (Dd d).natAbs) :
    chi d hsf a = ((chiZ d hsf a : ℤ) : ℂ) := by
  simp [MulChar.ringHomComp_apply]

theorem chiZ_eq_zero_of_dvd {d : ℤ} (hsf : Squarefree d) {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ Dd d) : chiZ d hsf (p : ZMod (Dd d).natAbs) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro hcop
  have hdvd : p ∣ (Dd d).natAbs := Int.natCast_dvd.mp h
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem chiZ_ne_zero_of_not_dvd {d : ℤ} (hsf : Squarefree d) {p : ℕ} (hp : p.Prime)
    (h : ¬ (p : ℤ) ∣ Dd d) : chiZ d hsf (p : ZMod (Dd d).natAbs) ≠ 0 := by
  have hu : IsUnit (p : ZMod (Dd d).natAbs) := by
    rw [ZMod.isUnit_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h' => h (Int.natCast_dvd.mpr h')
  intro h0
  have := hu.map (chiZ d hsf)
  rw [h0] at this
  exact not_isUnit_zero this

theorem chiZ_pm_one {d : ℤ} (hsf : Squarefree d) {p : ℕ} (hp : p.Prime) (h : ¬ (p : ℤ) ∣ Dd d) :
    chiZ d hsf (p : ZMod (Dd d).natAbs) = 1 ∨ chiZ d hsf (p : ZMod (Dd d).natAbs) = -1 := by
  rcases fundamentalDiscriminantChar_isQuadratic (isFD hsf) (p : ZMod (Dd d).natAbs) with
    h0 | h1 | h2
  · exact absurd h0 (chiZ_ne_zero_of_not_dvd hsf hp h)
  · exact Or.inl h1
  · exact Or.inr h2

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}
  (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d)
include hmin hgen hsf

theorem discr_eq : NumberField.discr K = Dd d := discr_eq_fundamentalDiscriminant hmin hgen hsf

/-- **The splitting law, in terms of `χ_D`**, at a prime not dividing `D`. -/
theorem ncard_eq_two_iff {p : ℕ} (hp : p.Prime) (hpD : ¬ (p : ℤ) ∣ Dd d) :
    (PO K p).ncard = 2 ↔ chiZ d hsf (p : ZMod (Dd d).natAbs) = 1 := by
  haveI := Fact.mk hp
  have hfin : finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
  obtain ⟨s, hs, _, hprod⟩ := (isFD hsf).exists_finset_primeDiscriminant
  have hval : chiZ d hsf (p : ZMod (Dd d).natAbs) = genusCharFun s (p : ℤ) := by
    rw [← fundamentalDiscriminantChar_apply_int (isFD hsf) hs hprod (p : ℤ)]
    simp
  rw [hval]
  by_cases h2 : p = 2
  · subst h2
    have hd4 : d % 4 = 1 :=
      (two_not_dvd_fundamentalDiscriminant_iff_mod_four_eq_one d).1 (by exact_mod_cast hpD)
    have hDd : Dd d = d := by rw [Dd, fundamentalDiscriminant_def, if_pos hd4]
    have hncard := NumberField.ncard_primesOver_two_of_mod_four_eq_one hmin hgen hd4
    have hg2 : genusCharFun s ((2 : ℕ) : ℤ) = ZMod.χ₈ (d : ZMod 8) := by
      rw [genusCharFun_def]
      calc ∏ P ∈ s, primeDiscriminantCharFun P ((2 : ℕ) : ℤ)
          = ∏ P ∈ s, ZMod.χ₈ (P : ZMod 8) :=
            Finset.prod_congr rfl fun P hP => by
              rw [show ((2 : ℕ) : ℤ) = 2 by norm_num]; exact primeDiscriminantCharFun_two (hs P hP)
        _ = ZMod.χ₈ ((∏ P ∈ s, P : ℤ) : ZMod 8) := by rw [Int.cast_prod, map_prod]
        _ = ZMod.χ₈ (d : ZMod 8) := by rw [hprod, hDd]
    rw [show (PO K 2) = (span {((2 : ℕ) : ℤ)} : Ideal ℤ).primesOver (𝓞 K) from rfl] at *
    simp only [Nat.cast_ofNat] at hncard ⊢
    rw [hncard, show ((2 : ℕ) : ℤ) = 2 by norm_num] at *
    rw [hg2, ZMod.χ₈_int_eq_if_mod_eight]
    have h8 : d % 8 = 1 ∨ d % 8 = 5 := by omega
    rcases h8 with h8 | h8 <;> simp [h8] <;> omega
  · have hcop : ¬ (p : ℤ) ∣ d := by
      intro hd
      obtain ⟨c, _, hcd⟩ := exists_sq_mul_eq_fundamentalDiscriminant d
      exact hpD (by rw [Dd, ← hcd]; exact Dvd.dvd.mul_left hd _)
    rw [genusCharFun_natCast_eq_legendreSym hs hprod h2, ← hfin]
    exact NumberField.ncard_primesOver_quadratic_iff hmin hgen h2 hcop

/-- **Ideals of prime-power norm in a quadratic field.** -/
theorem mult_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (BernoulliRegular.idealNormMultiplicity K (p ^ k) : ℂ) =
      ∑ i ∈ Finset.range (k + 1), (chi d hsf (p : ZMod (Dd d).natAbs)) ^ i := by
  classical
  have hfin : finrank ℚ K = 2 := NumberField.finrank_rat_eq_two hmin hgen
  rw [chi_apply]
  rcases local_cases hfin hp with ⟨hdvd, P, hPO, hN⟩ | ⟨hndvd, P, Q, hPQ, hPO, hNP, hNQ⟩ |
    ⟨hndvd, P, hPO, hN⟩
  · -- ramified
    rw [discr_eq hmin hgen hsf] at hdvd
    rw [chiZ_eq_zero_of_dvd hsf hp hdvd]
    have hS : ∀ I, I ∈ ({P} : Finset (Ideal (𝓞 K))) ↔ I ∈ PO K p := by
      intro I; rw [hPO]; simp
    have hNS : ∀ I ∈ ({P} : Finset (Ideal (𝓞 K))), absNorm I = p ^ 1 := by
      intro I hI; rw [Finset.mem_singleton.1 hI, hN, pow_one]
    have := mult_pow_eq_card_sym hp {P} hS hNS one_pos k
    rw [one_mul] at this
    rw [this, Sym.card_sym_eq_choose, Fintype.card_coe, Finset.card_singleton,
      Finset.sum_range_succ']
    simp
  · -- split
    rw [discr_eq hmin hgen hsf] at hndvd
    have hc : (PO K p).ncard = 2 := by rw [hPO]; exact Set.ncard_pair hPQ
    rw [(ncard_eq_two_iff hmin hgen hsf hp hndvd).1 hc]
    have hS : ∀ I, I ∈ ({P, Q} : Finset (Ideal (𝓞 K))) ↔ I ∈ PO K p := by
      intro I; rw [hPO]; simp
    have hNS : ∀ I ∈ ({P, Q} : Finset (Ideal (𝓞 K))), absNorm I = p ^ 1 := by
      intro I hI
      rcases Finset.mem_insert.1 hI with h | h
      · rw [h, hNP, pow_one]
      · rw [Finset.mem_singleton.1 h, hNQ, pow_one]
    have := mult_pow_eq_card_sym hp {P, Q} hS hNS one_pos k
    rw [one_mul] at this
    rw [this, Sym.card_sym_eq_choose, Fintype.card_coe, Finset.card_pair hPQ]
    simp only [Int.cast_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [show 2 + k - 1 = k + 1 by omega, Nat.choose_succ_self_right]
  · -- inert
    rw [discr_eq hmin hgen hsf] at hndvd
    have hc : (PO K p).ncard ≠ 2 := by rw [hPO, Set.ncard_singleton]; norm_num
    have hm1 : chiZ d hsf (p : ZMod (Dd d).natAbs) = -1 := by
      rcases chiZ_pm_one hsf hp hndvd with h | h
      · exact absurd ((ncard_eq_two_iff hmin hgen hsf hp hndvd).2 h) hc
      · exact h
    rw [hm1]
    have hS : ∀ I, I ∈ ({P} : Finset (Ideal (𝓞 K))) ↔ I ∈ PO K p := by
      intro I; rw [hPO]; simp
    have hNS : ∀ I ∈ ({P} : Finset (Ideal (𝓞 K))), absNorm I = p ^ 2 := by
      intro I hI; rw [Finset.mem_singleton.1 hI, hN]
    -- `∑_{i ≤ k} (-1)^i` is `1` for even `k` and `0` for odd `k`
    have hsum : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), ((-1 : ℤ) : ℂ) ^ i =
        if 2 ∣ k then 1 else 0 := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · have h1 : 2 ∣ k := ⟨j, by omega⟩
          have h2 : ¬ 2 ∣ k + 1 := by omega
          rw [if_pos h1, if_neg h2, hj, show j + j + 1 = 2 * j + 1 by ring, pow_succ, pow_mul]
          simp
        · have h1 : ¬ 2 ∣ k := by omega
          have h2 : 2 ∣ k + 1 := ⟨j + 1, by omega⟩
          rw [if_neg h1, if_pos h2, hj, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]
          simp
    rw [hsum k]
    split_ifs with h2k
    · obtain ⟨n, rfl⟩ := h2k
      rw [mult_pow_eq_card_sym hp {P} hS hNS two_pos n, Sym.card_sym_eq_choose, Fintype.card_coe,
        Finset.card_singleton]
      simp
    · rw [mult_pow_eq_zero hp {P} hS hNS h2k]
      simp

omit hmin hgen in
/-- `L(s, χ_D)`. -/
noncomputable def Lchi (d : ℤ) (hsf : Squarefree d) (s : ℂ) : ℂ :=
  haveI := neZero_Dd hsf
  DirichletCharacter.LFunction (chi d hsf) s

/-! ### The arithmetic functions -/

omit hmin hgen hsf in
/-- `n ↦ #{I : N I = n}` as an arithmetic function. -/
noncomputable def multA (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℂ :=
  ⟨fun n => (BernoulliRegular.idealNormMultiplicity K n : ℂ), by
    simp [BernoulliRegular.idealNormMultiplicity_zero]⟩

omit hmin hgen hsf in
theorem multA_apply (n : ℕ) : multA K n = (BernoulliRegular.idealNormMultiplicity K n : ℂ) := rfl

omit hmin hgen hsf in
theorem multA_isMultiplicative : (multA K).IsMultiplicative := by
  refine ⟨by simp [multA_apply, BernoulliRegular.idealNormMultiplicity_one], fun {m n} hmn => ?_⟩
  simp only [multA_apply]
  rw [BernoulliRegular.idealNormMultiplicity_mul K hmn]
  push_cast; rfl

omit hmin hgen in
/-- `χ_D` as an arithmetic function. -/
noncomputable def chiA (d : ℤ) (hsf : Squarefree d) : ArithmeticFunction ℂ :=
  toArithmeticFunction (fun n => chi d hsf n)

omit hmin hgen in
theorem chiA_apply {n : ℕ} (hn : n ≠ 0) : chiA d hsf n = chi d hsf n := by
  simp [chiA, toArithmeticFunction, hn]

omit hmin hgen in
theorem chiA_isMultiplicative : (chiA d hsf).IsMultiplicative := by
  refine ⟨by rw [chiA_apply hsf one_ne_zero]; simp, fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [chiA, toArithmeticFunction]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [chiA, toArithmeticFunction]
  rw [chiA_apply hsf (Nat.mul_ne_zero hm.ne' hn.ne'), chiA_apply hsf hm.ne',
    chiA_apply hsf hn.ne', Nat.cast_mul, map_mul]

/-- **`#{I : N I = n} = ∑_{m ∣ n} χ_D(m)`.** -/
theorem multA_eq : multA K = (ζ : ArithmeticFunction ℂ) * chiA d hsf := by
  have hmul : ((ζ : ArithmeticFunction ℂ) * chiA d hsf).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul (chiA_isMultiplicative hsf)
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ multA_isMultiplicative
    _ hmul).2 fun p k hp => ?_
  rw [multA_apply, mult_prime_pow hmin hgen hsf hp k, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chiA_apply hsf (pow_ne_zero _ hp.ne_zero), Nat.cast_pow, map_pow]

/-- **`ζ_K(s) = ζ(s) L(s, χ_D)` for `Re s > 1`.** -/
theorem dedekindZeta_eq {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = riemannZeta s * Lchi d hsf s := by
  haveI := neZero_Dd hsf
  rw [Lchi]
  have h1 : NumberField.dedekindZeta K s = LSeries (fun n => multA K n) s := by
    rw [BernoulliRegular.dedekindZeta_eq_tsum_idealNormMultiplicity K hs, LSeries]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, multA_apply, BernoulliRegular.idealNormMultiplicity_zero]
    · rw [LSeries.term_of_ne_zero hn.ne', multA_apply, Complex.cpow_neg, div_eq_mul_inv]
  have hz : LSeriesSummable (fun n => (ζ : ArithmeticFunction ℂ) n) s := by
    refine (LSeriesSummable_congr s fun {n} hn => ?_).1
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
    simp [ArithmeticFunction.natCoe_apply]
  have hc : LSeriesSummable (fun n => chiA d hsf n) s := by
    refine (LSeriesSummable_congr s fun {n} hn => ?_).2
      (DirichletCharacter.LSeriesSummable_of_one_lt_re (chi d hsf) hs)
    exact chiA_apply hsf hn
  rw [h1, multA_eq hmin hgen hsf, ArithmeticFunction.LSeries_mul' hz hc,
    DirichletCharacter.LFunction_eq_LSeries _ hs]
  congr 1
  · rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
    exact LSeries_congr (fun {n} hn => by simp [ArithmeticFunction.natCoe_apply]) s
  · exact LSeries_congr (fun {n} hn => chiA_apply hsf hn) s

end B4.CNF
