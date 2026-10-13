/-
B-4, class number formula, part 1 (2026-10-10): local structure of a rational prime in a quadratic
field, and the number of integral ideals of norm `p ^ k`.

* `local_cases`: for a quadratic field `K` and a prime `p`, either `p` ramifies (one prime above it,
  of norm `p`), or it splits (two distinct primes, each of norm `p`), or it is inert (one prime, of
  norm `p ^ 2`); the last two happen exactly when `p ∤ disc K`. The argument is the fundamental
  identity `∑ e f = 2` (Mathlib `Ideal.sum_ramification_inertia_eq_finrank`), as in TauCeti's
  `NumberField.Quadratic.TotalRamification`, which we do not import (it does not compile against
  the pinned Mathlib).
* `mult_pow_eq_zero`, `mult_pow_eq_card_sym`: if every prime above `p` has norm `p ^ f`, the ideals
  of norm `p ^ k` are the products of `k / f` primes above `p` (zero of them if `f ∤ k`). This is
  AINTLIB's cyclotomic argument (`BernoulliRegular.ZetaFactorisation.EulerProduct`,
  `idealNormMultiplicity_prime_pow_mul_localResidueDegree_eq_card_sym`) with the cyclotomic
  hypotheses replaced by the norm hypothesis; AINTLIB's version cannot be applied directly since it
  carries an `IsCyclotomicExtension` instance.
-/
import Mathlib
import BernoulliRegular.NumberFieldEulerProduct

open Ideal Module
open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace B4.CNF

variable {K : Type*} [Field K] [NumberField K]

/-- The primes of `𝓞 K` above the rational prime `p`. -/
abbrev PO (K : Type*) [Field K] [NumberField K] (p : ℕ) : Set (Ideal (𝓞 K)) :=
  (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)

theorem span_isMaximal {p : ℕ} (hp : p.Prime) : (span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
  haveI := Fact.mk hp
  Int.ideal_span_isMaximal_of_prime p

/-- The fundamental identity for a quadratic field. -/
theorem sum_e_f (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    haveI := span_isMaximal hp
    ∑ q : PO K p, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 2 := by
  haveI := span_isMaximal hp
  rw [Ideal.sum_ramification_inertia_eq_finrank, NumberField.RingOfIntegers.rank K, hK]

theorem absNorm_of_mem {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ PO K p) :
    absNorm P = p ^ P.inertiaDeg ℤ := by
  haveI : P.IsPrime := hP.1
  haveI : P.LiesOver (span {(p : ℤ)}) := hP.2
  rw [← Ideal.natAbs_pow_inertiaDeg (p : ℤ) P, Int.natAbs_natCast]

theorem e_pos {p : ℕ} (q : PO K p) : 0 < q.1.ramificationIdx ℤ := by
  haveI : q.1.IsPrime := q.2.1
  exact Ideal.ramificationIdx_pos (R := ℤ) (q := q.1)

theorem f_pos {p : ℕ} (q : PO K p) : 0 < q.1.inertiaDeg ℤ := by
  haveI : q.1.IsPrime := q.2.1
  haveI : q.1.LiesOver (span {(p : ℤ)}) := q.2.2
  exact Ideal.inertiaDeg_pos q.1 ℤ

/-- **Local structure of a rational prime in a quadratic field.** -/
theorem local_cases (hK : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    ((p : ℤ) ∣ NumberField.discr K ∧ ∃ P, PO K p = {P} ∧ absNorm P = p) ∨
    (¬ (p : ℤ) ∣ NumberField.discr K ∧ ∃ P Q, P ≠ Q ∧ PO K p = {P, Q} ∧ absNorm P = p ∧ absNorm Q = p) ∨
    (¬ (p : ℤ) ∣ NumberField.discr K ∧ ∃ P, PO K p = {P} ∧ absNorm P = p ^ 2) := by
  classical
  haveI := span_isMaximal hp
  have hsum := sum_e_f hK hp
  by_cases hdvd : (p : ℤ) ∣ NumberField.discr K
  · -- ramified: some prime above `p` has `e ≠ 1`
    left
    refine ⟨hdvd, ?_⟩
    have hnot : ¬ Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := by
      rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)]
      exact not_not.mpr hdvd
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one] at hnot
    push_neg at hnot
    obtain ⟨𝔭, h𝔭, hlo, hne⟩ := hnot
    set x : PO K p := ⟨𝔭, h𝔭, hlo⟩ with hx
    have he : 2 ≤ 𝔭.ramificationIdx ℤ := by
      have := e_pos x
      simp only [hx] at this
      omega
    have hf := f_pos x
    simp only [hx] at hf
    have htwo : 2 ≤ 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ :=
      le_trans (by omega) (Nat.mul_le_mul he hf)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at hsum
    have hxv : x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ = 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ :=
      rfl
    have hrest : ∑ q ∈ Finset.univ.erase x, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 0 := by
      omega
    have hxval : 𝔭.ramificationIdx ℤ * 𝔭.inertiaDeg ℤ = 2 := by omega
    have hfone : 𝔭.inertiaDeg ℤ = 1 := by
      rcases Nat.lt_or_ge (𝔭.inertiaDeg ℤ) 2 with h | h
      · omega
      · nlinarith
    have huniq : ∀ q : PO K p, q = x := fun q => by
      by_contra hne'
      exact absurd ((Finset.sum_eq_zero_iff.mp hrest) q
          (Finset.mem_erase.mpr ⟨hne', Finset.mem_univ q⟩))
        (Nat.mul_ne_zero (e_pos q).ne' (f_pos q).ne')
    refine ⟨𝔭, ?_, ?_⟩
    · ext P
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hP
        exact congrArg Subtype.val (huniq ⟨P, hP⟩)
      · rintro rfl
        exact ⟨h𝔭, hlo⟩
    · rw [absNorm_of_mem hp ⟨h𝔭, hlo⟩, hfone, pow_one]
  · -- unramified: all `e = 1`, so `∑ f = 2`
    right
    have hunr : Algebra.IsUnramifiedIn (𝓞 K) (span {(p : ℤ)}) := by
      rw [← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)]
      exact hdvd
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one] at hunr
    have he1 : ∀ q : PO K p, q.1.ramificationIdx ℤ = 1 := fun q => by
      haveI : q.1.IsPrime := q.2.1
      exact hunr q.1 q.2.2
    simp only [he1, one_mul] at hsum
    -- every `f ≥ 1`, so there are at most two primes
    have hcard_le : (Finset.univ : Finset (PO K p)).card ≤ 2 := by
      calc (Finset.univ : Finset (PO K p)).card = ∑ _q : PO K p, 1 := by simp
        _ ≤ ∑ q : PO K p, q.1.inertiaDeg ℤ := Finset.sum_le_sum fun q _ => f_pos q
        _ = 2 := hsum
    have hne : (Finset.univ : Finset (PO K p)).Nonempty := Finset.univ_nonempty (α := PO K p)
    have hcard_pos := hne.card_pos
    interval_cases hc : (Finset.univ : Finset (PO K p)).card
    · -- one prime, `f = 2`
      right
      refine ⟨hdvd, ?_⟩
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
      have hsum' := hsum
      rw [hx, Finset.sum_singleton] at hsum'
      refine ⟨x.1, ?_, ?_⟩
      · ext P
        simp only [Set.mem_singleton_iff]
        constructor
        · intro hP
          have : (⟨P, hP⟩ : PO K p) ∈ (Finset.univ : Finset (PO K p)) := Finset.mem_univ _
          rw [hx, Finset.mem_singleton] at this
          exact congrArg Subtype.val this
        · rintro rfl
          exact x.2
      · rw [absNorm_of_mem hp x.2, hsum']
    · -- two primes, `f = 1` each
      left
      refine ⟨hdvd, ?_⟩
      obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp hc
      have hsum' := hsum
      rw [hxy', Finset.sum_pair hxy] at hsum'
      have hfx := f_pos x
      have hfy := f_pos y
      have hx1 : x.1.inertiaDeg ℤ = 1 := by omega
      have hy1 : y.1.inertiaDeg ℤ = 1 := by omega
      refine ⟨x.1, y.1, fun h => hxy (Subtype.ext h), ?_, ?_, ?_⟩
      · ext P
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hP
          have : (⟨P, hP⟩ : PO K p) ∈ (Finset.univ : Finset (PO K p)) := Finset.mem_univ _
          rw [hxy', Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h
          · exact Or.inl (congrArg Subtype.val h)
          · exact Or.inr (congrArg Subtype.val h)
        · rintro (rfl | rfl)
          · exact x.2
          · exact y.2
      · rw [absNorm_of_mem hp x.2, hx1, pow_one]
      · rw [absNorm_of_mem hp y.2, hy1, pow_one]

/-! ### Ideals of prime-power norm -/

/-- A prime factor of an ideal of norm `p ^ k` lies above `p`. (AINTLIB,
`normalizedFactors_subset_primesOverFinset_of_absNorm_prime_pow`.) -/
theorem mem_PO_of_mem_factors {p : ℕ} (hp : p.Prime) {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥) {k : ℕ}
    (hI_norm : absNorm I = p ^ k) {P : Ideal (𝓞 K)}
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : P ∈ PO K p := by
  have hP_fac := (Ideal.mem_normalizedFactors_iff hI_ne).1 hP
  have hP_prime : P.IsPrime := hP_fac.1
  have hI_le_P : I ≤ P := hP_fac.2
  have hP_ne : P ≠ ⊥ := fun hP_bot => hI_ne (le_bot_iff.mp (hP_bot ▸ hI_le_P))
  letI : NeZero P := ⟨hP_ne⟩
  have hP_dvd : absNorm P ∣ p ^ k := by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_P
  have hunder_dvd : absNorm (Ideal.under ℤ P) ∣ p ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm P) hP_dvd
  have hunder_prime : (absNorm (Ideal.under ℤ P)).Prime := Nat.absNorm_under_prime P
  have hunder_eq : absNorm (Ideal.under ℤ P) = p :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime hp).1 (hunder_prime.dvd_of_dvd_pow hunder_dvd)
  have hunder_span : Ideal.under ℤ P = span {((p : ℕ) : ℤ)} := by
    calc Ideal.under ℤ P = span {(absNorm (Ideal.under ℤ P) : ℤ)} :=
          (Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P)).symm
      _ = span {((p : ℕ) : ℤ)} := by rw [hunder_eq]
  exact ⟨hP_prime, by rw [Ideal.liesOver_iff, hunder_span]⟩

variable {p : ℕ} (hp : p.Prime) {f : ℕ} (S : Finset (Ideal (𝓞 K)))
  (hS : ∀ P, P ∈ S ↔ P ∈ PO K p) (hN : ∀ P ∈ S, absNorm P = p ^ f)
include hp hS hN

theorem prime_of_mem_S {P : Ideal (𝓞 K)} (hP : P ∈ S) : Prime P := by
  have hP_ne : P ≠ ⊥ := by
    intro h
    have := hN P hP
    rw [h, Ideal.absNorm_bot] at this
    exact pow_ne_zero _ hp.ne_zero this.symm
  exact (Ideal.prime_iff_isPrime hP_ne).2 ((hS P).1 hP).1

theorem absNorm_prod_of_subset {m : Multiset (Ideal (𝓞 K))} (hm : m.toFinset ⊆ S) :
    absNorm m.prod = p ^ (f * Multiset.card m) := by
  classical
  have hsum_count : ∑ P ∈ S, m.count P = Multiset.card m :=
    Multiset.sum_count_eq_card fun P hP => hm (Multiset.mem_toFinset.2 hP)
  rw [Finset.prod_multiset_count_of_subset m S hm, map_prod]
  calc ∏ P ∈ S, absNorm (P ^ m.count P) = ∏ P ∈ S, (p ^ f) ^ m.count P := by
        refine Finset.prod_congr rfl fun P hP => ?_
        rw [map_pow, hN P hP]
    _ = p ^ (f * ∑ P ∈ S, m.count P) := by
        rw [Finset.prod_pow_eq_pow_sum]; simp only [Nat.pow_mul]
    _ = p ^ (f * Multiset.card m) := by rw [hsum_count]

theorem card_factors_of_norm {I : Ideal (𝓞 K)} (hI_ne : I ≠ ⊥) {k : ℕ}
    (hI_norm : absNorm I = p ^ k) :
    f * Multiset.card (UniqueFactorizationMonoid.normalizedFactors I) = k := by
  classical
  set m := UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsub : m.toFinset ⊆ S := fun P hP =>
    (hS P).2 (mem_PO_of_mem_factors hp hI_ne hI_norm (Multiset.mem_toFinset.1 hP))
  have hpow : p ^ (f * Multiset.card m) = p ^ k := by
    calc p ^ (f * Multiset.card m) = absNorm m.prod :=
          (absNorm_prod_of_subset hp S hS hN hsub).symm
      _ = absNorm I := by rw [hm, Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = p ^ k := hI_norm
  exact Nat.pow_right_injective hp.two_le hpow

/-- No ideal has norm `p ^ k` when `f ∤ k`. -/
theorem mult_pow_eq_zero {k : ℕ} (hk : ¬ f ∣ k) :
    BernoulliRegular.idealNormMultiplicity K (p ^ k) = 0 := by
  simp only [BernoulliRegular.idealNormMultiplicity]
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  exact hk ⟨_, (card_factors_of_norm hp S hS hN hI_ne hI_norm).symm⟩

/-- The ideals of norm `p ^ (f n)` are the products of `n` primes above `p`. -/
theorem mult_pow_eq_card_sym (hf : 0 < f) (n : ℕ) :
    BernoulliRegular.idealNormMultiplicity K (p ^ (f * n)) =
      Fintype.card (Sym {P : Ideal (𝓞 K) // P ∈ S} n) := by
  classical
  let α : Type _ := {P : Ideal (𝓞 K) // P ∈ S}
  let β : Type _ := {I : BernoulliRegular.NonzeroIdeal K // absNorm I.1 = p ^ (f * n)}
  let toSym : β → Sym α n := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ P, P ∈ m → P ∈ S := fun P hP =>
      (hS P).2 (mem_PO_of_mem_factors hp hI_ne hI_norm hP)
    have hm_card : Multiset.card m = n := by
      have hmul : f * Multiset.card m = f * n := card_factors_of_norm hp S hS hN hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hf hmul
    ⟨Multiset.pmap (fun P hP => (⟨P, hP⟩ : α)) m H, by
      simpa only [Multiset.card_pmap] using hm_card⟩
  let ofSym : Sym α n → β := fun s =>
    let m : Multiset (Ideal (𝓞 K)) := s.1.map Subtype.val
    have hm_card : Multiset.card m = n := by
      change Multiset.card (s.1.map Subtype.val) = n
      rw [Multiset.card_map]
      exact s.2
    have hm_subset : m.toFinset ⊆ S := by
      intro P hP
      rcases Multiset.mem_map.1 (Multiset.mem_toFinset.1 hP) with ⟨Q, _, rfl⟩
      exact Q.2
    have hm_prime : ∀ P ∈ m, Prime P := by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q, _, rfl⟩
      exact prime_of_mem_S hp S hS hN Q.2
    have hm_prod_ne : m.prod ≠ ⊥ := Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm : absNorm m.prod = p ^ (f * n) := by
      rw [absNorm_prod_of_subset hp S hS hN hm_subset, hm_card]
    ⟨⟨m.prod, hm_prod_ne⟩, hm_norm⟩
  have htoSym_map_val : ∀ b : β,
      (toSym b).1.map Subtype.val = UniqueFactorizationMonoid.normalizedFactors b.1.1 := by
    rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
    dsimp [toSym]
    rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  have hofSym_nfactors : ∀ s : Sym α n,
      UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val := by
    intro s
    dsimp [ofSym]
    have hm_prime : ∀ P ∈ s.1.map Subtype.val, Prime P := by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q, _, rfl⟩
      exact prime_of_mem_S hp S hS hN Q.2
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft : Function.LeftInverse ofSym toSym := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val, Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright : Function.RightInverse ofSym toSym := by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  let e : β ≃ Sym α n := ⟨toSym, ofSym, hleft, hright⟩
  simp only [BernoulliRegular.idealNormMultiplicity]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]

end B4.CNF
