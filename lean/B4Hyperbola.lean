/-
B-4, Lemma L1 (elementary version), the hyperbola identity (2026-10-10).
With f(d) = χ(d) d^{-σ}, g(m) = m^{-σ}, F(k) = ∑_{d ≤ k} f(d), G(k) = ∑_{m ≤ k} g(m), and integers
1 ≤ Y ≤ X:
  ∑_{n ≤ X} (f*g)(n) = ∑_{d ≤ Y} f(d) G(X/d) + ∑_{m ≤ X} g(m) (F(X/m) − F(min(Y, X/m)))
(`hyperbola`), obtained by splitting f = f_{≤Y} + f_{>Y} and applying Mathlib's
`sum_Ioc_mul_eq_sum_sum` to f_{≤Y} * g and to g * f_{>Y}. Moreover (f*g)(n) = n^{-σ} (1*χ)(n)
(`fg_apply`), so for a quadratic χ the left side has real part ≥ 1 (`one_le_re_S`).
Build: see README.md.
-/
import B4LSeriesCont

namespace B4

open ArithmeticFunction Finset Complex

variable {q : ℕ} [NeZero q]

/-- an arithmetic function from `ℕ → ℂ` (value 0 at 0) -/
def af (h : ℕ → ℂ) : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else h n, rfl⟩

theorem af_apply (h : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) : af h n = h n := by
  simp [af, hn]

noncomputable def fχ (χ : DirichletCharacter ℂ q) (σ : ℝ) (d : ℕ) : ℂ := χ d * (d : ℂ) ^ (-(σ : ℂ))
noncomputable def gσ (σ : ℝ) (m : ℕ) : ℂ := (m : ℂ) ^ (-(σ : ℂ))

/-- `F(k) = ∑_{1 ≤ d ≤ k} f(d)` -/
noncomputable def Fs (h : ℕ → ℂ) (k : ℕ) : ℂ := ∑ d ∈ Ioc 0 k, h d

theorem sum_Ioc_af (h : ℕ → ℂ) (k : ℕ) : ∑ d ∈ Ioc 0 k, af h d = Fs h k :=
  sum_congr rfl fun d hd => af_apply h (by simp at hd; omega)

/-- **Hyperbola identity.** -/
theorem hyperbola (h g : ℕ → ℂ) {X Y : ℕ} (hYX : Y ≤ X) :
    ∑ n ∈ Ioc 0 X, (af h * af g) n =
      ∑ d ∈ Ioc 0 Y, h d * Fs g (X / d) +
        ∑ m ∈ Ioc 0 X, g m * (Fs h (X / m) - Fs h (min Y (X / m))) := by
  set hle : ℕ → ℂ := fun d => if Y < d then 0 else h d
  set hgt : ℕ → ℂ := fun d => if Y < d then h d else 0
  have hsplit : af h = af hle + af hgt := by
    ext n
    rw [ArithmeticFunction.add_apply]
    show (if n = 0 then 0 else h n) = (if n = 0 then 0 else hle n) + (if n = 0 then 0 else hgt n)
    simp only [hle, hgt]
    split_ifs <;> simp
  rw [hsplit, add_mul]
  simp only [ArithmeticFunction.add_apply]
  rw [sum_add_distrib]
  congr 1
  · -- the part d ≤ Y
    rw [sum_Ioc_mul_eq_sum_sum]
    simp_rw [sum_Ioc_af]
    have : Ioc 0 X = Ioc 0 Y ∪ Ioc Y X := (Ioc_union_Ioc_eq_Ioc (Nat.zero_le Y) hYX).symm
    rw [this, sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    have h2 : ∑ x ∈ Ioc Y X, af hle x * Fs g (X / x) = 0 := by
      refine sum_eq_zero fun d hd => ?_
      simp only [mem_Ioc] at hd
      simp [af, hle, hd.1, show d ≠ 0 by omega]
    rw [h2, add_zero]
    refine sum_congr rfl fun d hd => ?_
    simp only [mem_Ioc] at hd
    rw [af_apply _ (by omega)]
    simp [hle, not_lt.mpr hd.2]
  · -- the part d > Y, summed over m first
    rw [mul_comm (af hgt), sum_Ioc_mul_eq_sum_sum]
    refine sum_congr rfl fun m hm => ?_
    simp only [mem_Ioc] at hm
    rw [af_apply _ (by omega), sum_Ioc_af]
    congr 1
    -- Fs hgt k = Fs h k − Fs h (min Y k)
    set k := X / m
    simp only [Fs, hgt]
    have hk : Ioc 0 k = Ioc 0 (min Y k) ∪ Ioc (min Y k) k :=
      (Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (min_le_right _ _)).symm
    rw [hk, sum_union (Ioc_disjoint_Ioc_of_le le_rfl), sum_union (Ioc_disjoint_Ioc_of_le le_rfl)]
    have e1 : ∑ x ∈ Ioc 0 (min Y k), (if Y < x then h x else 0) = 0 := by
      refine sum_eq_zero fun d hd => ?_
      simp only [mem_Ioc] at hd
      simp [not_lt.mpr (hd.2.trans (min_le_left _ _))]
    have e2 : ∑ x ∈ Ioc (min Y k) k, (if Y < x then h x else 0) = ∑ x ∈ Ioc (min Y k) k, h x := by
      refine sum_congr rfl fun d hd => ?_
      simp only [mem_Ioc] at hd
      have : Y < d := by
        rcases le_total Y k with h' | h'
        · rw [min_eq_left h'] at hd; exact hd.1
        · rw [min_eq_right h'] at hd; omega
      simp [this]
    rw [e1, e2]
    ring

omit [NeZero q] in
/-- `(f*g)(n) = n^{-σ} (1*χ)(n)` -/
theorem fg_apply (χ : DirichletCharacter ℂ q) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (af (fχ χ σ) * af (gσ σ)) n = (n : ℂ) ^ (-(σ : ℂ)) * DirichletCharacter.zetaMul χ n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => af (fχ χ σ) a * af (gσ σ) b)]
  simp only [DirichletCharacter.zetaMul, coe_zeta_mul_apply, mul_sum]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.pos_of_mem_divisors hd |>.ne'
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hq0 : n / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn)
    (Nat.pos_of_ne_zero hd0)).ne'
  rw [af_apply _ hd0, af_apply _ hq0]
  simp only [fχ, gσ, toArithmeticFunction, coe_mk, hd0, ite_false]
  have : (n : ℂ) ^ (-(σ : ℂ)) = (d : ℂ) ^ (-(σ : ℂ)) * ((n / d : ℕ) : ℂ) ^ (-(σ : ℂ)) := by
    rw [← natCast_mul_natCast_cpow]; congr 2; exact_mod_cast (Nat.mul_div_cancel' hdn).symm
  rw [this]; ring

omit [NeZero q] in
/-- `Re S ≥ 1` for a quadratic character. -/
theorem one_le_re_S (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (σ : ℝ) {X : ℕ} (hX : 1 ≤ X) :
    1 ≤ (∑ n ∈ Ioc 0 X, (af (fχ χ σ) * af (gσ σ)) n).re := by
  rw [re_sum]
  have hterm : ∀ n ∈ Ioc 0 X, 0 ≤ ((af (fχ χ σ) * af (gσ σ)) n).re := by
    intro n hn
    simp only [mem_Ioc] at hn
    rw [fg_apply χ σ (by omega)]
    have hz := DirichletCharacter.zetaMul_nonneg hχ2 n
    rw [Complex.nonneg_iff] at hz
    have hc : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; rfl
    rw [hc, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) hz.1
  have h1 : (1 : ℕ) ∈ Ioc 0 X := by simp; omega
  have hone : ((af (fχ χ σ) * af (gσ σ)) 1).re = 1 := by
    rw [fg_apply χ σ one_ne_zero]
    simp only [DirichletCharacter.zetaMul]
    rw [coe_zeta_mul_apply]
    simp [toArithmeticFunction]
  calc (1 : ℝ) = ((af (fχ χ σ) * af (gσ σ)) 1).re := hone.symm
    _ ≤ _ := single_le_sum hterm h1

#print axioms hyperbola
#print axioms one_le_re_S

end B4
