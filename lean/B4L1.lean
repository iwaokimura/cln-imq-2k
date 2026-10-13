/-
B-4, Lemma L1 (elementary version), assembly (2026-10-10). Lemma 8 of the paper, in the
integer form used for the formalization: for a real primitive... (any real nontrivial) character χ
mod q with χ² = 1, 1/2 ≤ σ < 1, δ = 1 − σ, L(t, χ) ≠ 0 for σ < t < 1, and integers 1 ≤ Y ≤ X:
  1 ≤ (X^δ/δ) · L(1, χ) + Err,
  Err = q (Y+1)^{-σ} (t^δ/δ + 4 t^{-σ}) + (X^δ/δ) q/(Y+1) + 4 Y X^{-σ} + q X^δ / Y,   t = X/Y.
(The paper states Lemma 8 in this form, with z = X/Y in place of t.)
Build: see README.md.
-/
import B4ZetaEM
import B4Sign
import B4Hyperbola

namespace B4

open Complex Finset

variable {q : ℕ} [NeZero q]

/-! ### Conversions between the `Ioc 0 k` sums and the `range k` sums -/

theorem sum_Ioc_eq_sum_range (h : ℕ → ℂ) (k : ℕ) :
    ∑ d ∈ Ioc 0 k, h d = ∑ n ∈ range k, h (n + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [sum_Ioc_succ_top (Nat.zero_le k), ih, sum_range_succ]

theorem Fs_gσ (σ : ℝ) (k : ℕ) : Fs (gσ σ) k = ((Zs σ k : ℝ) : ℂ) := by
  rw [Fs, sum_Ioc_eq_sum_range, Zs]
  push_cast
  refine sum_congr rfl fun n _ => ?_
  simp only [gσ]
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

theorem tail_Fs (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    ‖DirichletCharacter.LFunction χ σ - Fs (fχ χ σ) k‖ ≤ q * ((k : ℝ) + 1) ^ (-σ) := by
  have h := LFunction_sub_partial_le_q χ hχ hσ k
  have e : Fs (fχ χ σ) k =
      ∑ n ∈ range k, χ ((n + 1 : ℕ) : ZMod q) * ((n : ℂ) + 1) ^ (-(σ : ℂ)) := by
    rw [Fs, sum_Ioc_eq_sum_range]
    refine sum_congr rfl fun n _ => ?_
    simp only [fχ]
    push_cast; ring_nf
  rw [e]; exact h

/-! ### Real-variable facts -/

theorem rpow_mul_div_rpow {σ X d : ℝ} (hX : 0 < X) (hd : 0 < d) :
    d ^ (-σ) * (X / d) ^ (-σ) = X ^ (-σ) := by
  rw [Real.div_rpow hX.le hd.le, ← mul_div_assoc, mul_comm, mul_div_assoc,
    div_self (Real.rpow_pos_of_pos hd _).ne', mul_one]

theorem rpow_mul_div_rpow' {σ X d : ℝ} (hX : 0 < X) (hd : 0 < d) :
    d ^ (-σ) * (X / d) ^ (1 - σ) = X ^ (1 - σ) / d := by
  rw [Real.div_rpow hX.le hd.le]
  have : d ^ (1 - σ) = d * d ^ (-σ) := by
    rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hd, Real.rpow_one]
  rw [this]
  field_simp

omit [NeZero q] in
theorem norm_fχ_le (χ : DirichletCharacter ℂ q) (σ : ℝ) {d : ℕ} (hd : 0 < d) :
    ‖fχ χ σ d‖ ≤ (d : ℝ) ^ (-σ) := by
  simp only [fχ, norm_mul]
  rw [norm_natCast_cpow_of_pos hd]
  simp only [neg_re, ofReal_re]
  calc ‖χ d‖ * (d : ℝ) ^ (-σ) ≤ 1 * (d : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
    _ = _ := one_mul _

/-! ### The part `A = ∑_{d ≤ Y} f(d) G(X/d)` -/

omit [NeZero q] in
/-- `‖A − ζ(σ) F_σ(Y) − (X^δ/δ) F_1(Y)‖ ≤ 4 Y X^{-σ}` -/
theorem A_bound (χ : DirichletCharacter ℂ q) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {X Y : ℕ}
    (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    ‖∑ d ∈ Ioc 0 Y, fχ χ σ d * Fs (gσ σ) (X / d) -
        (((riemannZeta σ).re : ℝ) : ℂ) * Fs (fχ χ σ) Y -
        ((((X : ℝ) ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) * Fs (fχ χ 1) Y‖ ≤
      4 * Y * (X : ℝ) ^ (-σ) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hd1 : (0 : ℝ) < 1 - σ := by linarith
  have hsplit : ∑ d ∈ Ioc 0 Y, fχ χ σ d * Fs (gσ σ) (X / d) -
        (((riemannZeta σ).re : ℝ) : ℂ) * Fs (fχ χ σ) Y -
        ((((X : ℝ) ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) * Fs (fχ χ 1) Y =
      ∑ d ∈ Ioc 0 Y, (fχ χ σ d * Fs (gσ σ) (X / d) - (((riemannZeta σ).re : ℝ) : ℂ) * fχ χ σ d -
        ((((X : ℝ) ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) * fχ χ 1 d) := by
    rw [sum_sub_distrib, sum_sub_distrib, Fs, Fs, mul_sum, mul_sum]
  rw [hsplit]
  -- each term
  have hterm : ∀ d ∈ Ioc 0 Y,
      ‖fχ χ σ d * Fs (gσ σ) (X / d) - (((riemannZeta σ).re : ℝ) : ℂ) * fχ χ σ d -
        ((((X : ℝ) ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) * fχ χ 1 d‖ ≤ 4 * (X : ℝ) ^ (-σ) := by
    intro d hd
    simp only [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    set t : ℝ := (X : ℝ) / d
    have ht1 : 1 ≤ t := by
      rw [le_div_iff₀ hd0, one_mul]; exact_mod_cast hd.2.trans hYX
    have hfl : ⌊t⌋₊ = X / d := Nat.floor_div_eq_div X d
    have hEM := zeta_EM_real h0 h1 ht1
    rw [hfl] at hEM
    -- fχ 1 d = fχ σ d * d^{-(1-σ)} ... use: fχ σ d * (t^δ/δ) = (X^δ/δ) * fχ 1 d
    have hkey : fχ χ σ d * (((t ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) =
        ((((X : ℝ) ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) * fχ χ 1 d := by
      simp only [fχ]
      have hc1 : (d : ℂ) ^ (-(σ : ℂ)) = (((d : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg d)]; push_cast; rfl
      have hc2 : (d : ℂ) ^ (-((1 : ℝ) : ℂ)) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
        push_cast; rw [Complex.cpow_neg_one]
      rw [hc1, hc2]
      have := rpow_mul_div_rpow' (σ := σ) hX0 hd0
      have e : ((d : ℝ) ^ (-σ) * (t ^ (1 - σ) / (1 - σ))) = (X : ℝ) ^ (1 - σ) / (1 - σ) * (d : ℝ)⁻¹ := by
        rw [mul_div_assoc', this]; field_simp
      calc χ d * (((d : ℝ) ^ (-σ) : ℝ) : ℂ) * (((t ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ)
          = χ d * ((((d : ℝ) ^ (-σ) * (t ^ (1 - σ) / (1 - σ))) : ℝ) : ℂ) := by push_cast; ring
        _ = _ := by rw [e]; push_cast; ring
    have hdiff : fχ χ σ d * Fs (gσ σ) (X / d) - (((riemannZeta σ).re : ℝ) : ℂ) * fχ χ σ d -
        ((((X : ℝ) ^ (1 - σ) / (1 - σ)) : ℝ) : ℂ) * fχ χ 1 d =
        fχ χ σ d * (((Zs σ (X / d) - (riemannZeta σ).re - t ^ (1 - σ) / (1 - σ) : ℝ)) : ℂ) := by
      rw [Fs_gσ, ← hkey]; push_cast; ring
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖fχ χ σ d‖ * |Zs σ (X / d) - (riemannZeta σ).re - t ^ (1 - σ) / (1 - σ)|
        ≤ (d : ℝ) ^ (-σ) * (4 * t ^ (-σ)) :=
          mul_le_mul (norm_fχ_le χ σ hd.1) hEM (abs_nonneg _) (by positivity)
      _ = 4 * (X : ℝ) ^ (-σ) := by
          rw [show (d : ℝ) ^ (-σ) * (4 * t ^ (-σ)) = 4 * ((d : ℝ) ^ (-σ) * t ^ (-σ)) by ring,
            rpow_mul_div_rpow hX0 hd0]
  calc _ ≤ ∑ d ∈ Ioc 0 Y, 4 * (X : ℝ) ^ (-σ) := (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = 4 * Y * (X : ℝ) ^ (-σ) := by simp; ring

#print axioms A_bound

/-! ### The part `B = ∑_{m ≤ X} g(m) (F(X/m) − F(min(Y, X/m)))` -/

/-- with `R(k) = L(σ) − F(k)`: `B = R(Y) G(X/Y) − ∑_{m ≤ X/Y} g(m) R(X/m)` -/
theorem B_eq (χ : DirichletCharacter ℂ q) (σ : ℝ) {X Y : ℕ} (hY : 1 ≤ Y) :
    ∑ m ∈ Ioc 0 X, gσ σ m * (Fs (fχ χ σ) (X / m) - Fs (fχ χ σ) (min Y (X / m))) =
      (DirichletCharacter.LFunction χ σ - Fs (fχ χ σ) Y) * Fs (gσ σ) (X / Y) -
        ∑ m ∈ Ioc 0 (X / Y), gσ σ m *
          (DirichletCharacter.LFunction χ σ - Fs (fχ χ σ) (X / m)) := by
  set L := DirichletCharacter.LFunction χ (σ : ℂ)
  have hfilter : (Ioc 0 X).filter (fun m => Y ≤ X / m) = Ioc 0 (X / Y) := by
    ext m
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hm0, _⟩, hm⟩
      refine ⟨hm0, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      rw [Nat.le_div_iff_mul_le hm0] at hm
      linarith
    · rintro ⟨hm0, hm⟩
      rw [Nat.le_div_iff_mul_le (by omega)] at hm
      refine ⟨⟨hm0, ?_⟩, ?_⟩
      · nlinarith
      · rw [Nat.le_div_iff_mul_le hm0]; linarith
  have hterm : ∀ m ∈ Ioc 0 X, gσ σ m * (Fs (fχ χ σ) (X / m) - Fs (fχ χ σ) (min Y (X / m))) =
      if Y ≤ X / m then gσ σ m * ((L - Fs (fχ χ σ) Y) - (L - Fs (fχ χ σ) (X / m))) else 0 := by
    intro m _
    split_ifs with h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right (by omega)]; ring
  rw [sum_congr rfl hterm, ← sum_filter, hfilter,
    show Fs (gσ σ) (X / Y) = ∑ m ∈ Ioc 0 (X / Y), gσ σ m from rfl, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun m _ => by ring

/-- `‖∑_{m ≤ X/Y} g(m) R(X/m)‖ ≤ q X^{1-σ}/Y` -/
theorem B_tail_bound (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {σ : ℝ} (h0 : 0 < σ) {X Y : ℕ}
    (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    ‖∑ m ∈ Ioc 0 (X / Y), gσ σ m * (DirichletCharacter.LFunction χ σ - Fs (fχ χ σ) (X / m))‖ ≤
      q * (X : ℝ) ^ (1 - σ) / Y := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hterm : ∀ m ∈ Ioc 0 (X / Y),
      ‖gσ σ m * (DirichletCharacter.LFunction χ σ - Fs (fχ χ σ) (X / m))‖ ≤ q * (X : ℝ) ^ (-σ) := by
    intro m hm
    simp only [mem_Ioc] at hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm.1
    rw [norm_mul]
    have hg : ‖gσ σ m‖ = (m : ℝ) ^ (-σ) := by
      simp only [gσ]; rw [norm_natCast_cpow_of_pos hm.1]; simp
    rw [hg]
    have ht := tail_Fs χ hχ h0 (X / m)
    -- (X/m : ℕ) + 1 ≥ X/m (real)
    have hfl : (X : ℝ) / m ≤ ((X / m : ℕ) : ℝ) + 1 := by
      have := Nat.lt_floor_add_one ((X : ℝ) / m)
      rw [Nat.floor_div_eq_div] at this
      exact this.le
    have hmono : (((X / m : ℕ) : ℝ) + 1) ^ (-σ) ≤ ((X : ℝ) / m) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hfl (by linarith)
    calc (m : ℝ) ^ (-σ) * ‖DirichletCharacter.LFunction χ σ - Fs (fχ χ σ) (X / m)‖
        ≤ (m : ℝ) ^ (-σ) * (q * ((X : ℝ) / m) ^ (-σ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact ht.trans (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg q))
      _ = q * ((m : ℝ) ^ (-σ) * ((X : ℝ) / m) ^ (-σ)) := by ring
      _ = q * (X : ℝ) ^ (-σ) := by rw [rpow_mul_div_rpow hX0 hm0]
  have hcount : ((X / Y : ℕ) : ℝ) ≤ (X : ℝ) / Y := Nat.cast_div_le
  calc _ ≤ ∑ m ∈ Ioc 0 (X / Y), q * (X : ℝ) ^ (-σ) := (norm_sum_le _ _).trans (sum_le_sum hterm)
    _ = ((X / Y : ℕ) : ℝ) * (q * (X : ℝ) ^ (-σ)) := by simp
    _ ≤ (X : ℝ) / Y * (q * (X : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = q * (X : ℝ) ^ (1 - σ) / Y := by
        have : (X : ℝ) ^ (1 - σ) = X * (X : ℝ) ^ (-σ) := by
          rw [show 1 - σ = 1 + -σ by ring, Real.rpow_add hX0, Real.rpow_one]
        rw [this]; field_simp

/-! ### Lemma L1, elementary version -/

/-- **Lemma L1 (elementary).** -/
theorem L1_elementary (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) (hχ2 : χ ^ 2 = 1) {σ : ℝ} (h0 : 1 / 2 ≤ σ) (h1 : σ < 1)
    (hzf : ∀ t : ℝ, σ < t → t < 1 → DirichletCharacter.LFunction χ t ≠ 0)
    {X Y : ℕ} (hY : 1 ≤ Y) (hYX : Y ≤ X) :
    1 ≤ (X : ℝ) ^ (1 - σ) / (1 - σ) * (DirichletCharacter.LFunction χ 1).re +
      (q * ((Y : ℝ) + 1) ^ (-σ) * (((X : ℝ) / Y) ^ (1 - σ) / (1 - σ) + 4 * ((X : ℝ) / Y) ^ (-σ)) +
        (X : ℝ) ^ (1 - σ) / (1 - σ) * (q * ((Y : ℝ) + 1) ^ (-(1 : ℝ))) +
        4 * Y * (X : ℝ) ^ (-σ) + q * (X : ℝ) ^ (1 - σ) / Y) := by
  have hσ0 : 0 < σ := by linarith
  have hd : 0 < 1 - σ := by linarith
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  set c : ℝ := (X : ℝ) ^ (1 - σ) / (1 - σ) with hc
  have hc0 : 0 ≤ c := by positivity
  set ζr := (riemannZeta σ).re
  set Lσ := DirichletCharacter.LFunction χ (σ : ℂ)
  set L1 := DirichletCharacter.LFunction χ (((1 : ℝ)) : ℂ)
  have hL1 : L1 = DirichletCharacter.LFunction χ 1 := by simp [L1]
  -- S = A + B
  have hS := hyperbola (fχ χ σ) (gσ σ) hYX
  rw [B_eq χ σ hY] at hS
  have hS1 := one_le_re_S χ hχ2 σ (show 1 ≤ X by omega)
  set S := ∑ n ∈ Ioc 0 X, (af (fχ χ σ) * af (gσ σ)) n
  set A := ∑ d ∈ Ioc 0 Y, fχ χ σ d * Fs (gσ σ) (X / d)
  set RY := Lσ - Fs (fχ χ σ) Y
  set R1 := L1 - Fs (fχ χ 1) Y
  set T := ∑ m ∈ Ioc 0 (X / Y), gσ σ m * (Lσ - Fs (fχ χ σ) (X / m))
  -- the decomposition
  have hdecomp : S = (ζr : ℂ) * Lσ + (c : ℂ) * L1 +
      ((A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y) +
        RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ)) - (c : ℂ) * R1 - T) := by
    rw [hS]; simp only [RY, R1]; ring
  -- bounds
  have hA := A_bound χ hσ0 h1 hY hYX
  have hRY : ‖RY‖ ≤ q * ((Y : ℝ) + 1) ^ (-σ) := tail_Fs χ hχ hσ0 Y
  have hR1 : ‖R1‖ ≤ q * ((Y : ℝ) + 1) ^ (-(1 : ℝ)) := tail_Fs χ hχ one_pos Y
  have hT := B_tail_bound χ hχ hσ0 hY hYX
  set t : ℝ := (X : ℝ) / Y
  have ht1 : 1 ≤ t := by rw [le_div_iff₀ hY0, one_mul]; exact_mod_cast hYX
  have hG : ‖Fs (gσ σ) (X / Y) - (ζr : ℂ)‖ ≤ t ^ (1 - σ) / (1 - σ) + 4 * t ^ (-σ) := by
    have hEM := zeta_EM_real hσ0 h1 ht1
    rw [Nat.floor_div_eq_div] at hEM
    rw [Fs_gσ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have : 0 ≤ t ^ (1 - σ) / (1 - σ) := by positivity
    calc |Zs σ (X / Y) - ζr| ≤ |Zs σ (X / Y) - ζr - t ^ (1 - σ) / (1 - σ)| + |t ^ (1 - σ) / (1 - σ)| := by
          have := abs_add_le (Zs σ (X / Y) - ζr - t ^ (1 - σ) / (1 - σ)) (t ^ (1 - σ) / (1 - σ))
          simpa using this
      _ ≤ 4 * t ^ (-σ) + t ^ (1 - σ) / (1 - σ) := by rw [abs_of_nonneg this]; linarith
      _ = _ := by ring
  have herr : ‖(A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y) +
        RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ)) - (c : ℂ) * R1 - T‖ ≤
      q * ((Y : ℝ) + 1) ^ (-σ) * (t ^ (1 - σ) / (1 - σ) + 4 * t ^ (-σ)) +
        c * (q * ((Y : ℝ) + 1) ^ (-(1 : ℝ))) + 4 * Y * (X : ℝ) ^ (-σ) + q * (X : ℝ) ^ (1 - σ) / Y := by
    have e1 : ‖RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ))‖ ≤
        q * ((Y : ℝ) + 1) ^ (-σ) * (t ^ (1 - σ) / (1 - σ) + 4 * t ^ (-σ)) := by
      rw [norm_mul]; exact mul_le_mul hRY hG (norm_nonneg _) (by positivity)
    have e2 : ‖(c : ℂ) * R1‖ ≤ c * (q * ((Y : ℝ) + 1) ^ (-(1 : ℝ))) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
      exact mul_le_mul_of_nonneg_left hR1 hc0
    have hAb : ‖A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y‖ ≤ 4 * Y * (X : ℝ) ^ (-σ) := hA
    calc _ ≤ ‖(A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y) +
            RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ)) - (c : ℂ) * R1‖ + ‖T‖ := norm_sub_le _ _
      _ ≤ ‖(A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y) +
            RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ))‖ + ‖(c : ℂ) * R1‖ + ‖T‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ ‖A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y‖ +
            ‖RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ))‖ + ‖(c : ℂ) * R1‖ + ‖T‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ _ := by linarith
  -- real parts
  have hζ : ζr ≤ 0 := zeta_nonpos h0 h1
  have hLσ : 0 ≤ Lσ.re := LFunction_nonneg_of_zero_free χ hχ hreal hσ0 h1 hzf
  have hre1 : ((ζr : ℂ) * Lσ).re = ζr * Lσ.re := by simp [Complex.mul_re]
  have hre2 : ((c : ℂ) * L1).re = c * L1.re := by simp [Complex.mul_re]
  rw [hdecomp, Complex.add_re, Complex.add_re, hre1, hre2] at hS1
  have hrest := Complex.re_le_norm ((A - (ζr : ℂ) * Fs (fχ χ σ) Y - (c : ℂ) * Fs (fχ χ 1) Y) +
        RY * (Fs (gσ σ) (X / Y) - (ζr : ℂ)) - (c : ℂ) * R1 - T)
  have hprod : ζr * Lσ.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hζ hLσ
  have h3 : L1.re = (DirichletCharacter.LFunction χ 1).re := congrArg Complex.re hL1
  rw [h3] at hS1
  linarith

#print axioms B_eq
#print axioms L1_elementary

end B4
