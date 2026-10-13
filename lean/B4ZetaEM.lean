/-
B-4, Lemma L1 (elementary version), part (a) (2026-10-10): ζ(σ) for 1/2 ≤ σ < 1.
  * `zeta_im_eq_zero`: ζ(σ) is real (Mathlib `riemannZeta_conj`).
  * `zeta_EM_nat`:  |∑_{n ≤ N} n^{-σ} − ζ(σ) − N^{1-σ}/(1-σ)| ≤ N^{-σ}  for integers N ≥ 1, from the
    Euler–Maclaurin representation of PrimeNumberTheoremAnd (`Zeta0EqZeta`):
    ζ(s) = ∑_{n ≤ N} n^{-s} − N^{1-s}/(1-s) − N^{-s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{-s-1} dx.
  * `zeta_nonpos`: ζ(σ) ≤ 0 (N = 1).
  * `zeta_EM_real`: |∑_{n ≤ t} n^{-σ} − ζ(σ) − t^{1-σ}/(1-σ)| ≤ 4 t^{-σ}  for real t ≥ 1
    (the proof of Lemma 8 in the paper has u^{-σ}; the factor 4 comes from N = ⌊t⌋ ≥ t/2 and concavity of t^{1-σ}).
Build: see README.md.
-/
import PrimeNumberTheoremAnd.ZetaBounds

namespace B4

open Complex Finset MeasureTheory Set

/-- ζ(σ) is real for real σ. -/
theorem zeta_im_eq_zero (σ : ℝ) : (riemannZeta (σ : ℂ)).im = 0 := by
  have h := riemannZeta_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- The Euler–Maclaurin remainder integral. -/
theorem norm_EM_integral_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) :
    ‖∫ x in Ioi (N : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)‖ ≤
      (N : ℝ) ^ (-σ) / (2 * σ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hint : IntegrableOn (fun x : ℝ => (1 / 2 : ℝ) * x ^ (-σ - 1)) (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : 0 < x := lt_trans hN0 hx
    rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx0]
    have hnum : ‖((⌊x⌋ : ℂ) + 1 / 2 - x)‖ ≤ 1 / 2 := by
      have : ((⌊x⌋ : ℂ) + 1 / 2 - x) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
    have hre : ((σ : ℂ) + 1).re = σ + 1 := by simp
    rw [hre, div_eq_mul_inv, ← Real.rpow_neg hx0.le, show -(σ + 1) = -σ - 1 by ring]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0]
    rw [show -σ - 1 + 1 = -σ by ring]
    field_simp
    rfl

/-- Euler–Maclaurin at integers. -/
theorem zeta_EM_nat {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 0 < N) :
    ‖(∑ n ∈ range (N + 1), 1 / (n : ℂ) ^ (σ : ℂ)) - riemannZeta σ -
        (N : ℂ) ^ (1 - (σ : ℂ)) / (1 - σ)‖ ≤ (N : ℝ) ^ (-σ) := by
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt h1)
  have hz := Zeta0EqZeta hN (s := σ) (by simpa using h0) hs1
  rw [← hz]
  simp only [riemannZeta0]
  set I := ∫ x in Ioi (N : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ ((σ : ℂ) + 1)
  have hI := norm_EM_integral_le h0 hN
  have heq : (∑ n ∈ range (N + 1), 1 / (n : ℂ) ^ (σ : ℂ)) -
      ((∑ n ∈ range (N + 1), 1 / (n : ℂ) ^ (σ : ℂ)) + (-(N : ℂ) ^ (1 - (σ : ℂ))) / (1 - σ) +
        (-(N : ℂ) ^ (-(σ : ℂ))) / 2 + σ * I) - (N : ℂ) ^ (1 - (σ : ℂ)) / (1 - σ) =
      (N : ℂ) ^ (-(σ : ℂ)) / 2 - σ * I := by ring
  rw [heq]
  have hn : ‖(N : ℂ) ^ (-(σ : ℂ))‖ = (N : ℝ) ^ (-σ) := by
    rw [norm_natCast_cpow_of_pos hN]; simp
  calc ‖(N : ℂ) ^ (-(σ : ℂ)) / 2 - σ * I‖ ≤ ‖(N : ℂ) ^ (-(σ : ℂ)) / 2‖ + ‖(σ : ℂ) * I‖ :=
        norm_sub_le _ _
    _ = (N : ℝ) ^ (-σ) / 2 + σ * ‖I‖ := by
        rw [norm_div, hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]; simp
    _ ≤ (N : ℝ) ^ (-σ) / 2 + σ * ((N : ℝ) ^ (-σ) / (2 * σ)) := by gcongr
    _ = (N : ℝ) ^ (-σ) := by field_simp; ring

#print axioms zeta_EM_nat

/-- `Z(N) = ∑_{1 ≤ n ≤ N} n^{-σ}` (real) -/
noncomputable def Zs (σ : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range N, ((n : ℝ) + 1) ^ (-σ)

theorem Zs_cast {σ : ℝ} (h0 : 0 < σ) (N : ℕ) :
    (∑ n ∈ range (N + 1), 1 / (n : ℂ) ^ (σ : ℂ)) = ((Zs σ N : ℝ) : ℂ) := by
  rw [sum_range_succ', Zs]
  push_cast
  have h0' : (σ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  simp only [Complex.zero_cpow h0', div_zero, add_zero]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_cpow (by positivity), one_div, ← Complex.cpow_neg]
  push_cast; ring_nf

/-- the real Euler–Maclaurin bound at integers -/
theorem zeta_EM_nat_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 0 < N) :
    |Zs σ N - (riemannZeta σ).re - (N : ℝ) ^ (1 - σ) / (1 - σ)| ≤ (N : ℝ) ^ (-σ) := by
  have h := zeta_EM_nat h0 h1 hN
  rw [Zs_cast h0] at h
  have hz : riemannZeta (σ : ℂ) = (((riemannZeta σ).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [zeta_im_eq_zero]
  have hc : (N : ℂ) ^ (1 - (σ : ℂ)) / (1 - σ) = (((N : ℝ) ^ (1 - σ) / (1 - σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg N)]; push_cast; ring_nf
  rw [hz, hc, ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- `ζ(σ) ≤ 0` for `1/2 ≤ σ < 1`. -/
theorem zeta_nonpos {σ : ℝ} (h0 : 1 / 2 ≤ σ) (h1 : σ < 1) : (riemannZeta σ).re ≤ 0 := by
  have h := zeta_EM_nat_real (by linarith) h1 (N := 1) one_pos
  have hZ : Zs σ 1 = 1 := by simp [Zs]
  rw [hZ] at h
  simp only [Nat.cast_one, Real.one_rpow] at h
  have hd : 0 < 1 - σ := by linarith
  have h2 : 2 ≤ 1 / (1 - σ) := by rw [le_div_iff₀ hd]; linarith
  have := (abs_le.mp h).1
  linarith

/-- concavity: `t^δ − N^δ ≤ δ N^{δ-1} (t − N)` for `0 ≤ δ ≤ 1`, `0 < N ≤ t` -/
theorem rpow_sub_le_of_concave {δ N t : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hNt : N ≤ t) :
    t ^ δ - N ^ δ ≤ δ * N ^ (δ - 1) * (t - N) := by
  have hu : -1 ≤ (t - N) / N := by
    have : 0 ≤ (t - N) / N := div_nonneg (by linarith) hN.le
    linarith
  have h := rpow_one_add_le_one_add_mul_self hu hδ0 hδ1
  have ht : t = N * (1 + (t - N) / N) := by field_simp; ring
  have hNd : N ^ (δ - 1) = N ^ δ / N := by rw [Real.rpow_sub_one hN.ne']
  calc t ^ δ - N ^ δ = N ^ δ * ((1 + (t - N) / N) ^ δ - 1) := by
        conv_lhs => rw [ht]
        rw [Real.mul_rpow hN.le (by linarith)]; ring
    _ ≤ N ^ δ * (δ * ((t - N) / N)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = δ * N ^ (δ - 1) * (t - N) := by rw [hNd]; field_simp

/-- Euler–Maclaurin at real `t ≥ 1`, with `N = ⌊t⌋`. -/
theorem zeta_EM_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {t : ℝ} (ht : 1 ≤ t) :
    |Zs σ ⌊t⌋₊ - (riemannZeta σ).re - t ^ (1 - σ) / (1 - σ)| ≤ 4 * t ^ (-σ) := by
  set N := ⌊t⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast ht)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htN : t < N + 1 := Nat.lt_floor_add_one t
  have hd : 0 < 1 - σ := by linarith
  have hE := zeta_EM_nat_real h0 h1 (N := N) (by omega)
  -- 0 ≤ (t^δ − N^δ)/δ ≤ N^{-σ}
  have hc := rpow_sub_le_of_concave (δ := 1 - σ) hd.le (by linarith) (by linarith) hNt
  have hmono : (N : ℝ) ^ (1 - σ) ≤ t ^ (1 - σ) := Real.rpow_le_rpow (by linarith) hNt hd.le
  have hcorr : t ^ (1 - σ) / (1 - σ) - (N : ℝ) ^ (1 - σ) / (1 - σ) ≤ (N : ℝ) ^ (-σ) := by
    rw [← sub_div, div_le_iff₀ hd]
    have : (N : ℝ) ^ (1 - σ - 1) = (N : ℝ) ^ (-σ) := by ring_nf
    rw [this] at hc
    have hp : 0 ≤ (1 - σ) * (N : ℝ) ^ (-σ) :=
      mul_nonneg hd.le (Real.rpow_nonneg (show (0 : ℝ) ≤ N by linarith) (-σ))
    have := mul_le_mul_of_nonneg_left (show t - N ≤ 1 by linarith) hp
    linarith
  have hcorr0 : 0 ≤ t ^ (1 - σ) / (1 - σ) - (N : ℝ) ^ (1 - σ) / (1 - σ) := by
    rw [← sub_div]; exact div_nonneg (by linarith) hd.le
  -- N^{-σ} ≤ 2 t^{-σ}, since t ≤ 2N
  have h2N : t ≤ 2 * N := by linarith
  have hNσ : (N : ℝ) ^ (-σ) ≤ 2 * t ^ (-σ) := by
    have h1' : (N : ℝ) ^ (-σ) = ((2 * N) ^ (-σ)) * 2 ^ σ := by
      rw [Real.mul_rpow (by norm_num) (by linarith), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
    have h2' : ((2 * N : ℝ)) ^ (-σ) ≤ t ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h2N (by linarith)
    have h3' : (2 : ℝ) ^ σ ≤ 2 := by
      calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1.le
        _ = 2 := Real.rpow_one 2
    rw [h1']
    calc (2 * N : ℝ) ^ (-σ) * 2 ^ σ ≤ t ^ (-σ) * 2 :=
          mul_le_mul h2' h3' (by positivity) (by positivity)
      _ = 2 * t ^ (-σ) := by ring
  rw [abs_le] at hE ⊢
  constructor <;> nlinarith [hE.1, hE.2]

#print axioms zeta_nonpos
#print axioms zeta_EM_real

end B4
