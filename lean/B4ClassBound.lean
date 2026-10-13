/-
B-4, Lemma L1 applied (2026-10-10): from an explicit zero gap `GapFrom c T` to the lower bound
  √q · L(1, χ) > N π     for all real primitive χ mod q (q ≥ 3, q ≠ 8) with log q ≥ T,
which by the class number formula h(−d) = √d L(1, χ_d)/π (d > 4; formalized in B4ClassNumber.lean) means h > N.
Proof: `L1_elementary` with σ = 1 − c/ℓ (ℓ = log q), Y = ⌈A q ℓ⌉, X = V Y; every error term is bounded
uniformly for ℓ ≥ T (log(x)/x decreases for x ≥ e, e^{x/2}/x increases for x ≥ 2), so that
  √q L(1, χ) ≥ (1 − ε) c e^{-P} e^{T/2}/T,
with P and ε as in `classEps`, `classP` (computations/lean_h.gp). The remaining closed inequality is
proved by LeanCert in B4ClassCert.lean.
Build: see README.md.
-/
import B4L1
import B4Chain

namespace B4

open Real OAI.SiegelZeros.WeightedTorusJets

/-- `P = c (1 + log(2 V A T)/T)` -/
noncomputable def classP (c T A V : ℝ) : ℝ := c * (1 + Real.log (2 * V * A * T) / T)

/-- the total error bound `ε` -/
noncomputable def classEps (c T A V : ℝ) : ℝ :=
  Real.exp c * (Real.exp (c * Real.log (A * T) / T) * Real.exp (c / T * Real.log V) / (c * A) +
      4 * Real.exp (-(1 - c / T) * Real.log (A * T))) +
    Real.exp (classP c T A V) / (c * A) +
    4 * Real.exp (-(1 - c / T) * Real.log V) * Real.exp (classP c T A V) +
    Real.exp (classP c T A V) / (A * T)

theorem log_div_le_of_le {B ℓ T : ℝ} (hB : 0 < B) (hBT : Real.exp 1 ≤ B * T) (hT : T ≤ ℓ) :
    Real.log (B * ℓ) / ℓ ≤ Real.log (B * T) / T := by
  have hT0 : 0 < T := by
    by_contra h; replace h := not_lt.mp h
    have : B * T ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hB.le h
    linarith [Real.exp_pos 1]
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hT0 hT
  have hmem1 : B * T ∈ Set.Ici (Real.exp 1) := hBT
  have hmem2 : B * ℓ ∈ Set.Ici (Real.exp 1) := le_trans hBT (by nlinarith)
  have h := log_div_self_antitoneOn hmem1 hmem2 (by nlinarith)
  have e1 : Real.log (B * ℓ) / ℓ = B * (Real.log (B * ℓ) / (B * ℓ)) := by field_simp
  have e2 : Real.log (B * T) / T = B * (Real.log (B * T) / (B * T)) := by field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left h hB.le

theorem exp_half_div_le {T ℓ : ℝ} (hT : 2 ≤ T) (hTℓ : T ≤ ℓ) :
    Real.exp (T / 2) / T ≤ Real.exp (ℓ / 2) / ℓ := by
  have hT0 : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  rw [div_le_div_iff₀ hT0 hℓ0]
  have h1 : Real.exp (ℓ / 2) = Real.exp (T / 2) * Real.exp ((ℓ - T) / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : 1 + (ℓ - T) / 2 ≤ Real.exp ((ℓ - T) / 2) := by linarith [Real.add_one_le_exp ((ℓ - T) / 2)]
  have h3 : ℓ ≤ T * (1 + (ℓ - T) / 2) := by nlinarith
  have he : 0 < Real.exp (T / 2) := Real.exp_pos _
  calc Real.exp (T / 2) * ℓ ≤ Real.exp (T / 2) * (T * (1 + (ℓ - T) / 2)) :=
        mul_le_mul_of_nonneg_left h3 he.le
    _ ≤ Real.exp (T / 2) * (T * Real.exp ((ℓ - T) / 2)) := by
        apply mul_le_mul_of_nonneg_left _ he.le
        exact mul_le_mul_of_nonneg_left h2 hT0.le
    _ = Real.exp (ℓ / 2) * T := by rw [h1]; ring

set_option maxHeartbeats 4000000 in
/-- **Class-number-type bound from a zero gap.** -/
theorem h_bound_of_gap {c T A Nh : ℝ} {V : ℕ} (hc : 0 < c) (hT2 : 2 ≤ T) (hcT : c / T ≤ 1 / 2)
    (hAT : Real.exp 1 ≤ A * T) (hV : 1 ≤ V) (hgap : GapFrom c T)
    (heps : classEps c T A V < 1)
    (hcert : Nh * π < (1 - classEps c T A V) * c * Real.exp (-classP c T A V) * Real.exp (T / 2) / T) :
    ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 → ∀ (χ : DirichletCharacter ℂ q),
      (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 → T ≤ Real.log q →
      Nh * π < Real.sqrt q * (DirichletCharacter.LFunction χ 1).re := by
  intro q _ hq hq8 χ hreal hprim hne hℓT
  have hT0 : 0 < T := by linarith
  have hA0 : 0 < A := by
    by_contra h; replace h := not_lt.mp h
    have : A * T ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hT0.le
    linarith [Real.exp_pos 1]
  set ℓ := Real.log q with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hT0 hℓT
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqexp : (q : ℝ) = Real.exp ℓ := (Real.exp_log hq0).symm
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hχ2 : χ ^ 2 = 1 := MulChar.isQuadratic_iff_sq_eq_one.mp (real_character_isQuadratic χ hreal)
  -- σ = 1 − c/ℓ
  set δ := c / ℓ with hδ
  have hδ0 : 0 < δ := div_pos hc hℓ0
  have hδT : δ ≤ c / T := div_le_div_of_nonneg_left hc.le hT0 hℓT
  set σ := 1 - δ with hσ
  have h0 : 1 / 2 ≤ σ := by simp only [hσ]; linarith
  have h1 : σ < 1 := by simp only [hσ]; linarith
  set σT := 1 - c / T
  have hσσT : σT ≤ σ := by simp only [hσ, σT]; linarith
  have hσT0 : 0 ≤ σT := by simp only [σT]; linarith
  -- no zero in (σ, 1)
  have hzf : ∀ t : ℝ, σ < t → t < 1 → DirichletCharacter.LFunction χ t ≠ 0 := by
    intro t ht1 ht2 hz
    have ht0 : 0 < t := by linarith
    have hg := hgap q hq hq8 χ hreal hprim hne t ht0 ht2 hz hℓT
    have : (1 - t) * ℓ < c := by
      have : (1 - t) < δ := by simp only [hσ] at ht1; linarith
      calc (1 - t) * ℓ < δ * ℓ := mul_lt_mul_of_pos_right this hℓ0
        _ = c := by simp only [hδ]; field_simp
    linarith
  -- the cutoffs
  set Y : ℕ := ⌈A * q * ℓ⌉₊ with hYdef
  have hAqℓ : 1 ≤ A * q * ℓ := by
    have h1' : Real.exp 1 ≤ A * ℓ := le_trans hAT (by nlinarith)
    have h2' : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith
  have hYlo : A * q * ℓ ≤ Y := Nat.le_ceil _
  have hYhi : (Y : ℝ) ≤ 2 * (A * q * ℓ) := by
    have := Nat.ceil_lt_add_one (show 0 ≤ A * q * ℓ by linarith)
    linarith
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := le_trans hAqℓ hYlo
    exact_mod_cast this
  have hYX : Y ≤ V * Y := Nat.le_mul_of_pos_left Y (by omega)
  have hL := L1_elementary χ hne hreal hχ2 h0 h1 hzf hY1 hYX
  -- real quantities
  have hYr0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hVr : (1 : ℝ) ≤ V := by exact_mod_cast hV
  have hVr0 : (0 : ℝ) < V := by linarith
  have hXr : ((V * Y : ℕ) : ℝ) = V * Y := by push_cast; ring
  have ht : ((V * Y : ℕ) : ℝ) / Y = V := by rw [hXr]; field_simp
  rw [ht, hXr] at hL
  set Xr : ℝ := (V : ℝ) * Y with hXrdef
  have hXr0 : 0 < Xr := by positivity
  have hYXr : (Y : ℝ) ≤ Xr := by simp only [hXrdef]; nlinarith
  have h1σ : 1 - σ = δ := by simp only [hσ]; ring
  rw [h1σ] at hL
  -- q^δ = e^c
  have hqδ : (q : ℝ) ^ δ = Real.exp c := by
    rw [Real.rpow_def_of_pos hq0, ← hℓ]; congr 1; simp only [hδ]; field_simp
  -- X^δ ≤ e^P
  have hXδ : Xr ^ δ ≤ Real.exp (classP c T A V) := by
    rw [Real.rpow_def_of_pos hXr0]
    apply Real.exp_le_exp.mpr
    have hX2 : Xr ≤ 2 * V * A * ℓ * q := by
      have := mul_le_mul_of_nonneg_left hYhi hVr0.le
      simp only [hXrdef]; nlinarith
    have hlogX : Real.log Xr ≤ Real.log (2 * V * A * ℓ) + ℓ := by
      have := Real.log_le_log hXr0 hX2
      rw [show 2 * (V : ℝ) * A * ℓ * q = (2 * V * A * ℓ) * q by ring,
        Real.log_mul (by positivity) hq0.ne'] at this
      linarith
    have hAT0 : 0 ≤ A * T := by positivity
    have hM2 := log_div_le_of_le (B := 2 * V * A) (by positivity)
      (le_trans hAT (by
        have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 * V by linarith) hAT0
        nlinarith)) hℓT
    rw [show 2 * (V : ℝ) * A * T = 2 * V * A * T from rfl] at hM2
    have : Real.log Xr * δ ≤ c + c * (Real.log (2 * V * A * ℓ) / ℓ) := by
      have hδℓ : δ * ℓ = c := by simp only [hδ]; field_simp
      calc Real.log Xr * δ ≤ (Real.log (2 * V * A * ℓ) + ℓ) * δ :=
            mul_le_mul_of_nonneg_right hlogX hδ0.le
        _ = c + c * (Real.log (2 * V * A * ℓ) / ℓ) := by
            simp only [hδ]; field_simp; ring
    unfold classP
    nlinarith [mul_le_mul_of_nonneg_left hM2 hc.le]
  -- auxiliary facts
  have hAℓ0 : 0 < A * ℓ := by positivity
  have hAqℓ0 : 0 < A * q * ℓ := by positivity
  have hM1 := log_div_le_of_le (B := A) hA0 hAT hℓT
  have hlogAT : 1 ≤ Real.log (A * T) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; exact hAT
  have hlogAℓ : Real.log (A * T) ≤ Real.log (A * ℓ) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hVr
  have hσ0 : 0 ≤ σ := by linarith
  have hδℓ : δ * ℓ = c := by simp only [hδ]; field_simp
  have heP : 0 < Real.exp (classP c T A V) := Real.exp_pos _
  -- Term 1
  have hB1 : (q : ℝ) * ((Y : ℝ) + 1) ^ (-σ) * ((V : ℝ) ^ δ / δ + 4 * (V : ℝ) ^ (-σ)) ≤
      Real.exp c * (Real.exp (c * Real.log (A * T) / T) * Real.exp (c / T * Real.log V) / (c * A) +
        4 * Real.exp (-(1 - c / T) * Real.log (A * T))) := by
    have ha : ((Y : ℝ) + 1) ^ (-σ) ≤ (A * q * ℓ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hAqℓ0 (by linarith) (by linarith)
    have hb : (q : ℝ) * (A * q * ℓ) ^ (-σ) = Real.exp c * (A * ℓ) ^ (-σ) := by
      rw [show A * (q : ℝ) * ℓ = (A * ℓ) * q by ring, Real.mul_rpow hAℓ0.le hq0.le, ← hqδ]
      have : (q : ℝ) ^ δ = q * (q : ℝ) ^ (-σ) := by
        rw [show δ = 1 + -σ by simp only [hσ]; ring, Real.rpow_add hq0, Real.rpow_one]
      rw [this]; ring
    have hd : (A * ℓ) ^ (-σ) * ((V : ℝ) ^ δ / δ) = (A * ℓ) ^ δ * (V : ℝ) ^ δ / (c * A) := by
      have e : (A * ℓ) ^ δ = (A * ℓ) * (A * ℓ) ^ (-σ) := by
        rw [show δ = 1 + -σ by simp only [hσ]; ring, Real.rpow_add hAℓ0, Real.rpow_one]
      rw [e, hδ]; field_simp
    have he : (A * ℓ) ^ δ ≤ Real.exp (c * Real.log (A * T) / T) := by
      rw [Real.rpow_def_of_pos hAℓ0]
      apply Real.exp_le_exp.mpr
      have : Real.log (A * ℓ) * δ = c * (Real.log (A * ℓ) / ℓ) := by simp only [hδ]; field_simp
      rw [this, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hM1 hc.le
    have hf : (V : ℝ) ^ δ ≤ Real.exp (c / T * Real.log V) := by
      rw [Real.rpow_def_of_pos hVr0]
      apply Real.exp_le_exp.mpr
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hδT hlogV
    have hg : (A * ℓ) ^ (-σ) ≤ Real.exp (-(1 - c / T) * Real.log (A * T)) := by
      rw [Real.rpow_def_of_pos hAℓ0]
      apply Real.exp_le_exp.mpr
      have : (1 - c / T) * Real.log (A * T) ≤ σ * Real.log (A * ℓ) := by
        apply mul_le_mul hσσT hlogAℓ (by linarith) hσ0
      linarith
    have hV1 : (V : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hVr (by linarith)
    have hpos1 : 0 ≤ (A * ℓ) ^ (-σ) := by positivity
    calc (q : ℝ) * ((Y : ℝ) + 1) ^ (-σ) * ((V : ℝ) ^ δ / δ + 4 * (V : ℝ) ^ (-σ))
        ≤ (q : ℝ) * (A * q * ℓ) ^ (-σ) * ((V : ℝ) ^ δ / δ + 4 * (V : ℝ) ^ (-σ)) := by gcongr
      _ = Real.exp c * ((A * ℓ) ^ (-σ) * ((V : ℝ) ^ δ / δ) + (A * ℓ) ^ (-σ) * (4 * (V : ℝ) ^ (-σ))) := by
          rw [hb]; ring
      _ = Real.exp c * ((A * ℓ) ^ δ * (V : ℝ) ^ δ / (c * A) + (A * ℓ) ^ (-σ) * (4 * (V : ℝ) ^ (-σ))) := by
          rw [hd]
      _ ≤ _ := by
          have hx1 : (A * ℓ) ^ δ * (V : ℝ) ^ δ / (c * A) ≤
              Real.exp (c * Real.log (A * T) / T) * Real.exp (c / T * Real.log V) / (c * A) :=
            div_le_div_of_nonneg_right (mul_le_mul he hf (by positivity) (by positivity))
              (by positivity)
          have hx2 : (A * ℓ) ^ (-σ) * (4 * (V : ℝ) ^ (-σ)) ≤
              4 * Real.exp (-(1 - c / T) * Real.log (A * T)) := by
            calc (A * ℓ) ^ (-σ) * (4 * (V : ℝ) ^ (-σ)) ≤ (A * ℓ) ^ (-σ) * 4 :=
                  mul_le_mul_of_nonneg_left (by linarith) hpos1
              _ ≤ Real.exp (-(1 - c / T) * Real.log (A * T)) * 4 :=
                  mul_le_mul_of_nonneg_right hg (by norm_num)
              _ = _ := by ring
          exact mul_le_mul_of_nonneg_left (add_le_add hx1 hx2) (Real.exp_pos c).le
  -- Term 2
  have hB2 : Xr ^ δ / δ * ((q : ℝ) * ((Y : ℝ) + 1) ^ (-(1 : ℝ))) ≤
      Real.exp (classP c T A V) / (c * A) := by
    have ha : ((Y : ℝ) + 1) ^ (-(1 : ℝ)) ≤ (A * q * ℓ)⁻¹ := by
      rw [Real.rpow_neg_one]; exact inv_anti₀ hAqℓ0 (by linarith)
    have hb : (q : ℝ) * (A * q * ℓ)⁻¹ / δ = 1 / (c * A) := by
      rw [hδ]; field_simp
    calc Xr ^ δ / δ * ((q : ℝ) * ((Y : ℝ) + 1) ^ (-(1 : ℝ)))
        ≤ Xr ^ δ / δ * ((q : ℝ) * (A * q * ℓ)⁻¹) := by gcongr
      _ = Xr ^ δ * ((q : ℝ) * (A * q * ℓ)⁻¹ / δ) := by ring
      _ = Xr ^ δ * (1 / (c * A)) := by rw [hb]
      _ ≤ Real.exp (classP c T A V) * (1 / (c * A)) := by gcongr
      _ = _ := by ring
  -- Term 3
  have hB3 : 4 * (Y : ℝ) * Xr ^ (-σ) ≤
      4 * Real.exp (-(1 - c / T) * Real.log V) * Real.exp (classP c T A V) := by
    have ha : (Y : ℝ) * Xr ^ (-σ) = (V : ℝ) ^ (-σ) * (Y : ℝ) ^ δ := by
      simp only [hXrdef]
      rw [Real.mul_rpow hVr0.le hYr0.le]
      have : (Y : ℝ) ^ δ = Y * (Y : ℝ) ^ (-σ) := by
        rw [show δ = 1 + -σ by simp only [hσ]; ring, Real.rpow_add hYr0, Real.rpow_one]
      rw [this]; ring
    have hb : (Y : ℝ) ^ δ ≤ Real.exp (classP c T A V) :=
      (Real.rpow_le_rpow hYr0.le hYXr hδ0.le).trans hXδ
    have hc' : (V : ℝ) ^ (-σ) ≤ Real.exp (-(1 - c / T) * Real.log V) := by
      rw [Real.rpow_def_of_pos hVr0]
      apply Real.exp_le_exp.mpr
      have : (1 - c / T) * Real.log V ≤ σ * Real.log V := mul_le_mul_of_nonneg_right hσσT hlogV
      linarith
    calc 4 * (Y : ℝ) * Xr ^ (-σ) = 4 * ((V : ℝ) ^ (-σ) * (Y : ℝ) ^ δ) := by rw [← ha]; ring
      _ ≤ 4 * (Real.exp (-(1 - c / T) * Real.log V) * Real.exp (classP c T A V)) := by gcongr
      _ = _ := by ring
  -- Term 4
  have hB4 : (q : ℝ) * Xr ^ δ / Y ≤ Real.exp (classP c T A V) / (A * T) := by
    have ha : (q : ℝ) / Y ≤ 1 / (A * T) := by
      rw [div_le_div_iff₀ hYr0 (by positivity), one_mul]
      calc (q : ℝ) * (A * T) ≤ q * (A * ℓ) := by gcongr
        _ = A * q * ℓ := by ring
        _ ≤ Y := hYlo
    calc (q : ℝ) * Xr ^ δ / Y = Xr ^ δ * ((q : ℝ) / Y) := by ring
      _ ≤ Real.exp (classP c T A V) * (1 / (A * T)) := by gcongr
      _ = _ := by ring
  -- total error
  have hErr : (q : ℝ) * ((Y : ℝ) + 1) ^ (-σ) * ((V : ℝ) ^ δ / δ + 4 * (V : ℝ) ^ (-σ)) +
      Xr ^ δ / δ * ((q : ℝ) * ((Y : ℝ) + 1) ^ (-(1 : ℝ))) + 4 * (Y : ℝ) * Xr ^ (-σ) +
      (q : ℝ) * Xr ^ δ / Y ≤ classEps c T A V := by
    unfold classEps; linarith
  -- lower bound for L(1)
  set L1 := (DirichletCharacter.LFunction χ 1).re
  set ε := classEps c T A V
  have hXδ0 : 0 < Xr ^ δ := by positivity
  have hmain : 1 - ε ≤ Xr ^ δ / δ * L1 := by linarith
  have hL1 : (1 - ε) * δ * Real.exp (-classP c T A V) ≤ L1 := by
    have hk : 0 < Xr ^ δ / δ := by positivity
    have h1' : (1 - ε) / (Xr ^ δ / δ) ≤ L1 := by rw [div_le_iff₀ hk]; linarith
    have h2' : Real.exp (-classP c T A V) ≤ 1 / Xr ^ δ := by
      rw [Real.exp_neg, ← one_div]; exact one_div_le_one_div_of_le hXδ0 hXδ
    calc (1 - ε) * δ * Real.exp (-classP c T A V) ≤ (1 - ε) * δ * (1 / Xr ^ δ) := by
          apply mul_le_mul_of_nonneg_left h2'; nlinarith
      _ = (1 - ε) / (Xr ^ δ / δ) := by field_simp
      _ ≤ L1 := h1'
  -- √q = e^{ℓ/2}
  have hsq : Real.sqrt q = Real.exp (ℓ / 2) := by
    have e : Real.exp ℓ = Real.exp (ℓ / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hqexp, e, Real.sqrt_sq (Real.exp_pos _).le]
  have hmono := exp_half_div_le (T := T) (ℓ := ℓ) hT2 hℓT
  have hfin : (1 - ε) * c * Real.exp (-classP c T A V) * Real.exp (T / 2) / T ≤
      Real.sqrt q * L1 := by
    rw [hsq]
    have hk : 0 ≤ (1 - ε) * c * Real.exp (-classP c T A V) := by
      have : 0 < 1 - ε := by linarith
      positivity
    calc (1 - ε) * c * Real.exp (-classP c T A V) * Real.exp (T / 2) / T
        = (1 - ε) * c * Real.exp (-classP c T A V) * (Real.exp (T / 2) / T) := by ring
      _ ≤ (1 - ε) * c * Real.exp (-classP c T A V) * (Real.exp (ℓ / 2) / ℓ) := by gcongr
      _ = Real.exp (ℓ / 2) * ((1 - ε) * δ * Real.exp (-classP c T A V)) := by
          simp only [hδ]; field_simp
      _ ≤ Real.exp (ℓ / 2) * L1 := by gcongr
  linarith

#print axioms h_bound_of_gap

end B4
