/-
B-4, class number formula, part 3 (2026-10-10): the analytic class number formula for imaginary
quadratic fields, and the final class number bounds.

* `residue_eq`: `Res_{s=1} ζ_K = L(1, χ_D)` for a quadratic field (from `B4QuadZeta.dedekindZeta_eq`,
  Mathlib's `riemannZeta_residue_one` and `tendsto_sub_one_mul_dedekindZeta_nhdsGT`).
* `classNumber_formula`: for `K` imaginary quadratic, `h = w √|D| L(1, χ_D) / (2π)` (Mathlib's
  `dedekindZeta_residue_def` with `r₁ = 0`, `r₂ = 1`, `R = 1`), hence `h ≥ √|D| L(1, χ_D) / π`
  since `w ≥ 2` (`classNumber_ge`).
* `chi_isPrimitive`: the complex-valued `χ_D` is primitive of level `|D|` (TauCeti proves this for
  the integer-valued character).
* `classNumber_gt_N` (`N = 100, 200, 500, 1000, 2000`): every imaginary quadratic field with
  `log |disc K| ≥ T_N` has class number `> N`, from `B4.ClassCert.class_bound_hN`.
-/
import B4QuadZeta
import B4ClassCert
import TauCeti.NumberTheory.NumberField.Quadratic.Basic

open Ideal Module Polynomial Filter NumberField
open scoped NumberField Topology

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace B4.CNF

open TauCeti.Multiquadratic

/-! ### `χ_D` over `ℂ` is primitive and nontrivial -/

theorem chi_ker {d : ℤ} (hsf : Squarefree d) :
    (chi d hsf).toUnitHom.ker = (chiZ d hsf).toUnitHom.ker := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  rw [chi_apply]
  exact_mod_cast Iff.rfl

theorem chi_factorsThrough_iff {d : ℤ} (hsf : Squarefree d) (e : ℕ) :
    (chi d hsf).FactorsThrough e ↔ (chiZ d hsf).FactorsThrough e := by
  haveI := neZero_Dd hsf
  constructor
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ← chi_ker hsf]
    exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).1 h
  · intro h
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, chi_ker hsf]
    exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).1 h

theorem chi_isPrimitive {d : ℤ} (hsf : Squarefree d) : (chi d hsf).IsPrimitive := by
  have hZ := isPrimitive_fundamentalDiscriminantChar (isFD hsf)
  have hset : (chi d hsf).conductorSet = (chiZ d hsf).conductorSet :=
    Set.ext fun e => chi_factorsThrough_iff hsf e
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor, hset]
  exact hZ

theorem chi_ne_one {d : ℤ} (hsf : Squarefree d) (h1 : (Dd d).natAbs ≠ 1) : chi d hsf ≠ 1 := by
  haveI := neZero_Dd hsf
  intro h
  have := DirichletCharacter.eq_one_iff_conductor_eq_one.1 h
  rw [chi_isPrimitive hsf] at this
  exact h1 this

theorem chi_im {d : ℤ} (hsf : Squarefree d) (x : ZMod (Dd d).natAbs) : (chi d hsf x).im = 0 := by
  rw [chi_apply]; simp

/-! ### The residue -/

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}
  (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (hsf : Squarefree d)
include hmin hgen hsf

theorem natAbs_Dd_eq : ((Dd d).natAbs : ℝ) = |(NumberField.discr K : ℝ)| := by
  rw [discr_eq hmin hgen hsf, Nat.cast_natAbs, Int.cast_abs]

theorem natAbs_Dd_gt_two : 2 < (Dd d).natAbs := by
  have h := NumberField.abs_discr_gt_two (K := K)
    (by rw [NumberField.finrank_rat_eq_two hmin hgen]; norm_num)
  rw [discr_eq hmin hgen hsf, ← Int.natCast_natAbs] at h
  omega

/-- **`Res_{s=1} ζ_K = L(1, χ_D)`.** -/
theorem residue_eq : (NumberField.dedekindZeta_residue K : ℂ) = Lchi d hsf 1 := by
  haveI := neZero_Dd hsf
  have hne1 : chi d hsf ≠ 1 := chi_ne_one hsf (by have := natAbs_Dd_gt_two hmin hgen hsf; omega)
  -- the real points `s > 1` approach `1` in `ℂ \ {1}`
  have hof : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have : s = 1 := by exact_mod_cast h
      exact (lt_irrefl _ (this ▸ hs : (1 : ℝ) < 1))
  have hz : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hof
  have hL : Tendsto (fun s : ℝ => Lchi d hsf s) (𝓝[>] 1) (𝓝 (Lchi d hsf 1)) := by
    have hc := (DirichletCharacter.differentiable_LFunction hne1).continuous
    have : Tendsto (fun s : ℂ => DirichletCharacter.LFunction (chi d hsf) s) (𝓝 1)
        (𝓝 (DirichletCharacter.LFunction (chi d hsf) 1)) := hc.tendsto 1
    exact (this.comp ((Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds |>.trans
      (by simp))).congr fun s => rfl
  have hprod : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * NumberField.dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (1 * Lchi d hsf 1)) := by
    refine (hz.mul hL).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hre : 1 < ((s : ℂ)).re := by simpa using hs
    rw [dedekindZeta_eq hmin hgen hsf hre]
    ring
  rw [one_mul] at hprod
  exact tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K) hprod

theorem L1_im : (Lchi d hsf 1).im = 0 := by
  rw [← residue_eq hmin hgen hsf]; simp

theorem residue_eq_re : NumberField.dedekindZeta_residue K = (Lchi d hsf 1).re := by
  have := congrArg Complex.re (residue_eq hmin hgen hsf)
  simpa using this

/-! ### Imaginary quadratic fields -/

variable [IsTotallyComplex K]

theorem nrRealPlaces_eq : InfinitePlace.nrRealPlaces K = 0 :=
  (NumberField.nrRealPlaces_eq_zero_iff (K := K)).2 inferInstance

theorem nrComplexPlaces_eq : InfinitePlace.nrComplexPlaces K = 1 := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank (K := K)
  rw [nrRealPlaces_eq hmin hgen hsf, NumberField.finrank_rat_eq_two hmin hgen] at h
  omega

theorem regulator_eq : NumberField.Units.regulator K = 1 := by
  classical
  have hcard : Fintype.card (InfinitePlace K) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq hmin hgen hsf,
      nrComplexPlaces_eq hmin hgen hsf]
  rw [NumberField.Units.regulator_eq_det']
  haveI : IsEmpty {w : InfinitePlace K // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := by
    rw [isEmpty_subtype]
    intro w
    push Not
    have hsub : Subsingleton (InfinitePlace K) :=
      Fintype.card_le_one_iff_subsingleton.mp hcard.le
    exact Subsingleton.elim _ _
  rw [Matrix.det_isEmpty, abs_one]

/-- **The class number formula for an imaginary quadratic field**:
`2π h = w √|D| L(1, χ_D)`. -/
theorem classNumber_formula :
    2 * Real.pi * (NumberField.classNumber K : ℝ) =
      (NumberField.Units.torsionOrder K : ℝ) * Real.sqrt (Dd d).natAbs * (Lchi d hsf 1).re := by
  have h := NumberField.dedekindZeta_residue_def K
  rw [residue_eq_re hmin hgen hsf, nrRealPlaces_eq hmin hgen hsf, nrComplexPlaces_eq hmin hgen hsf,
    regulator_eq hmin hgen hsf, ← natAbs_Dd_eq hmin hgen hsf] at h
  have hw : (0 : ℝ) < NumberField.Units.torsionOrder K := by
    exact_mod_cast NumberField.Units.torsionOrder_pos K
  have hD : (0 : ℝ) < Real.sqrt (Dd d).natAbs := by
    apply Real.sqrt_pos.2
    have := natAbs_Dd_gt_two hmin hgen hsf
    exact_mod_cast (by omega : 0 < (Dd d).natAbs)
  rw [h]
  field_simp

/-- **`π h ≥ √|D| L(1, χ_D)`**, since `w ≥ 2`. -/
theorem classNumber_ge :
    Real.sqrt (Dd d).natAbs * (Lchi d hsf 1).re ≤ Real.pi * (NumberField.classNumber K : ℝ) := by
  have hf := classNumber_formula hmin hgen hsf
  have hw2 : (2 : ℝ) ≤ NumberField.Units.torsionOrder K := by
    obtain ⟨k, hk⟩ := NumberField.Units.even_torsionOrder (K := K)
    have := NumberField.Units.torsionOrder_pos K
    exact_mod_cast (by omega : 2 ≤ NumberField.Units.torsionOrder K)
  have hpos : 0 ≤ Real.sqrt (Dd d).natAbs * (Lchi d hsf 1).re := by
    have hres := NumberField.dedekindZeta_residue_pos K
    rw [residue_eq_re hmin hgen hsf] at hres
    exact mul_nonneg (Real.sqrt_nonneg _) hres.le
  nlinarith

end B4.CNF

/-! ### Final class number bounds -/

namespace B4.ClassNumber

open B4.CNF

/-- From an `L(1)`-bound of the shape `class_bound_hN` to a class number bound. -/
theorem classNumber_gt_of (N : ℕ) (T : ℝ) (hT : 3 ≤ T)
    (hb : ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 → ∀ (χ : DirichletCharacter ℂ q),
      (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 → T ≤ Real.log q →
      (N : ℝ) * Real.pi < Real.sqrt q * (DirichletCharacter.LFunction χ 1).re)
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    (hlog : T ≤ Real.log |(NumberField.discr K : ℝ)|) :
    N < NumberField.classNumber K := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := NumberField.exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  haveI := neZero_Dd hsf
  set q := (Dd d).natAbs with hq
  rw [← natAbs_Dd_eq hmin hgen hsf] at hlog
  -- `q ≥ e^3 > 8`
  have hq8 : (8 : ℝ) < q := by
    have hq0 : (0 : ℝ) < q := by
      have := natAbs_Dd_gt_two hmin hgen hsf
      exact_mod_cast (by omega : 0 < q)
    have h3 : (3 : ℝ) ≤ Real.log q := hT.trans hlog
    have he : Real.exp 3 ≤ q := by
      rw [← Real.exp_log hq0]; exact Real.exp_le_exp.2 h3
    have : (8 : ℝ) < Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      have h2 := Real.exp_one_gt_d9
      calc (8 : ℝ) < 2.7182818283 ^ 3 := by norm_num
        _ < Real.exp 1 ^ 3 := by gcongr
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    linarith
  have hq3 : 3 ≤ q := by exact_mod_cast (by linarith : (3 : ℝ) ≤ q)
  have hq8' : q ≠ 8 := by
    intro h; rw [h] at hq8; norm_num at hq8
  have hne1 : chi d hsf ≠ 1 := chi_ne_one hsf (by omega)
  have hL := hb q hq3 hq8' (chi d hsf) (chi_im hsf) (chi_isPrimitive hsf) hne1 hlog
  have hge := classNumber_ge hmin hgen hsf
  have hL' : (N : ℝ) * Real.pi < Real.sqrt q * (Lchi d hsf 1).re := by
    simpa [Lchi] using hL
  have hpi := Real.pi_pos
  have : (N : ℝ) < NumberField.classNumber K := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  exact_mod_cast this

/-- **Every imaginary quadratic field with `|disc| ≥ e^28.6787` has class number `> 100`.** -/
theorem classNumber_gt_100 (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (h : (286787/10000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    100 < NumberField.classNumber K :=
  classNumber_gt_of 100 _ (by norm_num) (by exact_mod_cast B4.ClassCert.class_bound_h100) K hK h

/-- **Every imaginary quadratic field with `|disc| ≥ e^30.1458` has class number `> 200`.** -/
theorem classNumber_gt_200 (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (h : (150729/5000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    200 < NumberField.classNumber K :=
  classNumber_gt_of 200 _ (by norm_num) (by exact_mod_cast B4.ClassCert.class_bound_h200) K hK h

/-- **Every imaginary quadratic field with `|disc| ≥ e^32.0058` has class number `> 500`.** -/
theorem classNumber_gt_500 (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (h : (160029/5000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    500 < NumberField.classNumber K :=
  classNumber_gt_of 500 _ (by norm_num) (by exact_mod_cast B4.ClassCert.class_bound_h500) K hK h

/-- **Every imaginary quadratic field with `|disc| ≥ e^33.4757` has class number `> 1000`.** -/
theorem classNumber_gt_1000 (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (h : (334757/10000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    1000 < NumberField.classNumber K :=
  classNumber_gt_of 1000 _ (by norm_num) (by exact_mod_cast B4.ClassCert.class_bound_h1000) K hK h

/-- **Every imaginary quadratic field with `|disc| ≥ e^35.0131` has class number `> 2000`.** -/
theorem classNumber_gt_2000 (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (h : (350131/10000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    2000 < NumberField.classNumber K :=
  classNumber_gt_of 2000 _ (by norm_num) (by exact_mod_cast B4.ClassCert.class_bound_h2000) K hK h

#print axioms classNumber_gt_100
#print axioms classNumber_gt_200
#print axioms classNumber_gt_500
#print axioms classNumber_gt_1000
#print axioms classNumber_gt_2000

end B4.ClassNumber
