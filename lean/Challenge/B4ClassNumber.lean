import Mathlib

/-! Comparator challenge for the B-4 class-number bounds (Mathlib only).
Module `Challenge.B4ClassNumber`; the solution is the module `B4ClassNumber` (see `comparator/README.md`).
Every imaginary quadratic field `K` with `log |disc K| ≥ T_N` has class number `> N`. -/

namespace B4.ClassNumber

theorem classNumber_gt_100 (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (h : (286787/10000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    100 < NumberField.classNumber K := by
  sorry

theorem classNumber_gt_200 (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (h : (150729/5000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    200 < NumberField.classNumber K := by
  sorry

theorem classNumber_gt_500 (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (h : (160029/5000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    500 < NumberField.classNumber K := by
  sorry

theorem classNumber_gt_1000 (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (h : (334757/10000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    1000 < NumberField.classNumber K := by
  sorry

theorem classNumber_gt_2000 (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (h : (350131/10000 : ℝ) ≤ Real.log |(NumberField.discr K : ℝ)|) :
    2000 < NumberField.classNumber K := by
  sorry

end B4.ClassNumber
