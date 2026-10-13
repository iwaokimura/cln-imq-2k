/-
B-4 (iii), step 2 (2026-10-10): the predicates `GapOn c l0 l1` ("(1-β) log q ≥ c for every exceptional
zero β of a real primitive character mod q, q ≥ 3, q ≠ 8, with l0 ≤ log q ≤ l1") and `GapFrom c l0`,
the joins, the wrapper of `interval_gap`, and the tail lemma for log q ≥ T.
Tail: N = 2^k with k = ⌈τ ℓ⌉, so L = 4/3 k log 2 ∈ [aℓ, aℓ + b], a = 4/3 τ log 2, b = 4/3 log 2.
Then brExpr ≥ αℓ − C0 with
  α  = a − e^η/4 − 2^{-m} − (1+ρ)(3a/4 + 1/2),
  C0 = K0 + e^η η e^{-1}/T + (m+2) log 2 + (3j+2) log 2 + 4(1+ρ) log 2 + W0,
and the coefficient times the bracket is ≥ 2η²e^{-η}(α − C0/T)/(a + b/T)² for ℓ ≥ T.
The certificate `certTail` is this inequality, division-free in log 2 (for LeanCert).
Build: see README.md.
-/
import B4Interval

namespace B4

open OAI.SiegelZeros.WeightedTorusJets

/-- `(1-β) log q ≥ c` for `l0 ≤ log q ≤ l1`. -/
def GapOn (c l0 l1 : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 → ∀ (χ : DirichletCharacter ℂ q),
    (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
    ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
    l0 ≤ Real.log q → Real.log q ≤ l1 → c ≤ (1 - β) * Real.log q

/-- `(1-β) log q ≥ c` for `log q ≥ l0`. -/
def GapFrom (c l0 : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≠ 8 → ∀ (χ : DirichletCharacter ℂ q),
    (∀ x : ZMod q, (χ x).im = 0) → χ.IsPrimitive → χ ≠ 1 →
    ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
    l0 ≤ Real.log q → c ≤ (1 - β) * Real.log q

theorem gapFrom_join {c c1 c2 a b : ℝ} (h1 : GapOn c1 a b) (h2 : GapFrom c2 b)
    (hc1 : c ≤ c1) (hc2 : c ≤ c2) : GapFrom c a := by
  intro q _ hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero ha
  rcases le_total (Real.log q) b with hb | hb
  · exact hc1.trans (h1 q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero ha hb)
  · exact hc2.trans (h2 q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero hb)

theorem gapOn_of_cert (k j m : ℕ) (hk : 15 ≤ k) (hj : 1 ≤ j) (hjk : 3 * j ≤ k)
    (η l0 l1 Rb c : ℝ) (hη : 0 < η) (hη13 : η ≤ 13) (hl0 : 0 < l0)
    (hRb : l1 ≤ Rb ∨ ((m : ℝ) + 2) * Real.log 2 + l1 / 2 ^ m ≤ Rb)
    (P Q : ℝ) (hP : P = 2 ^ (3 * j)) (hQ : Q = 4 ^ j)
    (hc : 0 < c) (hcert : certProp k j P Q Rb η l0 l1 c) : GapOn c l0 l1 :=
  fun q _ hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero hℓ0 hℓ1 =>
    interval_gap q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero k j m hk hj hjk η l0 l1 Rb c hη hη13 hl0
      hℓ0 hℓ1 hRb P Q hP hQ hc hcert

/-- the tail certificate: `c (a + b/T)² ≤ 2η²e^{-η}(α − C0/T)`, written with products only -/
def certTail (J M Y P Q τ η T c : ℝ) : Prop :=
  c * ((4 / 3 * τ * Real.log 2 + 4 / 3 * Real.log 2 / T) * (4 / 3 * τ * Real.log 2 + 4 / 3 * Real.log 2 / T))
    ≤ 2 * η * η * Real.exp (-η) *
      ((4 / 3 * τ * Real.log 2 - Real.exp η / 4 - 1 / Y
          - (1 + 192 * (4 * 97 ^ 2) / P) * (τ * Real.log 2 + 1 / 2))
        - ((1 + (5 * Real.log 2 + 3) / 4 + 1 / 1000) + Real.exp η * η * Real.exp (-1) / T
          + (M + 2) * Real.log 2 + (3 * J + 2) * Real.log 2 + 4 * (1 + 192 * (4 * 97 ^ 2) / P) * Real.log 2
          + 4 * 97 ^ 2 * (2 * Real.log 2 + 1 / 1000) / Q) / T)

set_option maxHeartbeats 4000000 in
/-- **Tail lemma.** -/
theorem tail_gap (j m : ℕ) (hj : 1 ≤ j) (τ η T c : ℝ) (hτ : 0 < τ) (hη : 0 < η) (hη13 : η ≤ 13)
    (hT : 0 < T) (hτT : 15 + 3 * (j : ℝ) ≤ τ * T) (ha : 1 ≤ 4 / 3 * τ * Real.log 2)
    (Y P Q : ℝ) (hY : Y = 2 ^ m) (hP : P = 2 ^ (3 * j)) (hQ : Q = 4 ^ j)
    (hc : 0 < c) (hcert : certTail j m Y P Q τ η T c) : GapFrom c T := by
  intro q _ hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero hℓT
  subst hY hP hQ
  set ℓ := Real.log q with hℓ
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hT hℓT
  set k : ℕ := ⌈τ * ℓ⌉₊ with hkdef
  have hk1 : τ * ℓ ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < τ * ℓ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hτℓ : τ * T ≤ τ * ℓ := mul_le_mul_of_nonneg_left hℓT hτ.le
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk15 : 15 ≤ k := by
    have : (15 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  have hjk : 3 * j ≤ k := by
    have : ((3 * j : ℕ) : ℝ) ≤ k := by push_cast; linarith
    exact_mod_cast this
  have h := core_gap q hq hq8 χ hreal hprim hne β hβ0 hβ1 hzero k j m hk15 hj hjk η ℓ
    (((m : ℝ) + 2) * Real.log 2 + ℓ / 2 ^ m) hη hη13 le_rfl (Or.inr le_rfl)
  rw [← hℓ] at h
  -- abbreviations
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  set a := 4 / 3 * τ * Real.log 2 with ha_def
  set b := 4 / 3 * Real.log 2 with hb_def
  set L := 4 / 3 * (k : ℝ) * Real.log 2 with hL
  have hb0 : 0 < b := by positivity
  have hLlo : a * ℓ ≤ L := by
    simp only [ha_def, hL]; nlinarith [mul_le_mul_of_nonneg_right hk1 (by positivity : (0 : ℝ) ≤ 4 / 3 * Real.log 2)]
  have hLhi : L ≤ a * ℓ + b := by
    simp only [ha_def, hL, hb_def]
    nlinarith [mul_le_mul_of_nonneg_right hk2.le (by positivity : (0 : ℝ) ≤ 4 / 3 * Real.log 2)]
  have hLT : T ≤ L := by nlinarith
  have hLpos : 0 < L := by linarith
  set ρ := 192 * (4 * 97 ^ 2) / (2 : ℝ) ^ (3 * j) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set K0 := 1 + (5 * Real.log 2 + 3) / 4 + 1 / (1000 : ℝ) with hK0
  set W0 := 4 * 97 ^ 2 * (2 * Real.log 2 + 1 / 1000) / (4 : ℝ) ^ j with hW0
  set α := a - Real.exp η / 4 - 1 / (2 : ℝ) ^ m - (1 + ρ) * (τ * Real.log 2 + 1 / 2) with hα
  set C0 := K0 + Real.exp η * η * Real.exp (-1) / T + (m + 2) * Real.log 2 + (3 * j + 2) * Real.log 2
    + 4 * (1 + ρ) * Real.log 2 + W0 with hC0
  have he : 0 < Real.exp η := Real.exp_pos η
  have hC0pos : 0 ≤ C0 := by
    simp only [hC0, hK0, hW0]
    have : 0 ≤ Real.log 2 := hlog2.le.trans' (by norm_num)
    positivity
  -- the bracket ≥ αℓ − C0
  have hbr : α * ℓ - C0 ≤ brExpr k j ((2 : ℝ) ^ (3 * j)) ((4 : ℝ) ^ j)
      (((m : ℝ) + 2) * Real.log 2 + ℓ / 2 ^ m) η ℓ := by
    simp only [brExpr, hα, hC0, hK0, hW0, ← hL, ← hρ]
    have h1 : η * Real.exp (-1) / L ≤ η * Real.exp (-1) / T :=
      div_le_div_of_nonneg_left (by positivity) hT hLT
    have h2 : Real.exp η * (ℓ / 4 + η * Real.exp (-1) / L) ≤
        Real.exp η * (ℓ / 4 + η * Real.exp (-1) / T) := by gcongr
    have h3 : (1 + ρ) * (((k : ℝ) + 3) * Real.log 2 + ℓ / 2) ≤
        (1 + ρ) * ((τ * Real.log 2 + 1 / 2) * ℓ + 4 * Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith [mul_le_mul_of_nonneg_right hk2.le (hlog2.le.trans' (by norm_num) : (0 : ℝ) ≤ Real.log 2)]
    have h4 : ℓ / (2 : ℝ) ^ m = 1 / (2 : ℝ) ^ m * ℓ := by ring
    have h5 : Real.exp η * η * Real.exp (-1) / T = Real.exp η * (η * Real.exp (-1) / T) := by ring
    rw [h4, h5]
    nlinarith
  -- D = α − C0/T > 0 from the certificate and c > 0
  set D := α - C0 / T with hD
  have hcert' : c * ((a + b / T) * (a + b / T)) ≤ 2 * η * η * Real.exp (-η) * D := by
    simpa [certTail, hα, hC0, hD, hK0, hW0, hρ, ha_def, hb_def] using hcert
  have hab : 0 < a + b / T := by have : 0 < b / T := div_pos hb0 hT; linarith
  have hD0 : 0 < D := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have : 2 * η * η * Real.exp (-η) * D ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    have : 0 < c * ((a + b / T) * (a + b / T)) := by positivity
    linarith
  -- αℓ − C0 ≥ Dℓ
  have hDℓ : D * ℓ ≤ α * ℓ - C0 := by
    simp only [hD]
    have : C0 ≤ C0 / T * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hT]; exact mul_le_mul_of_nonneg_left hℓT hC0pos
    nlinarith
  -- (aℓ + b) ≤ ℓ (a + b/T)
  have hLℓ : L ≤ ℓ * (a + b / T) := by
    have : b ≤ ℓ * (b / T) := by
      rw [mul_div_assoc', le_div_iff₀ hT]; nlinarith
    nlinarith
  -- conclude
  have hcoef : 0 ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 := by positivity
  calc c ≤ 2 * η * η * Real.exp (-η) * D / ((a + b / T) * (a + b / T)) := by
        rw [le_div_iff₀ (by positivity)]; exact hcert'
    _ ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 * (D * ℓ) := by
        rw [div_le_iff₀ (by positivity)]
        have hL2 : L ^ 2 ≤ (ℓ * (a + b / T)) ^ 2 := pow_le_pow_left₀ hLpos.le hLℓ 2
        have e1 : 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 * (D * ℓ) * ((a + b / T) * (a + b / T)) =
            2 * η * η * Real.exp (-η) * D * ((ℓ * (a + b / T)) ^ 2 / L ^ 2) := by
          field_simp
        rw [e1]
        have : 1 ≤ (ℓ * (a + b / T)) ^ 2 / L ^ 2 := by
          rw [le_div_iff₀ (by positivity)]; linarith
        have h0 : 0 ≤ 2 * η * η * Real.exp (-η) * D := by positivity
        nlinarith
    _ ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 * (α * ℓ - C0) := mul_le_mul_of_nonneg_left hDℓ hcoef
    _ ≤ 2 * η ^ 2 * ℓ * Real.exp (-η) / L ^ 2 * brExpr k j ((2 : ℝ) ^ (3 * j)) ((4 : ℝ) ^ j)
          (((m : ℝ) + 2) * Real.log 2 + ℓ / 2 ^ m) η ℓ := mul_le_mul_of_nonneg_left hbr hcoef
    _ ≤ _ := h

#print axioms gapFrom_join
#print axioms gapOn_of_cert
#print axioms tail_gap

end B4
