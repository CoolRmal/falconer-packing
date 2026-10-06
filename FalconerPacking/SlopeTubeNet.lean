/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SlopeStripGeometry
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Coverage and approximation by the explicit slope net

Every bounded slope is approximated at spacing `1/M`. Together the two charts cover all
unoriented lines. Parallel strip offsets cover the entire support ball at every net slope.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace FalconerPacking

/-- The uniform integer slope grid approximates every slope in the chart. -/
theorem exists_slopeNet_approx {M : ℕ} (hM : 0 < M) {t : ℝ} (ht : |t| ≤ 1) :
    ∃ k ∈ slopeNet M, |t - (k : ℝ) / M| ≤ 1 / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let k : ℤ := ⌊(M : ℝ) * t⌋
  have hfloor : (k : ℝ) ≤ (M : ℝ) * t := Int.floor_le _
  have hfloor' : (M : ℝ) * t < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hlow : -(M : ℤ) ≤ k := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith [(abs_le.mp ht).1]
  have hupp : k ≤ (M : ℤ) := by
    have h : (k : ℝ) ≤ M := by nlinarith [(abs_le.mp ht).2]
    exact_mod_cast h
  refine ⟨k, Finset.mem_Icc.mpr ⟨hlow, hupp⟩, ?_⟩
  rw [abs_le]
  constructor
  · have h : (k : ℝ) / M ≤ t := (div_le_iff₀ hMr).mpr (by nlinarith)
    have : 0 < (1 : ℝ) / M := one_div_pos.mpr hMr
    linarith
  · apply (le_div_iff₀ hMr).mpr
    have he : (t - (k : ℝ) / M) * M = t * M - k := by field_simp
    rw [he]
    linarith

theorem abs_slopeCoordinate_le_norm (c : Bool) (x : EuclideanSpace ℝ (Fin 2)) :
    |slopeCoordinate c x| ≤ ‖x‖ := by
  cases c <;> simpa [slopeCoordinate, Real.norm_eq_abs] using PiLp.norm_apply_le x _

/-- Bounded slope changes have their expected normal-coordinate error. -/
theorem abs_slopeLinearCoordinate_change_le (c : Bool) (s t : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    |slopeLinearCoordinate c s x - slopeLinearCoordinate c t x| ≤ |s - t| * ‖x‖ := by
  have he : slopeLinearCoordinate c s x - slopeLinearCoordinate c t x =
      (t - s) * slopeCoordinate (!c) x := by unfold slopeLinearCoordinate; ring
  rw [he, abs_mul, abs_sub_comm t s]
  exact mul_le_mul_of_nonneg_left (abs_slopeCoordinate_le_norm (!c) x) (abs_nonneg _)

/-- Every unoriented line has a bounded-slope representative in one of the two charts. -/
theorem exists_slope_chart (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    ∃ c : Bool, ∃ t : ℝ, |t| ≤ 1 ∧ slopeLinearCoordinate c t x = 0 := by
  have hcoords : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp [h.1, h.2]
  by_cases h : |x 0| ≤ |x 1|
  · have hx1 : x 1 ≠ 0 := by
      intro he
      have hx0 : x 0 = 0 := abs_eq_zero.mp (by simpa [he] using h)
      exact hcoords.elim (fun hz ↦ hz hx0) (fun hz ↦ hz he)
    refine ⟨false, x 0 / x 1, ?_, ?_⟩
    · rw [abs_div, div_le_one (abs_pos.mpr hx1)]
      exact h
    · simp [slopeLinearCoordinate, slopeCoordinate, hx1]
  · have hx0 : x 0 ≠ 0 := by intro he; simp [he] at h
    refine ⟨true, x 1 / x 0, ?_, ?_⟩
    · rw [abs_div, div_le_one (abs_pos.mpr hx0)]
      exact (lt_of_not_ge h).le
    · simp [slopeLinearCoordinate, slopeCoordinate, hx0]

/-- The concrete net approximates every line with normal error at most `norm/M`. -/
theorem exists_slopeNet_normal_error {M : ℕ} (hM : 0 < M)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ≠ 0) :
    ∃ c : Bool, ∃ k ∈ slopeNet M,
      |slopeLinearCoordinate c ((k : ℝ) / M) x| ≤ ‖x‖ / M := by
  obtain ⟨c, t, ht, he⟩ := exists_slope_chart x hx
  obtain ⟨k, hk, hkt⟩ := exists_slopeNet_approx hM ht
  refine ⟨c, k, hk, ?_⟩
  have h := abs_slopeLinearCoordinate_change_le c ((k : ℝ) / M) t x
  rw [he, sub_zero] at h
  have hkt' : |(k : ℝ) / M - t| ≤ 1 / M := by rwa [abs_sub_comm]
  exact h.trans (by simpa [div_eq_mul_inv, mul_comm] using
    (mul_le_mul_of_nonneg_right hkt' (norm_nonneg x)))

/-- Every point in the support ball lies in a labeled strip at every net slope. -/
theorem exists_slopeStrip_cover {o x : EuclideanSpace ℝ (Fin 2)} {b : ℝ}
    (hb : 0 < b) {M : ℕ} (hM : 0 < M) (c : Bool) {k : ℤ}
    (hk : k ∈ slopeNet M) (hx : x ∈ Metric.ball o b) :
    ∃ l : ℤ, (k, l) ∈ slopeStripLabels M ∧ x ∈ slopeStrip o b M c (k, l) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 0 < b / M := div_pos hb hMr
  let v := slopeLinearCoordinate c ((k : ℝ) / M) (x - o)
  have hv : |v| ≤ 2 * b := by
    have hnorm : ‖x - o‖ < b := by simpa [dist_eq_norm] using hx
    calc
      _ ≤ |slopeCoordinate c (x - o)| +
          |(k : ℝ) / M * slopeCoordinate (!c) (x - o)| := abs_sub _ _
      _ ≤ ‖x - o‖ + ‖x - o‖ := by
        apply add_le_add (abs_slopeCoordinate_le_norm c (x - o))
        rw [abs_mul]
        calc
          _ ≤ 1 * |slopeCoordinate (!c) (x - o)| :=
            mul_le_mul_of_nonneg_right (abs_slope_le_one hM hk) (abs_nonneg _)
          _ ≤ _ := by simpa using abs_slopeCoordinate_le_norm (!c) (x - o)
      _ ≤ _ := by linarith
  let z := v / (b / M)
  have hz : |z| ≤ 2 * M := by
    change |v / (b / M)| ≤ _
    rw [abs_div, abs_of_pos ha]
    apply (div_le_iff₀ ha).mpr
    have he : (2 * (M : ℝ)) * (b / M) = 2 * b := by field_simp
    rwa [he]
  let l : ℤ := ⌊z⌋
  have hl : (l : ℝ) ≤ z := Int.floor_le z
  have hl' : z < (l : ℝ) + 1 := Int.lt_floor_add_one z
  have hlowr : -(3 * (M : ℝ)) ≤ l := by linarith [(abs_le.mp hz).1]
  have huppr : (l : ℝ) ≤ 3 * M := by linarith [(abs_le.mp hz).2]
  have hlow : -(3 * (M : ℤ)) ≤ l := by exact_mod_cast hlowr
  have hupp : l ≤ 3 * (M : ℤ) := by exact_mod_cast huppr
  refine ⟨l, Finset.mem_product.mpr ⟨hk, Finset.mem_Icc.mpr ⟨hlow, hupp⟩⟩, hx, ?_, ?_⟩
  · exact (le_div_iff₀ ha).mp hl
  · exact (div_lt_iff₀ ha).mp hl'

end FalconerPacking
