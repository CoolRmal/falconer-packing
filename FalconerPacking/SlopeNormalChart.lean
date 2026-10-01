/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SlopeTubeNet

/-!
# Quantitative slope charts for every unit normal

One coordinate of a planar unit normal has absolute value at least one half. Dividing by
that coordinate gives a bounded slope, and the concrete slope net approximates its normal form.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- Every unit normal gives a bounded-slope linear form with a uniformly nonzero factor. -/
theorem exists_slope_chart_unit_normal (e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) :
    ∃ (c : Bool) (t v : ℝ), |t| ≤ 1 ∧ 1 / 2 ≤ |v| ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), ⟪e, x⟫ = v * slopeLinearCoordinate c t x := by
  have hsum : 1 ≤ |e 0| + |e 1| := by
    simpa [slopeCoordinate, dist_zero_right, he] using
      dist_le_sum_abs_slopeCoordinates false e 0
  by_cases h : |e 1| ≤ |e 0|
  · have hv : (1 / 2 : ℝ) ≤ |e 0| := by linarith
    have hn : e 0 ≠ 0 := by intro hz; norm_num [hz] at hv
    refine ⟨false, -(e 1) / e 0, e 0, ?_, hv, ?_⟩
    · rw [abs_div, abs_neg, div_le_one (abs_pos.mpr hn)]
      exact h
    · intro x
      simp only [slopeLinearCoordinate, slopeCoordinate, Bool.false_eq_true, if_false,
        Bool.not_false, if_true, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
      field_simp
      ring
  · have hv : (1 / 2 : ℝ) ≤ |e 1| := by linarith
    have hn : e 1 ≠ 0 := by intro hz; norm_num [hz] at hv
    refine ⟨true, -(e 0) / e 1, e 1, ?_, hv, ?_⟩
    · rw [abs_div, abs_neg, div_le_one (abs_pos.mpr hn)]
      exact (lt_of_not_ge h).le
    · intro x
      simp only [slopeLinearCoordinate, slopeCoordinate, if_true, Bool.not_true,
        Bool.false_eq_true, if_false, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
      field_simp
      ring

/-- The concrete slope grid approximates an arbitrary unit-normal coordinate uniformly. -/
theorem exists_slopeNet_unit_normal_bound {M : ℕ} (hM : 0 < M)
    (e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) :
    ∃ c : Bool, ∃ k ∈ slopeNet M, ∀ z : EuclideanSpace ℝ (Fin 2),
      |slopeLinearCoordinate c ((k : ℝ) / M) z| ≤ 2 * |⟪e, z⟫| + ‖z‖ / M := by
  obtain ⟨c, t, v, ht, hv, hid⟩ := exists_slope_chart_unit_normal e he
  obtain ⟨k, hk, hkt⟩ := exists_slopeNet_approx hM ht
  refine ⟨c, k, hk, fun z ↦ ?_⟩
  have horig : |slopeLinearCoordinate c t z| ≤ 2 * |⟪e, z⟫| := by
    rw [hid, abs_mul]
    nlinarith [abs_nonneg (slopeLinearCoordinate c t z)]
  have herror : |slopeLinearCoordinate c ((k : ℝ) / M) z -
      slopeLinearCoordinate c t z| ≤ ‖z‖ / M := by
    apply (abs_slopeLinearCoordinate_change_le c ((k : ℝ) / M) t z).trans
    have hk' : |(k : ℝ) / M - t| ≤ 1 / M := by rwa [abs_sub_comm]
    simpa only [one_div_mul_eq_div, mul_comm] using
      mul_le_mul_of_nonneg_right hk' (norm_nonneg z)
  have htri := abs_add_le (slopeLinearCoordinate c t z)
    (slopeLinearCoordinate c ((k : ℝ) / M) z - slopeLinearCoordinate c t z)
  rw [add_sub_cancel] at htri
  exact htri.trans (add_le_add horig herror)

end FalconerPacking
