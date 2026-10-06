/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.EnlargedSlopeTubeGeometry
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Actual unit normals and centers for the enlarged slope tubes

The coordinate normal of a slope chart is normalized explicitly. The resulting physical
strip contains the finite union used in the energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The coordinate normal representing a slope chart's exact linear form. -/
def slopeNormalVector (c : Bool) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (if c then ![-t, 1] else ![1, -t])

theorem inner_slopeNormalVector (c : Bool) (t : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪slopeNormalVector c t, x⟫ = slopeLinearCoordinate c t x := by
  cases c <;>
    simp [slopeNormalVector, slopeLinearCoordinate, slopeCoordinate,
      PiLp.inner_apply, Fin.sum_univ_two] <;> ring

theorem one_le_norm_slopeNormalVector (c : Bool) (t : ℝ) :
    1 ≤ ‖slopeNormalVector c t‖ := by
  cases c
  · simpa [slopeNormalVector] using PiLp.norm_apply_le (slopeNormalVector false t) 0
  · simpa [slopeNormalVector] using PiLp.norm_apply_le (slopeNormalVector true t) 1

/-- The unit normal of the actual slope strip. -/
def slopeUnitNormal (c : Bool) (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  NormedSpace.normalize (slopeNormalVector c t)

theorem norm_slopeUnitNormal (c : Bool) (t : ℝ) : ‖slopeUnitNormal c t‖ = 1 := by
  apply NormedSpace.norm_normalize
  apply norm_ne_zero_iff.mp
  exact ne_of_gt ((by norm_num : (0 : ℝ) < 1).trans_le (one_le_norm_slopeNormalVector c t))

theorem inner_slopeUnitNormal (c : Bool) (t : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪slopeUnitNormal c t, x⟫ = slopeLinearCoordinate c t x / ‖slopeNormalVector c t‖ := by
  simp [slopeUnitNormal, NormedSpace.normalize, inner_smul_left, inner_slopeNormalVector,
    div_eq_mul_inv, mul_comm]

/-- A point on the nominal center line of the actual finite-grid tube. -/
def slopeTubeCenter (o : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (M : ℕ)
    (i : Bool × (ℤ × ℤ)) : EuclideanSpace ℝ (Fin 2) :=
  o + ((i.2.2 : ℝ) * (b / M) / ‖slopeNormalVector i.1 ((i.2.1 : ℝ) / M)‖) •
    slopeUnitNormal i.1 ((i.2.1 : ℝ) / M)

/-- The centered physical normal form equals the normalized slope coordinate exactly. -/
theorem inner_slopeUnitNormal_sub_center
    (o x : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (M : ℕ) (i : Bool × (ℤ × ℤ)) :
    ⟪slopeUnitNormal i.1 ((i.2.1 : ℝ) / M), x - slopeTubeCenter o b M i⟫ =
      (slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) (x - o) -
        (i.2.2 : ℝ) * (b / M)) / ‖slopeNormalVector i.1 ((i.2.1 : ℝ) / M)‖ := by
  rw [slopeTubeCenter, sub_add_eq_sub_sub, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_slopeUnitNormal, one_pow, mul_one,
    inner_slopeUnitNormal, sub_div]

/-- The actual finite enlargement lies in the asserted physical unit-normal strip. -/
theorem enlargedSlopeTube_unit_normal_bound
    {o x : EuclideanSpace ℝ (Fin 2)} {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) {L : ℕ} {i : Bool × (ℤ × ℤ)}
    (hx : x ∈ enlargedSlopeTube o b M L i) :
    |⟪slopeUnitNormal i.1 ((i.2.1 : ℝ) / M), x - slopeTubeCenter o b M i⟫| ≤
      (L + 1) * (b / M) := by
  have hn := one_le_norm_slopeNormalVector i.1 ((i.2.1 : ℝ) / M)
  have hnpos : 0 < ‖slopeNormalVector i.1 ((i.2.1 : ℝ) / M)‖ := by linarith
  rw [inner_slopeUnitNormal_sub_center, abs_div, abs_of_pos hnpos]
  apply (div_le_self (abs_nonneg _) hn).trans
  exact (enlargedSlopeTube_normal_bound hb hM hx).2

end FalconerPacking
