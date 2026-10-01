/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialAngleChart
import Mathlib.Analysis.Complex.Isometry

/-!
# A common coordinate chart for two separated balls

An explicit translation and rotation send the source center to zero and the pin center
to the positive horizontal axis. Small balls around these centers then satisfy the
coordinate separation required by the strip-to-angle estimate.
-/

noncomputable section

open Set

namespace FalconerPacking

private theorem rotation_inverse_arg_apply (z : ℂ) :
    rotation (Circle.exp z.arg)⁻¹ z = (‖z‖ : ℂ) := by
  rw [rotation_apply, Circle.coe_inv, Circle.coe_exp]
  calc
    (Complex.exp (z.arg * Complex.I))⁻¹ * z =
        (Complex.exp (z.arg * Complex.I))⁻¹ *
          ((‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖z‖ : ℂ) := by
      rw [mul_left_comm, inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]

/-- The explicit rotation sending `b - a` to the positive horizontal axis. -/
def centerAlignmentRotation (a b : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.symm.trans
    ((rotation (Circle.exp (Complex.orthonormalBasisOneI.repr.symm (b - a)).arg)⁻¹).trans
      Complex.orthonormalBasisOneI.repr)

/-- Translation by the source center followed by the explicit alignment rotation. -/
def centerAlignment (a b : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) :=
  (IsometryEquiv.addRight (-a)).trans (centerAlignmentRotation a b).toIsometryEquiv

@[simp]
theorem centerAlignment_apply (a b x : EuclideanSpace ℝ (Fin 2)) :
    centerAlignment a b x = centerAlignmentRotation a b (x - a) := by
  rfl

@[simp]
theorem centerAlignment_source (a b : EuclideanSpace ℝ (Fin 2)) :
    centerAlignment a b a = 0 := by
  simp

/-- The pin center is sent to `(dist a b, 0)`. -/
theorem centerAlignment_pin (a b : EuclideanSpace ℝ (Fin 2)) :
    centerAlignment a b b = !₂[dist a b, 0] := by
  rw [centerAlignment_apply]
  change Complex.orthonormalBasisOneI.repr
    (rotation (Circle.exp (Complex.orthonormalBasisOneI.repr.symm (b - a)).arg)⁻¹
      (Complex.orthonormalBasisOneI.repr.symm (b - a))) = _
  rw [rotation_inverse_arg_apply, LinearIsometryEquiv.norm_map]
  ext i
  fin_cases i <;> simp [Complex.orthonormalBasisOneI_repr_apply, dist_eq_norm, norm_sub_rev]

theorem abs_first_coordinate_le_norm (z : EuclideanSpace ℝ (Fin 2)) : |z 0| ≤ ‖z‖ := by
  have h := EuclideanSpace.real_norm_sq_eq z
  rw [Fin.sum_univ_two] at h
  nlinarith [sq_nonneg (z 1), sq_abs (z 0), abs_nonneg (z 0), norm_nonneg z]

/-- Source and pin balls of radius at most one eighth of their center separation lie in
one bounded, quantitatively separated coordinate chart. -/
theorem centerAlignment_small_balls
    {a b x y : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hr : r ≤ dist a b / 8)
    (hx : x ∈ Metric.closedBall a r) (hy : y ∈ Metric.closedBall b r) :
    dist a b / 2 ≤ (centerAlignment a b y - centerAlignment a b x) 0 ∧
      ‖centerAlignment a b x‖ ≤ 2 * dist a b ∧
      ‖centerAlignment a b y‖ ≤ 2 * dist a b := by
  let e := centerAlignment a b
  have he0 : e a = 0 := centerAlignment_source a b
  have hxa : ‖e x‖ ≤ r := by
    rw [← dist_zero_right, ← he0, e.dist_eq]
    exact Metric.mem_closedBall.mp hx
  have hyb : ‖e y - e b‖ ≤ r := by
    rw [← dist_eq_norm, e.dist_eq]
    exact Metric.mem_closedBall.mp hy
  have hb : ‖e b‖ = dist a b := by
    rw [← dist_zero_right, ← he0, e.dist_eq]
    exact dist_comm b a
  have hfirst : (e b) 0 = dist a b := by
    rw [show e b = !₂[dist a b, 0] from centerAlignment_pin a b]
    rfl
  have hxc := (abs_le.mp ((abs_first_coordinate_le_norm (e x)).trans hxa)).2
  have hyc := (abs_le.mp ((abs_first_coordinate_le_norm (e y - e b)).trans hyb)).1
  have hynorm : ‖e y‖ ≤ r + dist a b := by
    calc ‖e y‖ ≤ ‖e y - e b‖ + ‖e b‖ := norm_le_norm_sub_add _ _
      _ ≤ r + dist a b := add_le_add hyb hb.le
  change dist a b / 2 ≤ (e y - e x) 0 ∧ ‖e x‖ ≤ _ ∧ ‖e y‖ ≤ _
  simp only [PiLp.sub_apply] at hyc ⊢
  constructor
  · rw [hfirst] at hyc
    linarith [dist_nonneg (x := a) (y := b)]
  constructor <;> linarith [dist_nonneg (x := a) (y := b)]

end FalconerPacking
