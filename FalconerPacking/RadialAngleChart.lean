/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A quantitative right-half-plane chart for radial angles

Positive first-coordinate separation fixes the argument branch. The angle difference
is bounded by the determinant divided by the two separated first coordinates.
-/

@[expose] public section

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- Arctangent is globally one-Lipschitz. -/
theorem lipschitzWith_arctan : LipschitzWith 1 Real.arctan := by
  apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
  intro t
  rw [Real.deriv_arctan]
  change |1 / (1 + t ^ 2)| ≤ 1
  rw [abs_of_pos (by positivity)]
  exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg t])

theorem abs_arctan_sub_arctan_le (a b : ℝ) :
    |Real.arctan a - Real.arctan b| ≤ |a - b| := by
  simpa only [Real.dist_eq, one_mul, NNReal.coe_one] using
    lipschitzWith_arctan.dist_le_mul a b

/-- The positive real half-plane uses precisely the ordinary arctangent branch. -/
theorem complex_arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  have h := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  rw [← Complex.tan_arg, Real.arctan_tan h.1 h.2]

/-- Existing radial angles are arctangents of slopes in the separated right-half-plane chart. -/
theorem radialAngle_eq_arctan_of_coord_pos
    {y x : EuclideanSpace ℝ (Fin 2)} (h : 0 < (y - x) 0) :
    radialAngle y x = Real.arctan ((y - x) 1 / (y - x) 0) := by
  have hr : (Complex.orthonormalBasisOneI.repr.symm (y - x)).re = (y - x) 0 := by
    simp [Complex.orthonormalBasisOneI_repr_symm_apply]
  have hi : (Complex.orthonormalBasisOneI.repr.symm (y - x)).im = (y - x) 1 := by
    simp [Complex.orthonormalBasisOneI_repr_symm_apply]
  rw [radialAngle, complex_arg_eq_arctan_of_re_pos (by rwa [hr]), hr, hi]

/-- The angular chart is controlled by the actual two-dimensional determinant. -/
theorem radialAngle_sub_le_det
    {y x x' : EuclideanSpace ℝ (Fin 2)} {δ : ℝ} (hδ : 0 < δ)
    (hx : δ ≤ (y - x) 0) (hx' : δ ≤ (y - x') 0) :
    |radialAngle y x - radialAngle y x'| ≤
      |(y - x) 1 * (y - x') 0 - (y - x') 1 * (y - x) 0| / δ ^ 2 := by
  have h₀ := hδ.trans_le hx
  have h₁ := hδ.trans_le hx'
  rw [radialAngle_eq_arctan_of_coord_pos h₀, radialAngle_eq_arctan_of_coord_pos h₁]
  refine (abs_arctan_sub_arctan_le _ _).trans ?_
  rw [div_sub_div _ _ h₀.ne' h₁.ne', abs_div, abs_mul,
    abs_of_pos h₀, abs_of_pos h₁]
  rw [mul_comm ((y - x) 0) ((y - x') 1)]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hδ)
  nlinarith [mul_le_mul hx hx' hδ.le h₀.le]

end FalconerPacking
