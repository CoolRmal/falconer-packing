/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AnisotropicSchwartzKernel
public import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Reproducing kernels for oriented rectangles

The coordinate frame is a linear isometry. Independent positive spatial widths give
an actual linear dilation, whose Jacobian and dual frequency coordinates are computed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Convolution RealInnerProductSpace

namespace FalconerPacking

/-- Independent nonzero dilations of the two Euclidean coordinates. -/
def euclideanCoordinateDilation (w : Fin 2 → ℝ) (hw : ∀ i, w i ≠ 0) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x ↦ WithLp.toLp 2 (fun i ↦ w i * x i)
      invFun := fun x ↦ WithLp.toLp 2 (fun i ↦ (w i)⁻¹ * x i)
      left_inv := by intro x; ext i; simp [hw i]
      right_inv := by intro x; ext i; simp [hw i]
      map_add' := by intro x y; ext i; simp [mul_add]
      map_smul' := by intro c x; ext i; simp [mul_left_comm] }

/-- The dilation acts coordinatewise. -/
theorem euclideanCoordinateDilation_apply (w : Fin 2 → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    euclideanCoordinateDilation w hw x i = w i * x i := rfl

/-- Its inverse acts by the reciprocal coordinates. -/
theorem euclideanCoordinateDilation_symm_apply (w : Fin 2 → ℝ) (hw : ∀ i, w i ≠ 0)
    (x : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (euclideanCoordinateDilation w hw).symm x i = (w i)⁻¹ * x i := rfl

/-- The exact Jacobian of the coordinate dilation is the product of its two factors. -/
theorem euclideanCoordinateDilation_det (w : Fin 2 → ℝ) (hw : ∀ i, w i ≠ 0) :
    (euclideanCoordinateDilation w hw).toLinearEquiv.toLinearMap.det = w 0 * w 1 := by
  have hmap : (euclideanCoordinateDilation w hw).toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin (Matrix.diagonal w) := by
    ext x i
    simp [euclideanCoordinateDilation_apply, Matrix.toLpLin_apply,
      Matrix.mulVec_diagonal]
  rw [hmap, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    Matrix.det_diagonal, Fin.prod_univ_two]

/-- The spatial map for widths a and b in an arbitrary orthonormal coordinate frame. -/
def orientedRectangleDilation
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  O.toContinuousLinearEquiv.trans
    (euclideanCoordinateDilation ![a⁻¹, b⁻¹] (by
      intro i
      fin_cases i <;> simp [ha.ne', hb.ne']))

/-- The first coordinate is the perpendicular displacement in units of the first width. -/
theorem orientedRectangleDilation_apply_zero
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin 2)) :
    orientedRectangleDilation O a b ha hb x 0 = (O x) 0 / a := by
  simp [orientedRectangleDilation, euclideanCoordinateDilation_apply, div_eq_mul_inv,
    mul_comm]

/-- The second coordinate is the parallel displacement in units of the second width. -/
theorem orientedRectangleDilation_apply_one
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin 2)) :
    orientedRectangleDilation O a b ha hb x 1 = (O x) 1 / b := by
  simp [orientedRectangleDilation, euclideanCoordinateDilation_apply, div_eq_mul_inv,
    mul_comm]

/-- The absolute Jacobian is exactly 1/(ab), independently of the orientation. -/
theorem orientedRectangleDilation_abs_det
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    |(orientedRectangleDilation O a b ha hb).toLinearEquiv.toLinearMap.det| =
      (a * b)⁻¹ := by
  have hO : |O.toLinearEquiv.toLinearMap.det| = 1 := by
    rw [← LinearMap.normDet_eq_abs_det]
    exact O.toLinearIsometry.normDet_eq_one
  change |LinearMap.det
    ((euclideanCoordinateDilation ![a⁻¹, b⁻¹] _).toLinearEquiv.toLinearMap.comp
      O.toLinearEquiv.toLinearMap)| = _
  rw [LinearMap.det_comp, abs_mul, hO, mul_one, euclideanCoordinateDilation_det]
  simp [abs_mul, abs_inv, abs_of_pos ha, abs_of_pos hb, mul_comm]

/-- The dual coordinates of the frequency variable are the two widths times its frame
coordinates. -/
theorem orientedRectangleDilation_dual
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (orientedRectangleDilation O a b ha hb).symm.toContinuousLinearMap.adjoint ξ =
      WithLp.toLp 2 ![a * (O ξ) 0, b * (O ξ) 1] := by
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hinverse : O ((orientedRectangleDilation O a b ha hb).symm y) =
      WithLp.toLp 2 ![a * y 0, b * y 1] := by
    ext i
    fin_cases i <;>
      simp [orientedRectangleDilation, euclideanCoordinateDilation_symm_apply]
  rw [← O.inner_map_map, ContinuousLinearEquiv.coe_coe, hinverse]
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm, mul_left_comm, mul_assoc]

/-- The oriented Fourier rectangle expressed by coordinate inequalities is exactly the
unit square condition used by the constructed kernel. -/
theorem orientedRectangleDilation_dual_mem_square_iff
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (∀ i, |((orientedRectangleDilation O a b ha hb).symm.toContinuousLinearMap.adjoint
      ξ) i| ≤ 1) ↔ |(O ξ) 0| ≤ a⁻¹ ∧ |(O ξ) 1| ≤ b⁻¹ := by
  rw [orientedRectangleDilation_dual]
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, abs_mul, abs_of_pos ha, abs_of_pos hb]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨by simpa only [mul_one] using (le_inv_mul_iff₀ ha).mpr h₀,
      by simpa only [mul_one] using (le_inv_mul_iff₀ hb).mpr h₁⟩
  · rintro ⟨h₀, h₁⟩
    exact ⟨(le_inv_mul_iff₀ ha).mp (by simpa only [mul_one] using h₀),
      (le_inv_mul_iff₀ hb).mp (by simpa only [mul_one] using h₁)⟩

/-- The constructed Schwartz kernel for the oriented rectangle with reciprocal frequency widths. -/
def orientedReproducingKernel
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ₀ : EuclideanSpace ℝ (Fin 2)) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  shiftedAnisotropicReproducingKernel (orientedRectangleDilation O a b ha hb) ξ₀

/-- Fourier support in the actual oriented a⁻¹ by b⁻¹ rectangle implies reproduction. -/
theorem orientedReproducingKernel_reproduces
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ₀ : EuclideanSpace ℝ (Fin 2))
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hf : ∀ ξ ∈ Function.support
      (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
      |(O (ξ - ξ₀)) 0| ≤ a⁻¹ ∧ |(O (ξ - ξ₀)) 1| ≤ b⁻¹)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (f ⋆[ContinuousLinearMap.mul ℂ ℂ] orientedReproducingKernel O a b ha hb ξ₀) x =
      f x := by
  apply shiftedAnisotropicReproducingKernel_reproduces
  intro ξ hξ
  exact (orientedRectangleDilation_dual_mem_square_iff O a b ha hb (ξ - ξ₀)).mpr
    (hf ξ hξ)

/-- The oriented kernel has a finite L¹ norm independent of widths, frame, and frequency center. -/
theorem orientedReproducingKernel_lintegral_enorm
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (ξ₀ : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ x, ‖orientedReproducingKernel O a b ha hb ξ₀ x‖ₑ) =
      ∫⁻ x, ‖unitReproducingKernel x‖ₑ :=
  shiftedAnisotropicReproducingKernel_lintegral_enorm _ ξ₀

/-- The rectangle distance is bounded by twice the Euclidean distance in rescaled coordinates. -/
theorem orientedRectangle_distance_le_twice_norm
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : EuclideanSpace ℝ (Fin 2)) :
    |(O x) 0| / a + |(O x) 1| / b ≤ 2 * ‖orientedRectangleDilation O a b ha hb x‖ := by
  have h₀ := PiLp.norm_apply_le (orientedRectangleDilation O a b ha hb x) 0
  have h₁ := PiLp.norm_apply_le (orientedRectangleDilation O a b ha hb x) 1
  simp only [Real.norm_eq_abs, orientedRectangleDilation_apply_zero,
    orientedRectangleDilation_apply_one, abs_div, abs_of_pos ha, abs_of_pos hb] at h₀ h₁
  linarith

/-- Rapid decay in the actual two oriented spatial widths, with constants uniform in all
geometric parameters. -/
theorem orientedReproducingKernel_decay (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (a b : ℝ) (ha : 0 < a) (hb : 0 < b) ξ₀ x,
        ‖orientedReproducingKernel O a b ha hb ξ₀ x‖ ≤
          C / (a * b) / (1 + |(O x) 0| / a + |(O x) 1| / b) ^ m := by
  obtain ⟨C, hC, hdecay⟩ := shiftedAnisotropicReproducingKernel_decay m
  refine ⟨2 ^ m * C, by positivity, ?_⟩
  intro O a b ha hb ξ₀ x
  let A := orientedRectangleDilation O a b ha hb
  have hnorm := hdecay A ξ₀ x
  rw [orientedRectangleDilation_abs_det] at hnorm
  have hscale : (1 + |(O x) 0| / a + |(O x) 1| / b) ^ m ≤
      2 ^ m * (1 + ‖A x‖) ^ m := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have h := orientedRectangle_distance_le_twice_norm O a b ha hb x
    dsimp only [A]
    linarith
  have hratio : C / (1 + ‖A x‖) ^ m ≤
      (2 ^ m * C) / (1 + |(O x) 0| / a + |(O x) 1| / b) ^ m := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      C * (1 + |(O x) 0| / a + |(O x) 1| / b) ^ m ≤
          C * (2 ^ m * (1 + ‖A x‖) ^ m) := mul_le_mul_of_nonneg_left hscale hC.le
      _ = _ := by ring
  calc
    _ ≤ (a * b)⁻¹ * C / (1 + ‖A x‖) ^ m := hnorm
    _ = (a * b)⁻¹ * (C / (1 + ‖A x‖) ^ m) := by ring
    _ ≤ (a * b)⁻¹ *
        ((2 ^ m * C) / (1 + |(O x) 0| / a + |(O x) 1| / b) ^ m) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end FalconerPacking
