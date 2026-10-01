/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicCapKernelBounds
import FalconerPacking.RescaledSchwartzKernel
import FalconerPacking.SourceWavePackets

/-!
# Physical kernels of the actual dyadic caps

The frequency normalization is dual to an explicit spatial dilation. Its Jacobian cancels
in first norms, and its transverse coordinate gives the square-root frequency gain in tails.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The exact spatial dilation dual to the normalization of a standard cap. -/
def capSpatialRescaling (T n N j : ℕ) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  orientedRectangleDilation (circleCapFrame (angularGridPoint N j))
    (Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹ ((2 : ℝ) ^ (T * n))⁻¹
    (by positivity) (by positivity)

/-- Applying the frequency rescaling after the dual spatial map is exactly the identity. -/
theorem capFrequencyRescaling_spatial_dual (T n N j : ℕ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    capFrequencyRescaling T n N j
      ((capSpatialRescaling T n N j).symm.toContinuousLinearMap.adjoint ξ) = ξ := by
  apply (circleCapFrame (angularGridPoint N j)).injective
  ext i
  fin_cases i
  · change circleCapFrame (angularGridPoint N j)
      (capFrequencyRescaling T n N j
        ((capSpatialRescaling T n N j).symm.toContinuousLinearMap.adjoint ξ)) 0 =
      circleCapFrame (angularGridPoint N j) ξ 0
    rw [capFrequencyRescaling_frame_zero]
    simp only [capSpatialRescaling, orientedRectangleDilation_dual,
      Matrix.cons_val_zero]
    simp [show Real.sqrt ((2 : ℝ) ^ (T * n)) ≠ 0 by positivity]
  · change circleCapFrame (angularGridPoint N j)
      (capFrequencyRescaling T n N j
        ((capSpatialRescaling T n N j).symm.toContinuousLinearMap.adjoint ξ)) 1 =
      circleCapFrame (angularGridPoint N j) ξ 1
    rw [capFrequencyRescaling_frame_one]
    simp only [capSpatialRescaling, orientedRectangleDilation_dual,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    simp

/-- The literal inverse Fourier cap kernel is the determinant-normalized spatial rescaling. -/
theorem fourierInv_dyadicAngularCap_eq_rescaled (T n N : ℕ) (hN : 0 < N) (j : ℕ) :
    (𝓕⁻ (dyadicAngularCap T n N hN j) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) =
      rescaledSchwartzKernel (capSpatialRescaling T n N j)
        (𝓕⁻ (rescaledDyadicAngularCap T n N hN j)) := by
  apply fourierInv_eq_rescaledSchwartzKernel
  intro ξ
  rw [rescaledDyadicAngularCap_apply, capFrequencyRescaling_spatial_dual]

/-- First norms of the physical cap kernels equal those of the normalized family exactly. -/
theorem lintegral_enorm_fourierInv_dyadicAngularCap (T n N : ℕ) (hN : 0 < N) (j : ℕ) :
    (∫⁻ x, ‖(𝓕⁻ (dyadicAngularCap T n N hN j) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) =
    ∫⁻ x, ‖(𝓕⁻ (rescaledDyadicAngularCap T n N hN j) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ := by
  rw [fourierInv_dyadicAngularCap_eq_rescaled, lintegral_enorm_rescaledSchwartzKernel]

/-- The packet normal is minus the first coordinate vector in the cap frame. -/
theorem circleCapFrame_sourceWavePacketNormal (N j : ℕ) :
    circleCapFrame (angularGridPoint N j) (sourceWavePacketNormal N j) =
      WithLp.toLp 2 ![-1, 0] := by
  simp only [sourceWavePacketNormal, circleCapFrame, planarRotation_angularDirection]
  rw [show Real.pi / 2 - angularGridPoint N j +
    (angularGridPoint N j + Real.pi / 2) = Real.pi by ring]
  ext i
  fin_cases i <;> simp [angularDirection_apply_zero, angularDirection_apply_one]

/-- The physical transverse coordinate is the absolute value of the packet normal component. -/
theorem abs_inner_sourceWavePacketNormal (N j : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    |⟪sourceWavePacketNormal N j, x⟫| =
      |circleCapFrame (angularGridPoint N j) x 0| := by
  rw [← (circleCapFrame (angularGridPoint N j)).inner_map_map,
    circleCapFrame_sourceWavePacketNormal]
  simp [PiLp.inner_apply, Fin.sum_univ_two]

/-- The first rescaled spatial coordinate is the physical normal component times sqrt R. -/
theorem capSpatialRescaling_transverse (T n N j : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    |capSpatialRescaling T n N j x 0| =
      Real.sqrt ((2 : ℝ) ^ (T * n)) * |⟪sourceWavePacketNormal N j, x⟫| := by
  rw [capSpatialRescaling, orientedRectangleDilation_apply_zero,
    abs_div, abs_inv, abs_of_pos (by positivity : 0 < Real.sqrt ((2 : ℝ) ^ (T * n))),
    div_inv_eq_mul, abs_inner_sourceWavePacketNormal, mul_comm]

/-- Uniform actual cap first norms follow without any assumed physical kernel estimate. -/
theorem dyadicCapKernel_uniform_lintegral {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i))) :
    ∃ C > 0, ∀ i,
      (∫⁻ x, ‖(𝓕⁻ (dyadicAngularCap T (n i) (N i) (hN i) (j i)) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := (rescaledDyadicCapKernel_uniform_integral_bounds
    T hK n N j hN hwidth hsmall hupper 0).1
  refine ⟨C, hC, fun i ↦ ?_⟩
  rw [lintegral_enorm_fourierInv_dyadicAngularCap]
  exact hc i

/-- Transverse tails transform exactly to the fixed transverse coordinate. -/
theorem lintegral_transverse_tail_fourierInv_dyadicAngularCap
    (T n N : ℕ) (hN : 0 < N) (j : ℕ) (w : ℝ) :
    (∫⁻ x in {x | w ≤ |⟪sourceWavePacketNormal N j, x⟫|},
      ‖(𝓕⁻ (dyadicAngularCap T n N hN j) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) =
    ∫⁻ z in {z : EuclideanSpace ℝ (Fin 2) |
      Real.sqrt ((2 : ℝ) ^ (T * n)) * w ≤ |z 0|},
      ‖(𝓕⁻ (rescaledDyadicAngularCap T n N hN j) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) z‖ₑ := by
  let S := {z : EuclideanSpace ℝ (Fin 2) |
    Real.sqrt ((2 : ℝ) ^ (T * n)) * w ≤ |z 0|}
  have hS : MeasurableSet S := isClosed_le continuous_const (by fun_prop) |>.measurableSet
  have he : (capSpatialRescaling T n N j) ⁻¹' S =
      {x | w ≤ |⟪sourceWavePacketNormal N j, x⟫|} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq, S, capSpatialRescaling_transverse]
    exact mul_le_mul_iff_right₀ (by positivity)
  rw [fourierInv_dyadicAngularCap_eq_rescaled, ← he]
  exact setLIntegral_enorm_rescaledSchwartzKernel _ _ hS

/-- Every power of transverse decay holds for the actual physical cap kernels. -/
theorem dyadicCapKernel_uniform_transverse_tail {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i)))
    (m : ℕ) :
    ∃ C > 0, ∀ i (w : ℝ), 0 < w →
      (∫⁻ x in {x | w ≤ |⟪sourceWavePacketNormal (N i) (j i), x⟫|},
        ‖(𝓕⁻ (dyadicAngularCap T (n i) (N i) (hN i) (j i)) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤
        ENNReal.ofReal (C / (Real.sqrt ((2 : ℝ) ^ (T * n i)) * w) ^ m) := by
  obtain ⟨C, hC, hc⟩ := (rescaledDyadicCapKernel_uniform_integral_bounds
    T hK n N j hN hwidth hsmall hupper m).2
  refine ⟨C, hC, fun i w hw ↦ ?_⟩
  rw [lintegral_transverse_tail_fourierInv_dyadicAngularCap]
  have he (z : EuclideanSpace ℝ (Fin 2)) : ⟪angularDirection 0, z⟫ = z 0 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, angularDirection_apply_zero,
      angularDirection_apply_one]
  simpa only [he] using hc i (angularDirection 0) (by simp) _ (by positivity)

end FalconerPacking
