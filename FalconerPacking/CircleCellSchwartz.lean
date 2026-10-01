/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleSpectralSchwartz
import FalconerPacking.AngularGridGeometry

/-!
# Actual angular-cell circle pieces

The half-open angular grid gives measurable spectral indicators. Convolution with the
fixed compact smooth bump yields genuine Schwartz pieces and an exact physical sum.
-/

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Classical
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The planar frequencies assigned to one half-open angular cell. -/
def circleAngularCell (N j : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun ξ ↦ radialAngle ξ 0) ⁻¹' angularGridCell N j

theorem measurableSet_circleAngularCell (N j : ℕ) :
    MeasurableSet (circleAngularCell N j) :=
  measurable_radialAngle.of_uncurry_right measurableSet_Ioc

/-- Fine angular data use genuine indicators, without smoothing their boundaries. -/
def circleCellData (N j : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  (circleAngularCell N j).indicator g

theorem integrable_circleCellData {r : ℝ} {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (N j : ℕ) :
    Integrable (circleCellData N j g) (normalizedCircleMeasure r) :=
  hg.indicator (measurableSet_circleAngularCell N j)

/-- Every planar frequency belongs to exactly one cell, including all boundary points. -/
theorem sum_circleCellData {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, circleCellData N j g ξ = g ξ := by
  have hθ := radialAngle_mem ξ 0
  rw [← biUnion_angularGridCell hN] at hθ
  obtain ⟨j, hj, hθ⟩ := mem_iUnion₂.mp hθ
  rw [Finset.sum_eq_single_of_mem j hj]
  · exact indicator_of_mem (show ξ ∈ circleAngularCell N j from hθ) g
  · intro i hi hij
    have hnot : radialAngle ξ 0 ∉ angularGridCell N i := by
      intro hθi
      exact Set.disjoint_left.mp (disjoint_angularGridCell N hij) hθi hθ
    exact indicator_of_notMem (show ξ ∉ circleAngularCell N i from hnot) g

/-- Angular restriction preserves measurability. -/
theorem measurable_circleCellData {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Measurable g) (N j : ℕ) : Measurable (circleCellData N j g) :=
  hg.indicator (measurableSet_circleAngularCell N j)

/-- Pointwise squared spectral mass is conserved by the disjoint angular partition. -/
theorem sum_circleCellData_norm_sq {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, ‖circleCellData N j g ξ‖ ^ 2 = ‖g ξ‖ ^ 2 := by
  have hθ := radialAngle_mem ξ 0
  rw [← biUnion_angularGridCell hN] at hθ
  obtain ⟨j, hj, hθ⟩ := mem_iUnion₂.mp hθ
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [circleCellData, indicator_of_mem (show ξ ∈ circleAngularCell N j from hθ)]
  · intro i hi hij
    have hnot : ξ ∉ circleAngularCell N i := by
      intro hθi
      exact Set.disjoint_left.mp (disjoint_angularGridCell N hij) hθi hθ
    simp only [circleCellData, indicator_of_notMem hnot, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Actual physical Schwartz pieces for the angular cells. -/
def circleCellPhysicalSchwartz (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (N j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  circlePhysicalSchwartz r (integrable_circleCellData hg N j) k hk

/-- Fourier transformation gives the actual cell convolution. -/
theorem fourier_circleCellPhysicalSchwartz_apply (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (N j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (circleCellPhysicalSchwartz r hg N j k hk) ξ =
      ∫ ζ, circleCellData N j g ζ * k (ξ - ζ) ∂normalizedCircleMeasure r := by
  rw [circleCellPhysicalSchwartz, fourier_circlePhysicalSchwartz,
    circleSpectralSchwartz_apply]
  rfl

/-- The circle extension commutes with this actual finite angular partition. -/
theorem sum_circleCellExtension {N : ℕ} (hN : 0 < N) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (x : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, circleSpectralExtension r (circleCellData N j g) x =
      circleSpectralExtension r g x := by
  have hi (j : ℕ) : Integrable
      (fun ξ ↦ (𝐞 ⟪ξ, x⟫ : ℂ) * circleCellData N j g ξ)
      (normalizedCircleMeasure r) :=
    (integrable_circleCellData hg N j).bdd_mul (c := 1)
      (by fun_prop) (ae_of_all _ fun ξ ↦ by simp)
  simp only [circleSpectralExtension]
  rw [← integral_finsetSum (Finset.range N) (fun j _ ↦ hi j)]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ ↦ by
    dsimp only
    rw [← Finset.mul_sum, sum_circleCellData hN]

/-- The physical cell functions reconstruct the original cutoff extension exactly. -/
theorem sum_circleCellPhysicalSchwartz {N : ℕ} (hN : 0 < N) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k) :
    ∑ j ∈ Finset.range N, circleCellPhysicalSchwartz r hg N j k hk =
      circlePhysicalSchwartz r hg k hk := by
  ext x
  simp only [sum_apply, circleCellPhysicalSchwartz, circlePhysicalSchwartz_apply]
  rw [← Finset.mul_sum, sum_circleCellExtension hN r hg]

/-- Positive-radius circle points have their exact radial-angle representation. -/
theorem ae_circle_radial_representation {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ξ ∂normalizedCircleMeasure r, ξ = r • angularDirection (radialAngle ξ 0) := by
  have hn : ∀ᵐ ξ ∂normalizedCircleMeasure r, ‖ξ‖ = r := by
    rw [normalizedCircleMeasure, ae_map_iff (by fun_prop) (by measurability)]
    exact ae_of_all _ fun θ ↦ by simp [norm_smul, hr.le]
  filter_upwards [hn] with ξ hξ
  have hne : ξ ≠ 0 := by
    intro he
    exact hr.ne' (by simpa only [he, norm_zero] using hξ.symm)
  rw [angularDirection_radialAngle hne, sub_zero, hξ, smul_smul,
    mul_inv_cancel₀ hr.ne', one_smul]

end FalconerPacking
