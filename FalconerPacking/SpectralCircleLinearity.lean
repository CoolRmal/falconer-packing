/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RemoteSpectralPacket

/-!
# Finite linearity and stable comparison for actual spectral circle extensions
-/

noncomputable section

open MeasureTheory Set Function FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

theorem integrable_circleSpectralExtension_integrand {r : ℝ}
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (y : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun ξ ↦ (𝐞 ⟪ξ, y⟫ : ℂ) * g ξ) (normalizedCircleMeasure r) := by
  have hc : Continuous (fun ξ ↦ (𝐞 ⟪ξ, y⟫ : ℂ)) := by fun_prop
  apply hg.norm.mono' (hc.aestronglyMeasurable.mul hg.aestronglyMeasurable)
  exact ae_of_all _ fun ξ ↦ by simp

theorem integrable_schwartz_normalizedCircleMeasure
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (r : ℝ) :
    Integrable f (normalizedCircleMeasure r) :=
  Integrable.of_bound f.continuous.aestronglyMeasurable (SchwartzMap.seminorm ℝ 0 0 f)
    (ae_of_all _ (SchwartzMap.norm_le_seminorm ℝ f))

theorem circleSpectralExtension_finsetSum {ι : Type*} (I : Finset ι)
    (g : ι → EuclideanSpace ℝ (Fin 2) → ℂ) (r : ℝ)
    (hg : ∀ i ∈ I, Integrable (g i) (normalizedCircleMeasure r))
    (y : EuclideanSpace ℝ (Fin 2)) :
    circleSpectralExtension r (fun ξ ↦ ∑ i ∈ I, g i ξ) y =
      ∑ i ∈ I, circleSpectralExtension r (g i) y := by
  simp only [circleSpectralExtension, Finset.mul_sum]
  exact integral_finsetSum I (fun i hi ↦ integrable_circleSpectralExtension_integrand (hg i hi) y)

theorem circleSpectralExtension_add {r : ℝ}
    {f g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Integrable f (normalizedCircleMeasure r))
    (hg : Integrable g (normalizedCircleMeasure r)) (y : EuclideanSpace ℝ (Fin 2)) :
    circleSpectralExtension r (f + g) y =
      circleSpectralExtension r f y + circleSpectralExtension r g y := by
  simp only [circleSpectralExtension, Pi.add_apply, mul_add]
  exact integral_add (integrable_circleSpectralExtension_integrand hf y)
    (integrable_circleSpectralExtension_integrand hg y)

/-- The pinned spectral average is exactly the extension of the actual Fourier transform. -/
theorem pinnedSpectralCircleAverage_eq_extension
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    pinnedSpectralCircleAverage f y r =
      circleSpectralExtension r (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) y := by
  rw [pinnedSpectralCircleAverage_eq_probability, circleSpectralExtension,
    normalizedCircleMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp only [Circle.smul_def, smul_eq_mul, real_inner_comm, SchwartzMap.fourier_coe]

/-- A finite source packet sum has exactly the sum of its spectral averages. -/
theorem pinnedSpectralCircleAverage_finsetSum {ι : Type*} (I : Finset ι)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    pinnedSpectralCircleAverage
      (∑ i ∈ I, f i : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) y r =
      ∑ i ∈ I, pinnedSpectralCircleAverage (f i) y r := by
  rw [pinnedSpectralCircleAverage_eq_extension, fourier_sum]
  have he : ((∑ i ∈ I, 𝓕 (f i) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
      EuclideanSpace ℝ (Fin 2) → ℂ) = fun ξ ↦ ∑ i ∈ I, (𝓕 (f i)) ξ := by
    ext ξ
    simp
  rw [he, circleSpectralExtension_finsetSum I _ r
    (fun i _ ↦ integrable_schwartz_normalizedCircleMeasure (𝓕 (f i)) r)]
  exact Finset.sum_congr rfl fun i _ ↦ (pinnedSpectralCircleAverage_eq_extension (f i) y r).symm

theorem pinnedSpectralCircleAverage_add
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    pinnedSpectralCircleAverage (f + g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) y r =
      pinnedSpectralCircleAverage f y r + pinnedSpectralCircleAverage g y r := by
  rw [pinnedSpectralCircleAverage_eq_extension, FourierTransform.fourier_add]
  change circleSpectralExtension r
    ((𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) +
      (𝓕 g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) y = _
  rw [circleSpectralExtension_add (integrable_schwartz_normalizedCircleMeasure (𝓕 f) r)
    (integrable_schwartz_normalizedCircleMeasure (𝓕 g) r)]
  rw [pinnedSpectralCircleAverage_eq_extension, pinnedSpectralCircleAverage_eq_extension]

/-- Uniform Fourier error bounds remain uniform after normalized circle extension. -/
theorem norm_circleSpectralExtension_sub_le {r : ℝ}
    {f g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Integrable f (normalizedCircleMeasure r))
    (hg : Integrable g (normalizedCircleMeasure r))
    (y : EuclideanSpace ℝ (Fin 2)) {E : ℝ}
    (hfg : ∀ᵐ ξ ∂normalizedCircleMeasure r, ‖f ξ - g ξ‖ ≤ E) :
    ‖circleSpectralExtension r f y - circleSpectralExtension r g y‖ ≤ E := by
  rw [circleSpectralExtension, circleSpectralExtension, ← integral_sub
    (integrable_circleSpectralExtension_integrand hf y)
    (integrable_circleSpectralExtension_integrand hg y)]
  refine (norm_integral_le_of_norm_le_const (C := E) ?_).trans (by simp)
  filter_upwards [hfg] with ξ hξ
  rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul]
  exact hξ

end FalconerPacking
