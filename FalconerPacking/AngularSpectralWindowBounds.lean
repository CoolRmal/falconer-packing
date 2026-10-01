/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularSpectralSelector
import FalconerPacking.RadialPlancherel

/-!
# Uniform finite-order bounds for the angular spectral selector

The actual real and complex angular windows are integrable on the normalized circle. Their
closed supports remain in the enlarged cap, and a single constant bounds every derivative up
to any prescribed finite order.
-/

noncomputable section

open Set Function MeasureTheory
open scoped ContDiff

namespace FalconerPacking

theorem angularSpectralWindow_mem_Icc (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) :
    angularSpectralWindow S c θ ∈ Icc (0 : ℝ) 1 :=
  ⟨angularUnitBump.nonneg, angularUnitBump.le_one⟩

/-- The actual complexified window is bounded by one in norm. -/
theorem norm_complex_angularSpectralWindow_le_one
    (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) :
    ‖(angularSpectralWindow S c θ : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (angularSpectralWindow_mem_Icc S c θ).1]
  exact (angularSpectralWindow_mem_Icc S c θ).2

/-- Closing the support introduces only the boundary of the enlarged chord cap. -/
theorem tsupport_complex_angularSpectralWindow_subset {S : ℝ} (hS : 0 < S)
    (c : EuclideanSpace ℝ (Fin 2)) :
    tsupport (fun θ ↦ (angularSpectralWindow S c θ : ℂ)) ⊆
      {θ | ‖angularDirection θ - c‖ ≤ 16 * Real.pi / S} := by
  apply closure_minimal
  · intro θ hθ
    have hne : angularSpectralWindow S c θ ≠ 0 := by simpa using hθ
    have hs := angularSpectralSelector_support hS
      (ξ := angularDirection θ) (c := c) (by
        simpa [angularSpectralSelector, angularSpectralWindow] using hne)
    simpa using hs.le
  · exact isClosed_le ((continuous_angularDirection.sub continuous_const).norm) continuous_const

/-- Both the real window and its complexification are integrable against normalized angle. -/
theorem integrable_angularSpectralWindow (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) :
    Integrable (angularSpectralWindow S c) radialAngularProbability ∧
      Integrable (fun θ ↦ (angularSpectralWindow S c θ : ℂ)) radialAngularProbability := by
  have hc : Integrable (fun θ ↦ (angularSpectralWindow S c θ : ℂ))
      radialAngularProbability :=
    (integrable_const (1 : ℝ)).mono'
      (Complex.continuous_ofReal.comp
        (contDiff_angularSpectralWindow S c).continuous).aestronglyMeasurable
      (ae_of_all _ (norm_complex_angularSpectralWindow_le_one S c))
  exact ⟨by simpa using hc.re, hc⟩

/-- One scale-independent constant controls all angular derivatives through order `N`. -/
theorem angularSpectralWindow_finite_derivative_bound (N : ℕ) :
    ∃ C > 0, ∀ S : ℝ, 1 ≤ S → ∀ (c : EuclideanSpace ℝ (Fin 2)) (k : ℕ), k ≤ N →
      ∀ θ, ‖iteratedDeriv k (angularSpectralWindow S c) θ‖ ≤ C * S ^ k := by
  choose B hB hbound using angularSpectralWindow_derivative_bound
  refine ⟨1 + ∑ k ∈ Finset.range (N + 1), B k, ?_, ?_⟩
  · have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (N + 1)) ↦ (hB k).le)
    linarith
  intro S hS c k hk θ
  apply (hbound k S hS c θ).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) k)
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (N + 1)) ↦ (hB j).le)
    (show k ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  linarith

end FalconerPacking
