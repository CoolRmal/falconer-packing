/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleCellSchwartz

/-!
# Terminal energy for the actual angular partition

A finite source has integrable circle data. The exact disjoint angular indicators have
squared multiplier sum one, so the terminal circle estimate applies without an assumed
partition or multiplier overlap bound.
-/

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Classical
open scoped ENNReal FourierTransform

namespace FalconerPacking

/-- Fourier data of a finite source are integrable on every normalized circle. -/
theorem integrable_circle_planarMeasureFourier
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (r : ℝ) :
    Integrable (planarMeasureFourier μ) (normalizedCircleMeasure r) :=
  (integrable_const (μ.real univ)).mono'
    (continuous_planarMeasureFourier μ).aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ norm_planarMeasureFourier_le μ ξ)

/-- Multiplying the cell indicator by the data is exactly the cell-restricted data. -/
theorem circleCellData_indicator_mul (N j : ℕ)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    (fun ξ ↦ circleCellData N j (fun _ ↦ 1) ξ * g ξ) = circleCellData N j g := by
  funext ξ
  by_cases hξ : ξ ∈ circleAngularCell N j <;> simp [circleCellData, hξ]

/-- The actual finite collection of angular-cell Schwartz functions obeys the terminal
circle energy estimate with multiplier constant exactly one. -/
theorem sum_circleCellPhysicalSchwartz_energy_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ closedBall 0 a) :
    (∑ j ∈ Finset.range N, ∫⁻ x,
      ‖circleCellPhysicalSchwartz r (integrable_circle_planarMeasureFourier μ r) N j k
        (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 a) hk) x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability := by
  have hm (j : ℕ) : Measurable (circleCellData N j (fun _ ↦ 1)) :=
    measurable_circleCellData measurable_const N j
  have hB (ξ : EuclideanSpace ℝ (Fin 2)) :
      ∑ j ∈ Finset.range N, ‖circleCellData N j (fun _ ↦ (1 : ℂ)) ξ‖ ^ 2 ≤ 1 := by
    rw [sum_circleCellData_norm_sq hN]
    norm_num
  have h := sum_circleSpectralExtension_cutoff_energy_le μ hr ha (Finset.range N)
    (fun j ↦ circleCellData N j (fun _ ↦ 1)) (fun j _ ↦ hm j) k hk hB
  simp_rw [circleCellData_indicator_mul] at h
  simpa only [circleCellPhysicalSchwartz, circlePhysicalSchwartz_apply,
    ENNReal.ofReal_one, mul_one] using h

end FalconerPacking
