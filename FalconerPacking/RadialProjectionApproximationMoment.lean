/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionSmoothMoment
public import FalconerPacking.SmoothProbabilityApproximation

/-!
# Uniform moments for the actual shrinking source sequence

Bounded Frostman source and pin probabilities produce one exponent above one and one common
moment bound for the explicitly normalized smooth approximations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter
open scoped ENNReal Convolution

namespace FalconerPacking

/-- The support of a smoothed source is contained pointwise in the sum of the source and bump balls. -/
theorem norm_le_of_smoothMeasureDensity_ne_zero
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) {M : ℝ}
    (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : smoothMeasureDensity μ (φ.normed volume) x ≠ 0) :
    ‖x‖ ≤ M + φ.rOut := by
  by_contra h
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  apply notMem_support.mp
  rw [φ.support_normed_eq]
  intro hxy
  have hr : ‖x - y‖ < φ.rOut := by simpa only [Metric.mem_ball, dist_zero_right] using hxy
  have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - y) y
  linarith

/-- The actual nonnegative radial density of the `n`th source approximation. -/
def shrinkingRadialDensity (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) : ℝ≥0∞ :=
  radialRayDensity (fun y ↦ ENNReal.ofReal
    (smoothMeasureDensity μ ((shrinkingSourceBump n).normed volume) y)) x θ

/-- The selected representative is jointly measurable in pin and angle at every scale. -/
theorem measurable_shrinkingRadialDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (n : ℕ) :
    Measurable (Function.uncurry (shrinkingRadialDensity μ n)) := by
  unfold Function.uncurry shrinkingRadialDensity
  apply measurable_radialRayDensity
  exact (contDiff_smoothMeasureDensity μ (shrinkingSourceBump n).contDiff_normed
    (shrinkingSourceBump n).hasCompactSupport_normed).continuous.measurable.ennreal_ofReal

/-- All smoothed source probabilities obey the same radial moment bound, under the original
Frostman and bounded-support assumptions. The smaller exponent is reserved for the weak limit. -/
theorem exists_uniform_shrinking_radial_moment
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {α β Cμ Cν Mμ Mν : ℝ} (hα : 1 < α) (hβ : 1 < β)
    (hCμ : 0 < Cμ) (hCν : 0 < Cν)
    (hμ : IsFrostman μ α Cμ) (hν : IsFrostman ν β Cν)
    (hμsupp : ∀ᵐ x ∂μ, ‖x‖ ≤ Mμ) (hνsupp : ∀ᵐ x ∂ν, ‖x‖ ≤ Mν) :
    ∃ b c : ℝ, ∃ K : ℝ≥0∞, 1 < c ∧ c < b ∧ K < ∞ ∧ ∀ n : ℕ,
      (∫⁻ x, ∫⁻ θ, shrinkingRadialDensity μ n x θ ^ b ∂radialAngularMeasure ∂ν) ≤ K := by
  obtain ⟨s, hs, hs'⟩ := exists_between (lt_min hα (by norm_num : (1 : ℝ) < 2))
  have hsα := hs'.trans_le (min_le_left α 2)
  have hs₂ := hs'.trans_le (min_le_right α 2)
  let p := 1 + (s - 1) / 8
  obtain ⟨hp, _, hpa₀, hpa₁, _⟩ := radialProjection_exact_exponents hs hs₂
  change 1 < p at hp
  change 0 < p * (2 - s) at hpa₀
  change p * (2 - s) < 1 at hpa₁
  have hsource : rieszEnergy μ s < ∞ :=
    lt_top_iff_ne_top.mpr (rieszEnergy_ne_top hCμ (by linarith) hsα hμ)
  have hpin : rieszEnergy ν (p * (2 - s)) < ∞ :=
    lt_top_iff_ne_top.mpr (rieszEnergy_ne_top hCν hpa₀ (hpa₁.trans hβ) hν)
  obtain ⟨b, c, hc, hcb, hbp⟩ := radial_trace_strong_exponents hp
  have hb : 0 ≤ b := by linarith
  obtain ⟨K, hK, hbound⟩ := exists_uniform_smooth_radial_moment_bound ν
    (Real.HolderConjugate.conjExponent hp) (by linarith : 0 < 2 - s)
    (by linarith : 2 - s < 1) hpa₁ hb hbp hsource hpin (Mν + Mμ + 1)
  refine ⟨b, c, K, hc, hcb, hK, ?_⟩
  intro n
  let φ := shrinkingSourceBump n
  have hφ : φ.rOut ≤ 1 := by
    dsimp [φ, shrinkingSourceBump]
    exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (by
      linarith [Nat.cast_nonneg (α := ℝ) n])
  have hfinite := isProbabilityMeasure_smoothMeasureDensity μ φ
  letI := hfinite
  apply hbound (smoothMeasureDensity μ (φ.normed volume))
    (contDiff_smoothMeasureDensity μ φ.contDiff_normed φ.hasCompactSupport_normed)
    (hasCompactSupport_smoothMeasureDensity μ φ.hasCompactSupport_normed hμsupp)
    (smoothMeasureDensity_nonneg μ φ.nonneg_normed) inferInstance
  · rw [withDensity_smoothMeasureDensity_eq_conv μ φ.contDiff_normed
      φ.hasCompactSupport_normed φ.nonneg_normed, show 2 - (2 - s) = s by ring]
    exact rieszEnergy_conv_le μ (smoothBumpMeasure φ) (by linarith) hs₂
  · filter_upwards [hνsupp] with x hx
    intro y hy
    have hy' : smoothMeasureDensity μ (φ.normed volume) y ≠ 0 := by
      intro hzero
      exact hy (by rw [hzero, ENNReal.ofReal_zero])
    have hnorm := norm_le_of_smoothMeasureDensity_ne_zero μ φ hμsupp hy'
    exact (dist_le_norm_add_norm x y).trans (by linarith)

end FalconerPacking
