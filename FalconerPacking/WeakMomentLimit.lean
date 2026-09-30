/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.WeakDensityLimit

/-!
# Absolute continuity from uniform higher moments

Hölder turns a uniform positive density moment of any order greater than one into a
positive-power set bound. The latter passes to weak limits by Portmanteau.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FalconerPacking

/-- A nonnegative density with a finite pth moment obeys the Hölder set bound. -/
theorem withDensity_le_moment_power
    {α : Type*} [MeasurableSpace α] (ν : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) {p : ℝ} (hp : 1 < p) {A : Set α} (hA : MeasurableSet A) :
    (ν.withDensity f) A ≤
      (∫⁻ x, f x ^ p ∂ν) ^ (1 / p) * ν A ^ ((p - 1) / p) := by
  have hp₀ : 0 < p := by linarith
  have hconj : p.HolderConjugate (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp, ?_⟩
    field_simp
    ring
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.restrict A) hconj
    hf.aemeasurable (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul,
    show 1 / (p / (p - 1)) = (p - 1) / p by field_simp] at h
  rw [withDensity_apply _ hA]
  exact h.trans (mul_le_mul'
    (ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
      (by positivity : 0 ≤ 1 / p)) le_rfl)

/-- The moment version of the uniform open-set bound survives weak convergence. -/
theorem absolutelyContinuous_of_tendsto_uniform_moment_densities
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {l : Filter ι} [l.NeBot] {μ : ι → ProbabilityMeasure α} {μ₀ : ProbabilityMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) {ν : Measure α} [ν.OuterRegular]
    (f : ι → α → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hdensity : ∀ i, (μ i : Measure α) = ν.withDensity (f i))
    {p : ℝ} (hp : 1 < p) {K : ℝ≥0∞} (hK : K ≠ ∞)
    (hbound : ∀ i, ∫⁻ x, f i x ^ p ∂ν ≤ K) :
    (μ₀ : Measure α) ≪ ν := by
  have hp₀ : 0 < p := by linarith
  apply absolutelyContinuous_of_tendsto_open_power_bound hμ
    (ENNReal.rpow_ne_top_of_nonneg (by positivity : 0 ≤ 1 / p) hK)
    (div_pos (by linarith : 0 < p - 1) hp₀)
  intro U hU
  exact Eventually.of_forall fun i ↦ by
    rw [hdensity i]
    exact (withDensity_le_moment_power ν (hf i) hp hU.measurableSet).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow (hbound i) (by positivity : 0 ≤ 1 / p)) le_rfl)

end FalconerPacking
