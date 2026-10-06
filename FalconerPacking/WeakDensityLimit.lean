/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.GeometricCapacity
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Absolute continuity of weak limits with uniform density bounds

An open-set estimate `μ U ≤ K * ν U ^ θ`, with finite `K` and positive `θ`, implies
absolute continuity when `ν` is outer regular. The estimate is closed under weak convergence
of probability measures by Portmanteau. Hölder's inequality supplies it for measures with
uniformly bounded `L²` densities. No convergence of the densities is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FalconerPacking

/-- A positive-power open-set mass bound forces absolute continuity by outer regularity. -/
theorem absolutelyContinuous_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [ν.OuterRegular] {K : ℝ≥0∞} (hK : K ≠ ∞)
    {θ : ℝ} (hθ : 0 < θ)
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) : μ ≪ ν := by
  intro A hA
  apply le_antisymm _ zero_le
  haveI := ENNReal.nhdsGT_zero_neBot
  have hlim : Tendsto (fun ε : ℝ≥0∞ ↦ K * ε ^ θ) (𝓝[>] 0) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK hθ).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨U, hAU, hU, hUε⟩ := A.exists_isOpen_lt_of_lt (μ := ν) ε
    (by simpa only [hA, mem_Ioi] using hε)
  exact (measure_mono hAU).trans ((hbound U hU).trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hUε.le hθ.le)))

/-- Every fixed open-set upper bound survives weak convergence of probability measures. -/
theorem probabilityMeasure_open_power_bound_of_tendsto
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {l : Filter ι} [l.NeBot] {μ : ι → ProbabilityMeasure α} {μ₀ : ProbabilityMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) (ν : Measure α) (K : ℝ≥0∞) (θ : ℝ)
    (hbound : ∀ U : Set α, IsOpen U → ∀ᶠ i in l, (μ i : Measure α) U ≤ K * ν U ^ θ) :
    ∀ U : Set α, IsOpen U → (μ₀ : Measure α) U ≤ K * ν U ^ θ := by
  intro U hU
  exact (isClosed_probabilityMeasure_open_mass_le hU _).mem_of_tendsto hμ (hbound U hU)

/-- Weak limits preserve absolute continuity under one uniform open-set power bound. -/
theorem absolutelyContinuous_of_tendsto_open_power_bound
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {l : Filter ι} [l.NeBot] {μ : ι → ProbabilityMeasure α} {μ₀ : ProbabilityMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) {ν : Measure α} [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ : ℝ} (hθ : 0 < θ)
    (hbound : ∀ U : Set α, IsOpen U → ∀ᶠ i in l, (μ i : Measure α) U ≤ K * ν U ^ θ) :
    (μ₀ : Measure α) ≪ ν :=
  absolutelyContinuous_of_open_power_bound hK hθ
    (probabilityMeasure_open_power_bound_of_tendsto hμ ν K θ hbound)

/-- Hölder's inequality bounds a density law on a measurable set by its `L²` norm. -/
theorem withDensity_ofReal_le_eLpNorm_two_mul_sqrt
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) {A : Set α} (hA : MeasurableSet A) :
    (ν.withDensity (fun x ↦ ENNReal.ofReal (f x))) A ≤
      eLpNorm f 2 ν * ν A ^ (1 / 2 : ℝ) := by
  rw [withDensity_apply _ hA]
  calc
    ∫⁻ x in A, ENNReal.ofReal (f x) ∂ν ≤ ∫⁻ x in A, ‖f x‖ₑ ∂ν :=
      lintegral_mono (fun x ↦ Real.ofReal_le_enorm (f x))
    _ = eLpNorm f 1 (ν.restrict A) := (eLpNorm_one_eq_lintegral_enorm hf.restrict).symm
    _ ≤ eLpNorm f 2 (ν.restrict A) * ν A ^ (1 / 2 : ℝ) := by
      have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict A)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.restrict
      norm_num at h ⊢
      exact h
    _ ≤ eLpNorm f 2 ν * ν A ^ (1 / 2 : ℝ) :=
      mul_le_mul' (eLpNorm_restrict_le f 2 ν A) le_rfl

/-- Uniformly `L²`-bounded density laws have absolutely continuous weak limits.
The density functions themselves need not converge in any topology. -/
theorem absolutelyContinuous_of_tendsto_uniform_L2_densities
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {l : Filter ι} [l.NeBot] {μ : ι → ProbabilityMeasure α} {μ₀ : ProbabilityMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) {ν : Measure α} [ν.OuterRegular]
    (f : ι → α → ℝ) (hf : ∀ i, MemLp (f i) 2 ν)
    (hdensity : ∀ i, (μ i : Measure α) = ν.withDensity (fun x ↦ ENNReal.ofReal (f i x)))
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hbound : ∀ i, eLpNorm (f i) 2 ν ≤ K) :
    (μ₀ : Measure α) ≪ ν := by
  apply absolutelyContinuous_of_tendsto_open_power_bound hμ hK (by norm_num : (0 : ℝ) < 1 / 2)
  intro U hU
  filter_upwards [] with i
  rw [hdensity i]
  exact (withDensity_ofReal_le_eLpNorm_two_mul_sqrt (hf i).aestronglyMeasurable
    hU.measurableSet).trans (mul_le_mul' (hbound i) le_rfl)

end FalconerPacking
