/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.WeakMomentLimit
public import Mathlib.MeasureTheory.Integral.Regular
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Domination under weak convergence

Domination of finite measures passes to simultaneous weak limits. The proof uses
nonnegative bounded continuous tests and regular approximation of open sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace FalconerPacking

/-- Domination of finite measures is preserved by simultaneous weak convergence. -/
theorem measure_le_of_tendsto_finiteMeasure
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    [ProperSpace α] {l : Filter ι} [l.NeBot]
    {μ ν : ι → FiniteMeasure α} {μ₀ ν₀ : FiniteMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) (hν : Tendsto ν l (𝓝 ν₀))
    (hdom : ∀ᶠ i in l, (μ i : Measure α) ≤ (ν i : Measure α)) :
    (μ₀ : Measure α) ≤ (ν₀ : Measure α) := by
  have htest (f : α →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
      ∫ x, f x ∂(μ₀ : Measure α) ≤ ∫ x, f x ∂(ν₀ : Measure α) := by
    apply le_of_tendsto_of_tendsto
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f)
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f)
    filter_upwards [hdom] with i hi
    exact integral_mono_measure hi (Eventually.of_forall hf)
      (f.integrable (μ := (ν i : Measure α)))
  have hopen (U : Set α) (hU : IsOpen U) :
      (μ₀ : Measure α) U ≤ (ν₀ : Measure α) U := by
    rw [hU.measure_eq_biSup_integral_continuous (μ₀ : Measure α)]
    refine iSup_le fun f ↦ iSup_le fun hf ↦ iSup_le fun hzero ↦
      iSup_le fun hnonneg ↦ iSup_le fun hle ↦ ?_
    let F : α →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ 1 (by
      intro x y
      rw [Real.dist_eq, abs_le]
      change -1 ≤ f x - f y ∧ f x - f y ≤ 1
      have hx : 0 ≤ f x ∧ f x ≤ 1 := ⟨hnonneg x, hle x⟩
      have hy : 0 ≤ f y ∧ f y ≤ 1 := ⟨hnonneg y, hle y⟩
      constructor <;> linarith)
    exact (ENNReal.ofReal_le_ofReal (htest F hnonneg)).trans
      (integral_le_measure (fun x _ ↦ hle x) (fun x hx ↦ (hzero hx).le))
  apply Measure.le_iff.mpr
  intro S _
  rw [S.measure_eq_iInf_isOpen (ν₀ : Measure α)]
  exact le_iInf fun U ↦ le_iInf fun hSU ↦ le_iInf fun hU ↦
    (measure_mono hSU).trans (hopen U hU)

/-- A fixed finite scalar in a domination inequality is preserved by weak limits. -/
theorem measure_le_smul_of_tendsto_finiteMeasure
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    [ProperSpace α] {l : Filter ι} [l.NeBot]
    {μ ν : ι → FiniteMeasure α} {μ₀ ν₀ : FiniteMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) (hν : Tendsto ν l (𝓝 ν₀)) (c : ℝ≥0)
    (hdom : ∀ᶠ i in l, (μ i : Measure α) ≤ c • (ν i : Measure α)) :
    (μ₀ : Measure α) ≤ c • (ν₀ : Measure α) := by
  have hν' : Tendsto (fun i ↦ c • ν i) l (𝓝 (c • ν₀)) :=
    tendsto_const_nhds.smul hν
  simpa only [FiniteMeasure.toMeasure_smul] using
    measure_le_of_tendsto_finiteMeasure hμ hν'
      (by simpa only [FiniteMeasure.toMeasure_smul] using hdom)

/-- Probability measures inherit the finite-measure domination result. -/
theorem measure_le_smul_of_tendsto_probabilityMeasure
    {α ι : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    [ProperSpace α] {l : Filter ι} [l.NeBot]
    {μ ν : ι → ProbabilityMeasure α} {μ₀ ν₀ : ProbabilityMeasure α}
    (hμ : Tendsto μ l (𝓝 μ₀)) (hν : Tendsto ν l (𝓝 ν₀)) (c : ℝ≥0)
    (hdom : ∀ᶠ i in l, (μ i : Measure α) ≤ c • (ν i : Measure α)) :
    (μ₀ : Measure α) ≤ c • (ν₀ : Measure α) := by
  exact measure_le_smul_of_tendsto_finiteMeasure
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).mp hμ)
    ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).mp hν) c hdom

/-- Compact support, uniform higher density moments, and moving domination produce
an absolutely continuous dominated probability limit along a subsequence. -/
theorem exists_dominated_absolutelyContinuous_subseq
    {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    [ProperSpace α] {K : Set α} (hK : IsCompact K)
    (μ : ℕ → ProbabilityMeasure α) (hsupp : ∀ n, (μ n : Measure α) Kᶜ = 0)
    {ν : ℕ → FiniteMeasure α} {ν₀ : FiniteMeasure α}
    (hν : Tendsto ν atTop (𝓝 ν₀)) (c : ℝ≥0)
    (hdom : ∀ n, (μ n : Measure α) ≤ c • (ν n : Measure α))
    (ξ : Measure α) [ξ.OuterRegular] (f : ℕ → α → ℝ≥0∞)
    (hf : ∀ n, Measurable (f n))
    (hdensity : ∀ n, (μ n : Measure α) = ξ.withDensity (f n))
    {p : ℝ} (hp : 1 < p) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hmoment : ∀ n, ∫⁻ x, f n x ^ p ∂ξ ≤ M) :
    ∃ (μ₀ : ProbabilityMeasure α) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 μ₀) ∧
      (μ₀ : Measure α) Kᶜ = 0 ∧ (μ₀ : Measure α) ≪ ξ ∧
      (μ₀ : Measure α) ≤ c • (ν₀ : Measure α) := by
  have hcompact := isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
    (E := α) (u := fun _ ↦ 0) (K := fun _ ↦ K)
    tendsto_const_nhds (fun _ ↦ hK) (Or.inl inferInstance)
  have hmem : ∀ n, μ n ∈ {ρ : ProbabilityMeasure α | ∀ j : ℕ, ρ Kᶜ ≤ 0} := by
    intro n j
    rw [← ENNReal.coe_le_coe]
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ENNReal.coe_zero, hsupp n] using (le_refl (0 : ℝ≥0∞))
  obtain ⟨μ₀, hμ₀, φ, hφ, hlim⟩ := hcompact.isSeqCompact hmem
  refine ⟨μ₀, φ, hφ, hlim, ?_, ?_, ?_⟩
  · have hzero := le_antisymm (hμ₀ 0) zero_le
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ENNReal.coe_zero] using congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hzero
  · exact absolutelyContinuous_of_tendsto_uniform_moment_densities hlim
      (fun n ↦ f (φ n)) (fun n ↦ hf (φ n)) (fun n ↦ hdensity (φ n)) hp hM
      (fun n ↦ hmoment (φ n))
  · exact measure_le_smul_of_tendsto_finiteMeasure
      ((ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).mp hlim)
      (hν.comp hφ.tendsto_atTop) c (Eventually.of_forall fun n ↦ hdom (φ n))

end FalconerPacking
