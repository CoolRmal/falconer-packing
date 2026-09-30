/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith

/-!
# Truncating two correlated angular densities

The retained measure has both angular marginals bounded by the truncation threshold.
The discarded mass is controlled by the two density moments, without an independence
assumption on the angular maps.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Above a positive finite threshold, a first power is bounded by the higher-power tail. -/
theorem le_rpow_tail {A x : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞)
    (hq : 1 ≤ q) (hAx : A ≤ x) : x ≤ A ^ (1 - q) * x ^ q := by
  have he : 0 ≤ q - 1 := by linarith
  have hp : x * A ^ (q - 1) ≤ x ^ q := by
    calc
      x * A ^ (q - 1) ≤ x * x ^ (q - 1) :=
        mul_le_mul_right (ENNReal.rpow_le_rpow hAx he) x
      _ = x ^ q := by
        rw [show q = 1 + (q - 1) by ring,
          ENNReal.rpow_add_of_nonneg 1 (q - 1) (by norm_num) he, ENNReal.rpow_one]
        congr 2
        ring
  have hz : A ^ (q - 1) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hA) hAt).ne'
  have ht : A ^ (q - 1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg he hAt
  have h := (ENNReal.le_div_iff_mul_le (Or.inl hz) (Or.inl ht)).2 hp
  rw [div_eq_mul_inv, mul_comm, ← ENNReal.rpow_neg] at h
  simpa only [neg_sub] using h

/-- The mass of a density above a threshold is bounded by its higher moment. -/
theorem withDensity_tail_le {α : Type*} [MeasurableSpace α]
    (σ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f)
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    σ.withDensity f {x | A < f x} ≤ A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ := by
  have hs : MeasurableSet {x | A < f x} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ hs]
  calc
    ∫⁻ x in {x | A < f x}, f x ∂σ ≤
        ∫⁻ x in {x | A < f x}, A ^ (1 - q) * f x ^ q ∂σ := by
      apply setLIntegral_mono' hs
      intro x hx
      exact le_rpow_tail hA hAt hq hx.le
    _ ≤ ∫⁻ x, A ^ (1 - q) * f x ^ q ∂σ := setLIntegral_le_lintegral _ _
    _ = A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ := lintegral_const_mul _ (hf.pow_const q)

/-- Restricting a density to where it is bounded gives domination by a constant measure. -/
theorem restrict_withDensity_le_smul {α : Type*} [MeasurableSpace α]
    (σ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) (A : ℝ≥0∞) :
    (σ.withDensity f).restrict {x | f x ≤ A} ≤ A • σ := by
  have hs : MeasurableSet {x | f x ≤ A} := measurableSet_le hf measurable_const
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_apply hS, withDensity_apply _ (hS.inter hs),
    Measure.smul_apply, smul_eq_mul]
  calc
    ∫⁻ x in S ∩ {x | f x ≤ A}, f x ∂σ ≤ ∫⁻ _ in S ∩ {x | f x ≤ A}, A ∂σ := by
      apply setLIntegral_mono' (hS.inter hs)
      exact fun x hx ↦ hx.2
    _ = A * σ (S ∩ {x | f x ≤ A}) := by simp
    _ ≤ A * σ S := mul_le_mul_right (measure_mono inter_subset_left) A

/-- A further restriction preserves the bound on a pushed-forward density. -/
theorem map_restrict_le_smul_of_density {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (σ : Measure β)
    {θ : α → β} (hθ : Measurable θ) {f : β → ℝ≥0∞} (hf : Measurable f)
    (hmap : μ.map θ = σ.withDensity f) (A : ℝ≥0∞) {S : Set α}
    (hS : S ⊆ {x | f (θ x) ≤ A}) : (μ.restrict S).map θ ≤ A • σ := by
  calc
    (μ.restrict S).map θ ≤ (μ.restrict (θ ⁻¹' {x | f x ≤ A})).map θ :=
      Measure.map_mono (Measure.restrict_mono_set μ hS) hθ
    _ = (μ.map θ).restrict {x | f x ≤ A} :=
      (Measure.restrict_map hθ (measurableSet_le hf measurable_const)).symm
    _ = (σ.withDensity f).restrict {x | f x ≤ A} := by rw [hmap]
    _ ≤ A • σ := restrict_withDensity_le_smul σ hf A

/-- A single pin restriction gives both bounded angular marginals and the sum of the two
moment bounds for the deleted mass. The angular maps may be arbitrarily correlated. -/
theorem correlated_density_truncation {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (σ : Measure β)
    {θ φ : α → β} (hθ : Measurable θ) (hφ : Measurable φ)
    {f g : β → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hθmap : μ.map θ = σ.withDensity f) (hφmap : μ.map φ = σ.withDensity g)
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    ∃ S : Set α, MeasurableSet S ∧
      (μ.restrict S).map θ ≤ A • σ ∧ (μ.restrict S).map φ ≤ A • σ ∧
      μ Sᶜ ≤ A ^ (1 - q) * ((∫⁻ x, f x ^ q ∂σ) + ∫⁻ x, g x ^ q ∂σ) := by
  let S := {x | f (θ x) ≤ A} ∩ {x | g (φ x) ≤ A}
  refine ⟨S, (measurableSet_le (hf.comp hθ) measurable_const).inter
    (measurableSet_le (hg.comp hφ) measurable_const),
    map_restrict_le_smul_of_density μ σ hθ hf hθmap A inter_subset_left,
    map_restrict_le_smul_of_density μ σ hφ hg hφmap A inter_subset_right, ?_⟩
  have hcomp : Sᶜ = (θ ⁻¹' {x | A < f x}) ∪ (φ ⁻¹' {x | A < g x}) := by
    ext x
    simp only [S, mem_compl_iff, mem_inter_iff, mem_setOf_eq, not_and_or,
      not_le, mem_union, mem_preimage]
  rw [hcomp, mul_add]
  calc
    μ ((θ ⁻¹' {x | A < f x}) ∪ (φ ⁻¹' {x | A < g x})) ≤
        μ (θ ⁻¹' {x | A < f x}) + μ (φ ⁻¹' {x | A < g x}) := measure_union_le _ _
    _ = σ.withDensity f {x | A < f x} + σ.withDensity g {x | A < g x} := by
      rw [← Measure.map_apply hθ (measurableSet_lt measurable_const hf), hθmap,
        ← Measure.map_apply hφ (measurableSet_lt measurable_const hg), hφmap]
    _ ≤ A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ + A ^ (1 - q) * ∫⁻ x, g x ^ q ∂σ :=
      add_le_add (withDensity_tail_le σ hf hA hAt hq)
        (withDensity_tail_le σ hg hA hAt hq)

end FalconerPacking
