/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.TruncatedConditionalEnergy
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Finite tube pair counting and heavy-tube deletion

The exact square-mass identity retains the diagonal and therefore applies to measures with
atoms. The weighted deletion estimate uses actual measurable product sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The number of members of a finite set family that contain both points. -/
def tubePairCount {α ι : Type*} (I : Finset ι) (T : ι → Set α) (x y : α) : ℕ := by
  classical
  exact (I.filter (fun i ↦ x ∈ T i ∧ y ∈ T i)).card

theorem tubePairCount_eq_sum_indicator {α ι : Type*}
    (I : Finset ι) (T : ι → Set α) (x y : α) :
    (tubePairCount I T x y : ℝ≥0∞) =
      ∑ i ∈ I, (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x *
        (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y := by
  classical
  rw [tubePairCount, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ T i <;> by_cases hy : y ∈ T i <;> simp [hx, hy]

/-- Square masses count pairs exactly, with no nonatomicity assumption. -/
theorem sum_measure_sq_eq_lintegral_tubePairCount {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (I : Finset ι) (T : ι → Set α)
    (hT : ∀ i ∈ I, MeasurableSet (T i)) :
    (∑ i ∈ I, μ (T i) ^ 2) =
      ∫⁻ x, ∫⁻ y, (tubePairCount I T x y : ℝ≥0∞) ∂μ ∂μ := by
  have hm (i : ι) (hi : i ∈ I) :
      Measurable ((T i).indicator (fun _ ↦ (1 : ℝ≥0∞))) :=
    measurable_const.indicator (hT i hi)
  simp_rw [tubePairCount_eq_sum_indicator]
  have hinner (x : α) :
      (∫⁻ y, ∑ i ∈ I, (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x *
        (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y ∂μ) =
      ∑ i ∈ I, (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x * μ (T i) := by
    rw [lintegral_finsetSum I (f := fun i y ↦
      (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x *
        (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) y)
      (fun i hi ↦ measurable_const.mul (hm i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_const_mul _ (hm i hi), lintegral_indicator (hT i hi),
      setLIntegral_const, one_mul]
  simp_rw [hinner]
  rw [lintegral_finsetSum I (f := fun i x ↦
    (T i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x * μ (T i))
    (fun i hi ↦ (hm i hi).mul_const _)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_mul_const _ (hm i hi), lintegral_indicator (hT i hi),
    setLIntegral_const, one_mul, pow_two]

/-- Threshold times total heavy-tube mass is bounded by the full square-mass sum. -/
theorem threshold_mul_sum_heavy_tube_mass_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (I : Finset ι) (T : ι → Set α) (a : ℝ≥0∞) :
    a * (∑ i ∈ I.filter (fun i ↦ a < μ (T i)), μ (T i)) ≤
      ∑ i ∈ I, μ (T i) ^ 2 := by
  classical
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ I.filter (fun i ↦ a < μ (T i)), μ (T i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [pow_two] using mul_le_mul_left (Finset.mem_filter.mp hi).2.le (μ (T i))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ bot_le)

/-- Product sets associated with heavy tubes obey the square-mass deletion bound. -/
theorem prod_union_heavy_tubes_le {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (I : Finset ι) (T : ι → Set α) (S : ι → Set β)
    {a c : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hS : ∀ i ∈ I, ν (S i) ≤ c) :
    (μ.prod ν) (⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) ≤
      (c / a) * ∑ i ∈ I, μ (T i) ^ 2 := by
  classical
  refine (measure_biUnion_finset_le _ _).trans ?_
  simp_rw [Measure.prod_prod]
  calc
    _ ≤ ∑ i ∈ I.filter (fun i ↦ a < μ (T i)), μ (T i) * c :=
      Finset.sum_le_sum fun i hi ↦ mul_le_mul_right (hS i (Finset.mem_filter.mp hi).1) _
    _ = (c / a) * (a * ∑ i ∈ I.filter (fun i ↦ a < μ (T i)), μ (T i)) := by
      rw [← Finset.sum_mul, ← mul_assoc, ENNReal.div_mul_cancel ha hat, mul_comm]
    _ ≤ _ := mul_le_mul_right (threshold_mul_sum_heavy_tube_mass_le μ I T a) _

end FalconerPacking
