/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.BallOverlap

/-!
# Measures formed from selected tube weights

A selected test at one child controls all enlarged children meeting a common rectangle.
The overlap loss is counted once, before the normalized averaging measures are inserted.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Classical

namespace FalconerPacking

/-- A finite sum of weights times normalized child averages. -/
def selectedAveragingMeasure {α ι : Type*} [MeasurableSpace α]
    (I : Finset ι) (w : ι → ℝ≥0∞) (μ : ι → Measure α) : Measure α :=
  ∑ i ∈ I, w i • μ i

/-- Only children whose supports meet the tested set can contribute to its mass. -/
theorem selectedAveragingMeasure_le_intersecting_weights {α ι : Type*}
    [MeasurableSpace α] (I : Finset ι) (w : ι → ℝ≥0∞) (μ : ι → Measure α)
    (S : ι → Set α) (U : Set α)
    (hmass : ∀ i ∈ I, μ i univ ≤ 1) (hsupport : ∀ i ∈ I, μ i (S i)ᶜ = 0) :
    selectedAveragingMeasure I w μ U ≤
      ∑ i ∈ I with (S i ∩ U).Nonempty, w i := by
  classical
  rw [selectedAveragingMeasure, Measure.finsetSum_apply, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i hi
  rw [Measure.smul_apply, smul_eq_mul]
  split_ifs with hmeet
  · exact (mul_le_mul_right ((measure_mono (subset_univ U)).trans (hmass i hi)) _).trans_eq
      (mul_one _)
  · have hzero : μ i U = 0 := by
      apply measure_mono_null _ (hsupport i hi)
      intro x hx hxs
      exact hmeet ⟨x, hxs, hx⟩
    simp [hzero]

/-- One selected tube test, geometric containment, and bounded cube overlap imply the
dual-rectangle mass bound. No tests at unselected children are required. -/
theorem selectedAveragingMeasure_le_of_tube_tests {α ι : Type*}
    [MeasurableSpace α] (σ : Measure α) (I : Finset ι)
    (E S T : ι → Set α) (μ : ι → Measure α) (P U : Set α)
    (Λ : ℕ) (A : ℝ≥0∞)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) (hP : MeasurableSet P)
    (hT : ∀ i ∈ I, MeasurableSet (T i))
    (hsub : ∀ i ∈ I, E i ⊆ P)
    (hover : ∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ)
    (hmass : ∀ i ∈ I, μ i univ ≤ 1) (hsupport : ∀ i ∈ I, μ i (S i)ᶜ = 0)
    (htest : ∀ i ∈ I, σ (T i ∩ P) ≤ A)
    (hcontain : ∀ i ∈ I, (S i ∩ U).Nonempty →
      ∀ j ∈ I, (S j ∩ U).Nonempty → E j ⊆ T i) :
    selectedAveragingMeasure I (fun i ↦ σ (E i)) μ U ≤ Λ * A := by
  classical
  let J := I.filter fun i ↦ (S i ∩ U).Nonempty
  have hfirst := selectedAveragingMeasure_le_intersecting_weights I
    (fun i ↦ σ (E i)) μ S U hmass hsupport
  change selectedAveragingMeasure I (fun i ↦ σ (E i)) μ U ≤
    ∑ i ∈ J, σ (E i) at hfirst
  by_cases hJ : J.Nonempty
  · obtain ⟨i, hi⟩ := hJ
    obtain ⟨hiI, hiU⟩ := Finset.mem_filter.mp hi
    apply hfirst.trans
    apply (sum_measure_le_mul_of_multiplicity σ J E ((hT i hiI).inter hP)
      (fun j hj ↦ hE j (Finset.mem_filter.mp hj).1) ?_ Λ ?_).trans
        (mul_le_mul_right (htest i hiI) _)
    · intro j hj x hx
      obtain ⟨hjI, hjU⟩ := Finset.mem_filter.mp hj
      exact ⟨hcontain i hiI hiU j hjI hjU hx, hsub j hjI hx⟩
    · intro x
      exact (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.filter_subset _ _))).trans (hover x)
  · have hz : selectedAveragingMeasure I (fun i ↦ σ (E i)) μ U = 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty.mp hJ] using hfirst
    simp [hz]

/-- The total averaging mass loses only the overlap multiplicity. -/
theorem selectedAveragingMeasure_univ_le {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) (I : Finset ι) (E : ι → Set α) (μ : ι → Measure α)
    (P : Set α) (Λ : ℕ)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) (hP : MeasurableSet P)
    (hsub : ∀ i ∈ I, E i ⊆ P)
    (hover : ∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ)
    (hmass : ∀ i ∈ I, μ i univ ≤ 1) :
    selectedAveragingMeasure I (fun i ↦ σ (E i)) μ univ ≤ Λ * σ P := by
  rw [selectedAveragingMeasure, Measure.finsetSum_apply]
  apply (Finset.sum_le_sum (fun i hi ↦ ?_)).trans
    (sum_measure_le_mul_of_multiplicity σ I E hP hE hsub Λ hover)
  simpa only [Measure.smul_apply, smul_eq_mul, mul_one] using
    mul_le_mul_right (hmass i hi) (σ (E i))

/-- The selected-test estimate applies to the actual normalized restrictions of any
reference measure, in particular normalized planar volume on enlarged squares. -/
theorem selectedNormalizedAverages_le_of_tube_tests {α ι : Type*}
    [MeasurableSpace α] (σ ρ : Measure α) (I : Finset ι)
    (E S T : ι → Set α) (P U : Set α) (Λ : ℕ) (A : ℝ≥0∞)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) (hS : ∀ i ∈ I, MeasurableSet (S i))
    (hP : MeasurableSet P) (hT : ∀ i ∈ I, MeasurableSet (T i))
    (hsub : ∀ i ∈ I, E i ⊆ P)
    (hover : ∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ)
    (htest : ∀ i ∈ I, σ (T i ∩ P) ≤ A)
    (hcontain : ∀ i ∈ I, (S i ∩ U).Nonempty →
      ∀ j ∈ I, (S j ∩ U).Nonempty → E j ⊆ T i) :
    selectedAveragingMeasure I (fun i ↦ σ (E i))
      (fun i ↦ (ρ (S i))⁻¹ • ρ.restrict (S i)) U ≤ Λ * A := by
  apply selectedAveragingMeasure_le_of_tube_tests σ I E S T _ P U Λ A
    hE hP hT hsub hover ?_ ?_ htest hcontain
  · intro i hi
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using
      ENNReal.inv_mul_le_one (ρ (S i))
  · intro i hi
    simp [Measure.restrict_apply, (hS i hi).compl]

end FalconerPacking
