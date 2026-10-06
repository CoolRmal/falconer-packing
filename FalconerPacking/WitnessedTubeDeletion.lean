/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SlopeTubeEnergy
public import FalconerPacking.RadialHeavyCells

/-!
# Heavy-tube deletion from a retained witness

A source tube need not have small mass before source-heavy pairs are discarded. It is
enough that any retained pair in it certifies the mass bound for that source tube. Empty
retained pieces contribute nothing. The resulting deletion estimate keeps this distinction
explicit and uses the actual truncated pair energy of the finite slope-tube family.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Only tubes with a retained witness need a source-mass estimate. -/
theorem prod_retained_heavy_tubes_le {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (I : Finset ι) (T : ι → Set α) (S : ι → Set β) (bad : Set (α × β))
    {a c : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hS : ∀ i ∈ I, ((T i ×ˢ S i) \ bad).Nonempty → ν (S i) ≤ c) :
    (μ.prod ν) ((⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) \ bad) ≤
      (c / a) * ∑ i ∈ I, μ (T i) ^ 2 := by
  let J := I.filter (fun i ↦ ((T i ×ˢ S i) \ bad).Nonempty)
  have hsub : ((⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) \ bad) ⊆
      ⋃ i ∈ J.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i := by
    rintro p ⟨hp, hb⟩
    obtain ⟨i, hi, hp⟩ := mem_iUnion₂.mp hp
    obtain ⟨hi, hh⟩ := Finset.mem_filter.mp hi
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hi, ⟨p, hp, hb⟩⟩, hh⟩, hp⟩
  apply (measure_mono hsub).trans
  apply (prod_union_heavy_tubes_le μ ν J T S ha hat
    (fun i hi ↦ hS i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)).trans
  apply mul_le_mul_right
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ ↦ bot_le)

/-- Null sets of exceptional pins do not affect the retained-witness deletion bound. -/
theorem prod_retained_heavy_tubes_le_outside_null_pins {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (I : Finset ι) (T : ι → Set α) (S : ι → Set β) (bad : Set (α × β))
    (P : Set α) (hP : μ P = 0)
    {a c : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hS : ∀ i ∈ I, (((T i \ P) ×ˢ S i) \ bad).Nonempty → ν (S i) ≤ c) :
    (μ.prod ν) ((⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) \ bad) ≤
      (c / a) * ∑ i ∈ I, μ (T i) ^ 2 := by
  let bad' := bad ∪ (P ×ˢ univ)
  let U := ⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i
  have hw : ∀ i ∈ I, ((T i ×ˢ S i) \ bad').Nonempty → ν (S i) ≤ c := by
    intro i hi h
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hp⟩ := h
    have hn : x ∉ P := fun hxP ↦ hp (Or.inr ⟨hxP, mem_univ y⟩)
    exact hS i hi ⟨(x, y), ⟨⟨hx, hn⟩, hy⟩, fun hb ↦ hp (Or.inl hb)⟩
  have hsub : U \ bad ⊆ (U \ bad') ∪ (P ×ˢ univ) := by
    rintro ⟨x, y⟩ ⟨hp, hb⟩
    by_cases hx : x ∈ P
    · exact Or.inr ⟨hx, mem_univ y⟩
    · exact Or.inl ⟨hp, fun h ↦ h.elim hb (fun h ↦ hx h.1)⟩
  have hnull : (μ.prod ν) (P ×ˢ univ) = 0 := by rw [Measure.prod_prod, hP, zero_mul]
  exact ((measure_mono hsub).trans (measure_union_le _ _)).trans
    (by simpa only [hnull, add_zero] using
      prod_retained_heavy_tubes_le μ ν I T S bad' ha hat hw)

/-- The concrete slope-tube family turns the retained-witness estimate into truncated energy. -/
theorem prod_retained_heavy_slopeTubes_le {β : Type*} [MeasurableSpace β]
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (ν : Measure β) [SFinite ν]
    (o : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) (S : Bool × (ℤ × ℤ) → Set β)
    (bad : Set (EuclideanSpace ℝ (Fin 2) × β))
    {a c : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hS : ∀ i ∈ slopeTubeLabels M,
      ((slopeTube o b M i ×ˢ S i) \ bad).Nonempty → ν (S i) ≤ c) :
    (μ.prod ν) ((⋃ i ∈ (slopeTubeLabels M).filter
      (fun i ↦ a < μ (slopeTube o b M i)), slopeTube o b M i ×ˢ S i) \ bad) ≤
      20 * (c / a) * truncEnergy μ (b / M) b := by
  apply (prod_retained_heavy_tubes_le μ ν (slopeTubeLabels M)
    (slopeTube o b M) S bad ha hat hS).trans
  calc
    _ ≤ (c / a) * (20 * truncEnergy μ (b / M) b) :=
      mul_le_mul_right (sum_measure_slopeTube_sq_le_truncEnergy μ o hb hM) _
    _ = _ := by ring

/-- A retained radial cell bounds the entire associated source set whenever it contains
all its directions from the witness pin. -/
theorem source_mass_le_of_retained_cell_witness {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (C : ι → Set ℝ) (A : ℝ≥0∞)
    {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : ν.map (radialAngle x) ≪ radialAngularMeasure)
    (hpair : (x, y) ∉ radialHeavyCellPairs ν I C A)
    {i : ι} (hi : i ∈ I) (hC : MeasurableSet (C i))
    (hθ : radialAngle x y ∈ C i)
    (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S ⊆ radialAngle x ⁻¹' C i) :
    ν S ≤ A * radialAngularMeasure (C i) :=
  (measure_mono hS).trans (radial_cell_mass_le_of_pair_retained ν I C A hx hpair hi hC hθ)

/-- Deleting the source-heavy pairs as well adds precisely their own product mass. -/
theorem prod_all_heavy_slopeTubes_le {β : Type*} [MeasurableSpace β]
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (ν : Measure β) [SFinite ν]
    (o : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) (S : Bool × (ℤ × ℤ) → Set β)
    (bad : Set (EuclideanSpace ℝ (Fin 2) × β))
    {a c : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hS : ∀ i ∈ slopeTubeLabels M,
      ((slopeTube o b M i ×ˢ S i) \ bad).Nonempty → ν (S i) ≤ c) :
    (μ.prod ν) (bad ∪ ⋃ i ∈ (slopeTubeLabels M).filter
      (fun i ↦ a < μ (slopeTube o b M i)), slopeTube o b M i ×ˢ S i) ≤
      (μ.prod ν) bad + 20 * (c / a) * truncEnergy μ (b / M) b := by
  let U := ⋃ i ∈ (slopeTubeLabels M).filter
    (fun i ↦ a < μ (slopeTube o b M i)), slopeTube o b M i ×ˢ S i
  change (μ.prod ν) (bad ∪ U) ≤ _
  rw [← union_sdiff_self]
  exact (measure_union_le _ _).trans (add_le_add_right
    (prod_retained_heavy_slopeTubes_le μ ν o hb hM S bad ha hat hS) _)

end FalconerPacking
