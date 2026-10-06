/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AngularTruncation

/-!
# Finite angular heavy-cell deletion

Heavy cells are defined by their actual density averages. A high/low decomposition controls
their mass without a maximal-function theorem and without paying the number of cells.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The actual average of a nonnegative density on a measurable cell. -/
def angularCellAverage {α : Type*} [MeasurableSpace α]
    (σ : Measure α) (f : α → ℝ≥0∞) (C : Set α) : ℝ≥0∞ :=
  (∫⁻ x in C, f x ∂σ) / σ C

theorem lt_angularCellAverage_iff {α : Type*} [MeasurableSpace α]
    (σ : Measure α) (f : α → ℝ≥0∞) (C : Set α) (A : ℝ≥0∞)
    (hC : σ C ≠ 0) (hCt : σ C ≠ ∞) :
    A < angularCellAverage σ f C ↔ A * σ C < ∫⁻ x in C, f x ∂σ :=
  ENNReal.lt_div_iff_mul_lt (Or.inl hC) (Or.inl hCt)

/-- The union of cells whose density mass exceeds threshold times reference mass. -/
def angularHeavyCells {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) (f : α → ℝ≥0∞) (I : Finset ι) (C : ι → Set α)
    (A : ℝ≥0∞) : Set α := by
  classical
  exact ⋃ i ∈ I.filter (fun i ↦ A * σ (C i) < ∫⁻ x in C i, f x ∂σ), C i

theorem mem_angularHeavyCells {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) (f : α → ℝ≥0∞) (I : Finset ι) (C : ι → Set α)
    (A : ℝ≥0∞) (x : α) :
    x ∈ angularHeavyCells σ f I C A ↔
      ∃ i ∈ I, x ∈ C i ∧ A * σ (C i) < ∫⁻ z in C i, f z ∂σ := by
  classical
  simp only [angularHeavyCells, mem_iUnion, Finset.mem_filter]
  aesop

theorem measurableSet_angularHeavyCells {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) (f : α → ℝ≥0∞) (I : Finset ι) (C : ι → Set α)
    (A : ℝ≥0∞) (hC : ∀ i ∈ I, MeasurableSet (C i)) :
    MeasurableSet (angularHeavyCells σ f I C A) := by
  classical
  exact Finset.measurableSet_biUnion _ fun i hi ↦ hC i (Finset.mem_filter.mp hi).1

/-- On a heavy cell at threshold `2*A`, at least half its density mass lies above `A`. -/
theorem heavy_cell_mass_le_twice_tail {α : Type*} [MeasurableSpace α]
    (σ : Measure α) {f : α → ℝ≥0∞} {C : Set α} {A : ℝ≥0∞}
    (hfinite : (∫⁻ x in C, f x ∂σ) ≠ ∞)
    (hheavy : 2 * A * σ C ≤ ∫⁻ x in C, f x ∂σ) :
    (∫⁻ x in C, f x ∂σ) ≤
      2 * ∫⁻ x in C, {z | A < f z}.indicator f x ∂σ := by
  have hsplit : (∫⁻ x in C, f x ∂σ) ≤
      A * σ C + ∫⁻ x in C, {z | A < f z}.indicator f x ∂σ := by
    calc
      _ ≤ ∫⁻ x in C, A + {z | A < f z}.indicator f x ∂σ := by
        apply lintegral_mono
        intro x
        by_cases hx : A < f x
        · simp only [Set.indicator, mem_setOf_eq, if_pos hx]
          exact le_add_left le_rfl
        · simp only [Set.indicator, mem_setOf_eq, if_neg hx, add_zero]
          exact le_of_not_gt hx
      _ = _ := by rw [lintegral_add_left measurable_const, setLIntegral_const]
  apply ENNReal.le_of_add_le_add_left hfinite
  calc
    _ ≤ (A * σ C + ∫⁻ x in C, {z | A < f z}.indicator f x ∂σ) +
        (A * σ C + ∫⁻ x in C, {z | A < f z}.indicator f x ∂σ) := add_le_add hsplit hsplit
    _ = 2 * A * σ C + 2 * ∫⁻ x in C, {z | A < f z}.indicator f x ∂σ := by ring
    _ ≤ _ := add_le_add_left hheavy _

/-- A finite disjoint family loses at most twice the high-density tail, regardless of its size. -/
theorem withDensity_angularHeavyCells_le {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hfinite : (∫⁻ x, f x ∂σ) ≠ ∞) (I : Finset ι) (C : ι → Set α)
    (hd : (↑I : Set ι).PairwiseDisjoint C) (hC : ∀ i ∈ I, MeasurableSet (C i))
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    σ.withDensity f (angularHeavyCells σ f I C (2 * A)) ≤
      2 * A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ := by
  classical
  let J := I.filter (fun i ↦ 2 * A * σ (C i) < ∫⁻ x in C i, f x ∂σ)
  have hJI : J ⊆ I := Finset.filter_subset _ _
  have hJd : (↑J : Set ι).PairwiseDisjoint C :=
    fun i hi j hj hij ↦ hd (hJI hi) (hJI hj) hij
  have hJm : ∀ i ∈ J, MeasurableSet (C i) := fun i hi ↦ hC i (hJI hi)
  have hs : MeasurableSet {x | A < f x} := measurableSet_lt measurable_const hf
  rw [withDensity_apply _ (measurableSet_angularHeavyCells σ f I C (2 * A) hC)]
  change (∫⁻ x in ⋃ i ∈ J, C i, f x ∂σ) ≤ _
  calc
    _ = ∑ i ∈ J, ∫⁻ x in C i, f x ∂σ := lintegral_biUnion_finset hJd hJm f
    _ ≤ ∑ i ∈ J, 2 * ∫⁻ x in C i, {z | A < f z}.indicator f x ∂σ := by
      apply Finset.sum_le_sum
      intro i hi
      exact heavy_cell_mass_le_twice_tail σ
        (ne_top_of_le_ne_top hfinite (setLIntegral_le_lintegral _ _))
        (Finset.mem_filter.mp hi).2.le
    _ = 2 * ∫⁻ x in ⋃ i ∈ J, C i, {z | A < f z}.indicator f x ∂σ := by
      rw [lintegral_biUnion_finset hJd hJm, Finset.mul_sum]
    _ ≤ 2 * ∫⁻ x, {z | A < f z}.indicator f x ∂σ :=
      mul_le_mul_right (setLIntegral_le_lintegral _ _) 2
    _ = 2 * σ.withDensity f {x | A < f x} := by
      rw [lintegral_indicator hs, withDensity_apply _ hs]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_right (withDensity_tail_le σ hf hA hAt hq) 2

/-- Every cell containing a retained point has the asserted actual mass bound. -/
theorem cell_mass_le_of_not_mem_angularHeavyCells {α ι : Type*} [MeasurableSpace α]
    (σ : Measure α) (f : α → ℝ≥0∞) (I : Finset ι) (C : ι → Set α)
    (A : ℝ≥0∞) {x : α} (hx : x ∉ angularHeavyCells σ f I C A)
    {i : ι} (hi : i ∈ I) (hxi : x ∈ C i) :
    (∫⁻ z in C i, f z ∂σ) ≤ A * σ (C i) := by
  by_contra h
  exact hx ((mem_angularHeavyCells σ f I C A x).mpr ⟨i, hi, hxi, lt_of_not_ge h⟩)

/-- The heavy-cell union is measurable jointly in the parameter and angular variable. -/
theorem measurableSet_angularHeavyCellPairs {α β ι : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (σ : Measure β) [SFinite σ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (I : Finset ι) (C : ι → Set β)
    (A : ℝ≥0∞) (hC : ∀ i ∈ I, MeasurableSet (C i)) :
    MeasurableSet {p : α × β | p.2 ∈ angularHeavyCells σ (f p.1) I C A} := by
  have hm (i : ι) : Measurable (fun x ↦ ∫⁻ z in C i, f x z ∂σ) :=
    hf.lintegral_prod_right
  have hset : {p : α × β | p.2 ∈ angularHeavyCells σ (f p.1) I C A} =
      ⋃ i ∈ I, {p : α × β | p.2 ∈ C i ∧
        A * σ (C i) < ∫⁻ z in C i, f p.1 z ∂σ} := by
    ext p
    simp only [mem_setOf_eq, mem_angularHeavyCells, mem_iUnion]
    aesop
  rw [hset]
  exact Finset.measurableSet_biUnion I fun i hi ↦
    (measurable_snd (hC i hi)).inter
      (measurableSet_lt measurable_const ((hm i).comp measurable_fst))

/-- Several finite angular scales cost only their number, not the number of cells. -/
theorem withDensity_biUnion_angularHeavyCells_le {α ι κ : Type*} [MeasurableSpace α]
    (σ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f)
    (hfinite : (∫⁻ x, f x ∂σ) ≠ ∞) (S : Finset κ)
    (I : κ → Finset ι) (C : κ → ι → Set α)
    (hd : ∀ j ∈ S, (↑(I j) : Set ι).PairwiseDisjoint (C j))
    (hC : ∀ j ∈ S, ∀ i ∈ I j, MeasurableSet (C j i))
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    σ.withDensity f (⋃ j ∈ S, angularHeavyCells σ f (I j) (C j) (2 * A)) ≤
      S.card * (2 * A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ) := by
  refine (measure_biUnion_finset_le S _).trans ?_
  calc
    _ ≤ ∑ j ∈ S, 2 * A ^ (1 - q) * ∫⁻ x, f x ^ q ∂σ :=
      Finset.sum_le_sum fun j hj ↦
        withDensity_angularHeavyCells_le σ hf hfinite (I j) (C j) (hd j hj)
          (hC j hj) hA hAt hq
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

end FalconerPacking
