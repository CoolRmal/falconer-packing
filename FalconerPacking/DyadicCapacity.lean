/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.LaminarContent
public import FalconerPacking.Content
public import FalconerPacking.Capacity
public import Mathlib.Data.Int.Interval

/-!
# Geometric dyadic capacity in the plane

A thin frame of finer dyadic squares enlarges each half-open cube to an open neighborhood.
The frame uses only linearly many fine squares, so its power-weighted cost tends to zero
for exponents greater than one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FalconerPacking

/-- The side length to the power `s`, as an extended nonnegative weight. -/
def dyadicPowerWeight (s : ℝ) (Q : DyadicCell) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-(Q.level : ℝ) * s))

/-- The actual power-weighted dyadic covering content. -/
def dyadicPowerContent (s : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) → ℝ≥0∞ :=
  dyadicCoverContent (dyadicPowerWeight s)

/-- Integer indices for a one-square-thick frame around a refined coarse square. -/
def dyadicFrameIndices (k : Fin 2 → ℤ) (m : ℕ) : Finset (ℤ × ℤ) :=
  ({2 ^ m * k 0 - 1, 2 ^ m * (k 0 + 1)} ×ˢ
      Finset.Icc (2 ^ m * k 1 - 1) (2 ^ m * (k 1 + 1))) ∪
    (Finset.Icc (2 ^ m * k 0 - 1) (2 ^ m * (k 0 + 1)) ×ˢ
      {2 ^ m * k 1 - 1, 2 ^ m * (k 1 + 1)})

/-- Addresses of the finer squares making up the frame. -/
def dyadicFrame (Q : DyadicCell) (m : ℕ) : Finset DyadicCell :=
  (dyadicFrameIndices Q.index m).image (fun z ↦ ⟨Q.level + m, ![z.1, z.2]⟩)

/-- The number of indices in one enlarged coordinate interval. -/
theorem card_dyadicFrame_interval (k : ℤ) (m : ℕ) :
    (Finset.Icc (2 ^ m * k - 1) (2 ^ m * (k + 1))).card = 2 ^ m + 2 := by
  rw [Int.card_Icc]
  have h : (2 : ℤ) ^ m * (k + 1) + 1 - (2 ^ m * k - 1) = 2 ^ m + 2 := by ring
  rw [h]
  norm_cast

/-- A refined frame has at most four times the enlarged side length many squares. -/
theorem card_dyadicFrame_le (Q : DyadicCell) (m : ℕ) :
    (dyadicFrame Q m).card ≤ 4 * (2 ^ m + 2) := by
  calc
    _ ≤ (dyadicFrameIndices Q.index m).card := Finset.card_image_le
    _ ≤ ({2 ^ m * Q.index 0 - 1, 2 ^ m * (Q.index 0 + 1)} ×ˢ
          Finset.Icc (2 ^ m * Q.index 1 - 1) (2 ^ m * (Q.index 1 + 1))).card +
        (Finset.Icc (2 ^ m * Q.index 0 - 1) (2 ^ m * (Q.index 0 + 1)) ×ˢ
          {2 ^ m * Q.index 1 - 1, 2 ^ m * (Q.index 1 + 1)}).card := Finset.card_union_le _ _
    _ ≤ 2 * (2 ^ m + 2) + (2 ^ m + 2) * 2 := by
      simp only [Finset.card_product, card_dyadicFrame_interval]
      gcongr <;> exact Finset.card_le_two
    _ = _ := by ring

/-- All frame squares lie at the selected finer generation. -/
theorem level_mem_dyadicFrame {Q R : DyadicCell} {m : ℕ} (hR : R ∈ dyadicFrame Q m) :
    R.level = Q.level + m := by
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hR
  rfl

/-- A finite dyadic family has the corresponding finite sum as its cost. -/
theorem dyadicCoverCost_finset (w : DyadicCell → ℝ≥0∞) (F : Finset DyadicCell) :
    dyadicCoverCost w (F : Set DyadicCell) = ∑ Q ∈ F, w Q := by
  classical
  exact (sum_eq_tsum_indicator w F).symm

/-- The frame cost is bounded by its linear cardinality times the fine-square weight. -/
theorem dyadicCoverCost_frame_le (s : ℝ) (Q : DyadicCell) (m : ℕ) :
    dyadicCoverCost (dyadicPowerWeight s) (dyadicFrame Q m : Set DyadicCell) ≤
      (4 * (2 ^ m + 2) : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-((Q.level + m : ℕ) : ℝ) * s)) := by
  rw [dyadicCoverCost_finset]
  calc
    _ = ∑ _R ∈ dyadicFrame Q m,
        ENNReal.ofReal ((2 : ℝ) ^ (-((Q.level + m : ℕ) : ℝ) * s)) := by
      apply Finset.sum_congr rfl
      intro R hR
      simp only [dyadicPowerWeight, level_mem_dyadicFrame hR]
    _ = (dyadicFrame Q m).card *
        ENNReal.ofReal ((2 : ℝ) ^ (-((Q.level + m : ℕ) : ℝ) * s)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_left (by exact_mod_cast card_dyadicFrame_le Q m) _

/-- An open enlargement by one fine-square side length in each coordinate. -/
def dyadicFrameNeighborhood (Q : DyadicCell) (m : ℕ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, ((2 : ℝ) ^ m * Q.index i - 1) < (2 : ℝ) ^ m * (2 ^ Q.level * x i) ∧
    (2 : ℝ) ^ m * (2 ^ Q.level * x i) < (2 : ℝ) ^ m * (Q.index i + 1) + 1}

/-- The enlargement is open in the Euclidean topology. -/
theorem isOpen_dyadicFrameNeighborhood (Q : DyadicCell) (m : ℕ) :
    IsOpen (dyadicFrameNeighborhood Q m) := by
  have heq : dyadicFrameNeighborhood Q m = ⋂ i : Fin 2,
      {x : EuclideanSpace ℝ (Fin 2) |
        ((2 : ℝ) ^ m * Q.index i - 1) < (2 : ℝ) ^ m * (2 ^ Q.level * x i)} ∩
      {x : EuclideanSpace ℝ (Fin 2) |
        (2 : ℝ) ^ m * (2 ^ Q.level * x i) < (2 : ℝ) ^ m * (Q.index i + 1) + 1} := by
    ext x
    simp [dyadicFrameNeighborhood]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_lt (by fun_prop) continuous_const)

/-- The open enlargement contains the original half-open cube. -/
theorem subset_dyadicFrameNeighborhood (Q : DyadicCell) (m : ℕ) :
    Q.carrier ⊆ dyadicFrameNeighborhood Q m := by
  intro x hx i
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hlow := mul_le_mul_of_nonneg_left (hx i).1 hp.le
  have hhigh := mul_lt_mul_of_pos_left (hx i).2 hp
  constructor <;> linarith

/-- A coordinate in the enlarged interval has a frame index if it lies outside the old interval. -/
theorem floor_mem_dyadicFrame_interval {a p : ℤ} (hp : 0 < p) {v : ℝ}
    (hlow : (p : ℝ) * a - 1 < p * v) (hhigh : (p : ℝ) * v < p * (a + 1) + 1) :
    p * a - 1 ≤ ⌊(p : ℝ) * v⌋ ∧ ⌊(p : ℝ) * v⌋ ≤ p * (a + 1) ∧
      (v < a ∨ (a : ℝ) + 1 ≤ v →
        ⌊(p : ℝ) * v⌋ = p * a - 1 ∨ ⌊(p : ℝ) * v⌋ = p * (a + 1)) := by
  have hlo : p * a - 1 ≤ ⌊(p : ℝ) * v⌋ := Int.le_floor.mpr (by exact_mod_cast hlow.le)
  have hhi : ⌊(p : ℝ) * v⌋ < p * (a + 1) + 1 := Int.floor_lt.mpr (by exact_mod_cast hhigh)
  refine ⟨hlo, by omega, ?_⟩
  intro hout
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  rcases hout with hleft | hright
  · have hlt : ⌊(p : ℝ) * v⌋ < p * a :=
      Int.floor_lt.mpr (by exact_mod_cast mul_lt_mul_of_pos_left hleft hp')
    exact Or.inl (by omega)
  · have hle : p * (a + 1) ≤ ⌊(p : ℝ) * v⌋ :=
      Int.le_floor.mpr (by exact_mod_cast mul_le_mul_of_nonneg_left hright hp'.le)
    exact Or.inr (by omega)

/-- Outside the original cube, the enlargement is covered by the finite frame. -/
theorem dyadicFrameNeighborhood_subset (Q : DyadicCell) (m : ℕ) :
    dyadicFrameNeighborhood Q m ⊆ Q.carrier ∪ dyadicCoverUnion (dyadicFrame Q m) := by
  classical
  intro x hx
  by_cases hxQ : x ∈ Q.carrier
  · exact Or.inl hxQ
  apply Or.inr
  let k := cubeIndex (Q.level + m) x
  have hcoord (i : Fin 2) := floor_mem_dyadicFrame_interval (a := Q.index i)
    (p := (2 : ℤ) ^ m) (by positivity) (v := 2 ^ Q.level * x i)
    (by exact_mod_cast (hx i).1) (by exact_mod_cast (hx i).2)
  have hk (i : Fin 2) : k i = ⌊(((2 : ℤ) ^ m : ℤ) : ℝ) * (2 ^ Q.level * x i)⌋ := by
    simp only [k, cubeIndex, Int.cast_pow, Int.cast_ofNat, pow_add]
    congr 1
    ring
  have hbounds (i : Fin 2) :
      2 ^ m * Q.index i - 1 ≤ k i ∧ k i ≤ 2 ^ m * (Q.index i + 1) := by
    rw [hk]
    exact ⟨(hcoord i).1, (hcoord i).2.1⟩
  have hout : ∃ i : Fin 2, k i = 2 ^ m * Q.index i - 1 ∨
      k i = 2 ^ m * (Q.index i + 1) := by
    change ¬ ∀ i, (Q.index i : ℝ) ≤ 2 ^ Q.level * x i ∧
      2 ^ Q.level * x i < (Q.index i : ℝ) + 1 at hxQ
    push Not at hxQ
    obtain ⟨i, hi⟩ := hxQ
    refine ⟨i, ?_⟩
    rw [hk]
    apply (hcoord i).2.2
    by_cases h : (Q.index i : ℝ) ≤ 2 ^ Q.level * x i
    · exact Or.inr (hi h)
    · exact Or.inl (lt_of_not_ge h)
  have hframe : (k 0, k 1) ∈ dyadicFrameIndices Q.index m := by
    obtain ⟨i, hi⟩ := hout
    fin_cases i
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨by simpa using hi,
          Finset.mem_Icc.mpr (hbounds 1)⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (hbounds 0),
          by simpa using hi⟩))
  have hcell : (⟨Q.level + m, k⟩ : DyadicCell) ∈ dyadicFrame Q m := by
    apply Finset.mem_image.mpr
    refine ⟨(k 0, k 1), hframe, ?_⟩
    congr 1
    funext i
    fin_cases i <;> rfl
  exact mem_iUnion₂.mpr ⟨⟨Q.level + m, k⟩, hcell, mem_dyadicCube_cubeIndex _ x⟩

/-- The linear number of frame squares leaves the geometric decay factor `2^(1-s)`. -/
theorem dyadicFrame_weight_factor (s : ℝ) (n m : ℕ) :
    (2 : ℝ) ^ m * 2 ^ (-((n + m : ℕ) : ℝ) * s) =
      2 ^ (-(n : ℝ) * s) * (2 ^ (1 - s)) ^ m := by
  rw [← Real.rpow_natCast (2 ^ (1 - s)) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast 2 m,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

/-- A convenient geometric upper bound for the frame cost. -/
theorem dyadicCoverCost_frame_le_geometric (s : ℝ) (Q : DyadicCell) (m : ℕ) :
    dyadicCoverCost (dyadicPowerWeight s) (dyadicFrame Q m : Set DyadicCell) ≤
      ENNReal.ofReal (12 * (2 : ℝ) ^ (-(Q.level : ℝ) * s) * (2 ^ (1 - s)) ^ m) := by
  have hcount : 4 * (2 ^ m + 2) ≤ 12 * (2 : ℕ) ^ m := by
    have hpos : 0 < (2 : ℕ) ^ m := by positivity
    omega
  refine (dyadicCoverCost_frame_le s Q m).trans ?_
  calc
    _ ≤ (12 * (2 ^ m : ℕ) : ℕ) *
        ENNReal.ofReal ((2 : ℝ) ^ (-((Q.level + m : ℕ) : ℝ) * s)) :=
      mul_le_mul_left (by exact_mod_cast hcount) _
    _ = _ := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      simpa only [Nat.cast_add, mul_assoc] using
        congrArg (fun t : ℝ ↦ 12 * t) (dyadicFrame_weight_factor s Q.level m)

/-- When `s > 1`, a sufficiently fine frame has arbitrarily small total cost. -/
theorem exists_dyadicFrame_cost_lt {s : ℝ} (hs : 1 < s) (Q : DyadicCell)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m, dyadicCoverCost (dyadicPowerWeight s) (dyadicFrame Q m : Set DyadicCell) < ε := by
  have hratio : (2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht := (tendsto_const_nhds (x := 12 * (2 : ℝ) ^ (-(Q.level : ℝ) * s))).mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hratio)
  have hzero : Filter.Tendsto
      (fun m : ℕ ↦ ENNReal.ofReal (12 * (2 : ℝ) ^ (-(Q.level : ℝ) * s) *
        (2 ^ (1 - s)) ^ m)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  obtain ⟨m, hm⟩ := (hzero.eventually (gt_mem_nhds hε)).exists
  exact ⟨m, (dyadicCoverCost_frame_le_geometric s Q m).trans_lt hm⟩

instance : Countable DyadicCell :=
  Function.Injective.countable (f := fun Q : DyadicCell ↦ (Q.level, Q.index)) (by
    rintro ⟨n, k⟩ ⟨m, l⟩ h
    simpa using h)

/-- Combining two cube families costs no more than their separate costs. -/
theorem dyadicCoverCost_union_le (w : DyadicCell → ℝ≥0∞) (S T : Set DyadicCell) :
    dyadicCoverCost w (S ∪ T) ≤ dyadicCoverCost w S + dyadicCoverCost w T := by
  classical
  rw [dyadicCoverCost, dyadicCoverCost, dyadicCoverCost, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro Q
  by_cases hS : Q ∈ S <;> by_cases hT : Q ∈ T <;> simp [hS, hT]

/-- A union of cube families has cost bounded by the sum of the individual costs. -/
theorem dyadicCoverCost_iUnion_le {ι : Type*} (w : DyadicCell → ℝ≥0∞)
    (S : ι → Set DyadicCell) :
    dyadicCoverCost w (⋃ i, S i) ≤ ∑' i, dyadicCoverCost w (S i) := by
  classical
  simp only [dyadicCoverCost]
  rw [ENNReal.tsum_comm]
  apply ENNReal.tsum_le_tsum
  intro Q
  by_cases hQ : Q ∈ ⋃ i, S i
  · rw [indicator_of_mem hQ]
    obtain ⟨i, hi⟩ := mem_iUnion.mp hQ
    exact (le_of_eq (indicator_of_mem hi w).symm).trans
      (ENNReal.le_tsum (f := fun i ↦ (S i).indicator w Q) i)
  · simp only [indicator_of_notMem hQ, zero_le]

/-- Every dyadic cover can be enlarged to an open cover for arbitrarily small additional cost. -/
theorem exists_open_superset_dyadicCover_cost {s : ℝ} (hs : 1 < s) (S : Set DyadicCell)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ dyadicCoverUnion S ⊆ U ∧
      dyadicPowerContent s U ≤ dyadicCoverCost (dyadicPowerWeight s) S + ε := by
  classical
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' DyadicCell
  choose m hm using fun Q ↦ exists_dyadicFrame_cost_lt hs Q (ENNReal.coe_pos.mpr (hδpos Q))
  let U := ⋃ Q ∈ S, dyadicFrameNeighborhood Q (m Q)
  let T := ⋃ Q, (dyadicFrame Q (m Q) : Set DyadicCell)
  have hUT : U ⊆ dyadicCoverUnion (S ∪ T) := by
    intro x hx
    obtain ⟨Q, hQS, hxQ⟩ := mem_iUnion₂.mp hx
    rcases dyadicFrameNeighborhood_subset Q (m Q) hxQ with hinside | hframe
    · exact mem_iUnion₂.mpr ⟨Q, Or.inl hQS, hinside⟩
    · obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp hframe
      exact mem_iUnion₂.mpr ⟨R, Or.inr (mem_iUnion.mpr ⟨Q, hR⟩), hxR⟩
  refine ⟨U, isOpen_iUnion fun Q ↦ isOpen_iUnion fun _ ↦
    isOpen_dyadicFrameNeighborhood Q (m Q), ?_, ?_⟩
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨Q, hQ, subset_dyadicFrameNeighborhood Q (m Q) hxQ⟩
  · refine (dyadicCoverContent_le_cost _ hUT).trans ?_
    refine (dyadicCoverCost_union_le _ S T).trans (add_le_add le_rfl ?_)
    exact (dyadicCoverCost_iUnion_le _ _).trans
      ((ENNReal.tsum_le_tsum (fun Q ↦ (hm Q).le)).trans hδsum.le)

/-- Exact open outer approximation of dyadic content in the planar range `s > 1`. -/
theorem exists_open_superset_dyadicPowerContent_le {s : ℝ} (hs : 1 < s)
    (E : Set (EuclideanSpace ℝ (Fin 2))) {ε : ℝ≥0} (hε : 0 < ε)
    (hfinite : dyadicPowerContent s E ≠ ∞) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ E ⊆ U ∧
      dyadicPowerContent s U ≤ dyadicPowerContent s E + ε := by
  have hhalf : (0 : ℝ≥0∞) < ((ε / 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_pos.mpr (by positivity)
  obtain ⟨S, _, hcover, hcost⟩ := exists_antichain_dyadicCoverCost_lt (dyadicPowerWeight s)
    (E := E) (ENNReal.lt_add_right hfinite hhalf.ne')
  obtain ⟨U, hU, hSU, hbound⟩ := exists_open_superset_dyadicCover_cost hs S hhalf
  refine ⟨U, hU, hcover.trans hSU, hbound.trans ?_⟩
  calc
    _ ≤ (dyadicPowerContent s E + (ε / 2 : ℝ≥0)) + (ε / 2 : ℝ≥0) :=
      add_le_add hcost.le le_rfl
    _ = _ := by rw [add_assoc, ← ENNReal.coe_add, add_halves]

/-- Decreasing compact intersections have exactly the limiting dyadic content. -/
theorem dyadicPowerContent_iInter {s : ℝ} (hs : 1 < s)
    {K : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K) :
    dyadicPowerContent s (⋂ n, K n) = ⨅ n, dyadicPowerContent s (K n) := by
  apply le_antisymm
  · exact le_iInf fun n ↦ dyadicCoverContent_mono _ (iInter_subset K n)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    obtain ⟨U, hU, hsub, hcost⟩ :=
      exists_open_superset_dyadicPowerContent_le hs (⋂ n, K n) hε hfinite.ne
    obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact' hanti.directed_ge hK
      (fun n ↦ (hK n).isClosed) (hU.mem_nhdsSet.mpr hsub)
    exact (iInf_le (fun n ↦ dyadicPowerContent s (K n)) n).trans
      ((dyadicCoverContent_mono _ hn).trans hcost)

/-- The concrete planar dyadic power content is a Choquet capacity for `s > 1`. -/
theorem isChoquetCapacity_dyadicPowerContent {s : ℝ} (hs : 1 < s) :
    IsChoquetCapacity (dyadicPowerContent s) where
  map_empty := by
    apply le_antisymm _ zero_le
    exact (dyadicCoverContent_le_cost _ (S := ∅) (empty_subset _)).trans_eq
      (by simp [dyadicCoverCost])
  monotone := dyadicCoverContent_mono _
  map_iUnion _ hE := dyadicCoverContent_iUnion _ hE
  map_iInter _ hK hanti _ := dyadicPowerContent_iInter hs hK hanti

/-- Positive dyadic content on an analytic planar set is witnessed by a compact subset. -/
theorem exists_isCompact_subset_dyadicPowerContent_pos {s : ℝ} (hs : 1 < s)
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : AnalyticSet E)
    (hpos : 0 < dyadicPowerContent s E) :
    ∃ K, IsCompact K ∧ K ⊆ E ∧ 0 < dyadicPowerContent s K :=
  (isChoquetCapacity_dyadicPowerContent hs).exists_isCompact_subset_of_analyticSet hE hpos

end FalconerPacking
