/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dyadic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Antichain
import Mathlib.Order.WellFounded
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Laminar covers and continuity of dyadic content

The cover-merging argument uses maximal cubes in cumulative covers. Their weighted costs
telescope because the maximal union and the smaller overlaps account for both original covers.
The concrete dyadic order below has finite ascending chains, since coarser cubes have smaller
natural-number generations.
-/

noncomputable section

open Set
open scoped ENNReal

namespace FalconerPacking

/-- An address of one cube in the existing planar dyadic hierarchy. -/
structure DyadicCell where
  level : ℕ
  index : Fin 2 → ℤ
  deriving DecidableEq

/-- The half-open square represented by an address. -/
def DyadicCell.carrier (Q : DyadicCell) : Set (EuclideanSpace ℝ (Fin 2)) :=
  dyadicCube Q.level Q.index

/-- Every dyadic cube contains its lower coordinate corner. -/
theorem dyadicCube_nonempty (n : ℕ) (k : Fin 2 → ℤ) : (dyadicCube n k).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun i ↦ (k i : ℝ) / (2 : ℝ) ^ n), fun i ↦ ?_⟩
  have hp : (2 : ℝ) ^ n ≠ 0 := by positivity
  change (k i : ℝ) ≤ 2 ^ n * ((k i : ℝ) / 2 ^ n) ∧
    2 ^ n * ((k i : ℝ) / 2 ^ n) < (k i : ℝ) + 1
  rw [mul_div_cancel₀ _ hp]
  constructor
  · exact le_rfl
  · linarith

/-- If two cubes meet, the cube of finer generation lies in the coarser one. -/
theorem dyadicCube_subset_of_le_of_mem {n m : ℕ} (hnm : n ≤ m)
    {k l : Fin 2 → ℤ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ dyadicCube n k) (hy : x ∈ dyadicCube m l) :
    dyadicCube m l ⊆ dyadicCube n k := by
  have hsub := dyadicCube_subset_ancestor n (m - n) l
  rw [Nat.add_sub_of_le hnm] at hsub
  have hidx : ancestor (m - n) l = k :=
    (mem_dyadicCube_iff.mp (hsub hy)).symm.trans (mem_dyadicCube_iff.mp hx)
  simpa only [hidx] using hsub

instance : PartialOrder DyadicCell where
  le Q R := R.level ≤ Q.level ∧ Q.carrier ⊆ R.carrier
  le_refl Q := ⟨le_rfl, subset_rfl⟩
  le_trans _ _ _ hQR hRS := ⟨hRS.1.trans hQR.1, hQR.2.trans hRS.2⟩
  le_antisymm Q R hQR hRQ := by
    have hlev : Q.level = R.level := le_antisymm hRQ.1 hQR.1
    obtain ⟨x, hx⟩ := dyadicCube_nonempty Q.level Q.index
    have hR := hQR.2 hx
    have hidx : Q.index = R.index := by
      rw [← mem_dyadicCube_iff.mp hx, ← mem_dyadicCube_iff.mp hR, hlev]
    cases Q
    cases R
    simp_all

/-- Coarser cubes have strictly smaller generation. -/
theorem DyadicCell.level_strictAnti : StrictAnti DyadicCell.level := by
  intro Q R hQR
  apply lt_of_le_of_ne hQR.le.1
  intro hlev
  obtain ⟨x, hx⟩ := dyadicCube_nonempty Q.level Q.index
  have hR := hQR.le.2 hx
  have hsub : R.carrier ⊆ Q.carrier :=
    dyadicCube_subset_of_le_of_mem hlev.ge hx hR
  exact hQR.not_ge ⟨hlev.ge, hsub⟩

instance : WellFoundedGT DyadicCell := DyadicCell.level_strictAnti.wellFoundedGT

/-- Intersecting cubes are comparable in the inclusion order. -/
theorem DyadicCell.le_or_le_of_mem {Q R : DyadicCell}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ Q.carrier) (hy : x ∈ R.carrier) :
    Q ≤ R ∨ R ≤ Q := by
  rcases le_total Q.level R.level with h | h
  · exact Or.inr ⟨h, dyadicCube_subset_of_le_of_mem h hx hy⟩
  · exact Or.inl ⟨h, dyadicCube_subset_of_le_of_mem h hy hx⟩

/-- The union covered by a family of dyadic addresses. -/
def dyadicCoverUnion (S : Set DyadicCell) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ Q ∈ S, Q.carrier

/-- Maximal addresses retain the coarsest cube wherever members of a cover overlap. -/
def dyadicCoverMaxima (S : Set DyadicCell) : Set DyadicCell :=
  {Q | Maximal (· ∈ S) Q}

/-- Every member of a cover lies in a maximal member. -/
theorem exists_dyadicCoverMaxima_ge {S : Set DyadicCell} {Q : DyadicCell} (hQ : Q ∈ S) :
    ∃ R ∈ dyadicCoverMaxima S, Q ≤ R := by
  obtain ⟨R, hR⟩ := WellFoundedGT.exists_maximal (inferInstance : WellFoundedGT DyadicCell)
    (S ∩ Ici Q) ⟨Q, hQ, mem_Ici.mpr le_rfl⟩
  exact ⟨R, ⟨hR.1.1, fun T hT hRT ↦ hR.2 ⟨hT, hR.1.2.trans hRT⟩ hRT⟩, hR.1.2⟩

/-- Maximal cubes form an antichain. -/
theorem isAntichain_dyadicCoverMaxima (S : Set DyadicCell) :
    IsAntichain (· ≤ ·) (dyadicCoverMaxima S) := setOf_maximal_antichain _

/-- Removing nonmaximal cubes leaves exactly the same covered set. -/
theorem dyadicCoverUnion_maxima (S : Set DyadicCell) :
    dyadicCoverUnion (dyadicCoverMaxima S) = dyadicCoverUnion S := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨Q, hQ.1, hxQ⟩
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hx
    obtain ⟨R, hR, hQR⟩ := exists_dyadicCoverMaxima_ge hQ
    exact mem_iUnion₂.mpr ⟨R, hR, hQR.2 hxQ⟩

/-- Cost of a selected family, with arbitrary nonnegative extended-real cube weights. -/
def dyadicCoverCost (w : DyadicCell → ℝ≥0∞) (S : Set DyadicCell) : ℝ≥0∞ :=
  ∑' Q, S.indicator w Q

/-- Discarding cubes cannot increase cost. -/
theorem dyadicCoverCost_mono (w : DyadicCell → ℝ≥0∞) {S T : Set DyadicCell} (hST : S ⊆ T) :
    dyadicCoverCost w S ≤ dyadicCoverCost w T := by
  apply ENNReal.tsum_le_tsum
  intro Q
  by_cases hQ : Q ∈ S
  · simp only [indicator_of_mem hQ, indicator_of_mem (hST hQ), le_refl]
  · simp only [indicator_of_notMem hQ, zero_le]

/-- Smaller cubes in overlaps of two covers. -/
def dyadicCoverOverlap (S T : Set DyadicCell) : Set DyadicCell :=
  {Q | (Q ∈ S ∧ ∃ R ∈ T, Q ≤ R) ∨ (Q ∈ T ∧ ∃ R ∈ S, Q ≤ R)}

/-- The smaller-overlap family covers the intersection of the covered sets. -/
theorem inter_dyadicCoverUnion_subset_overlap (S T : Set DyadicCell) :
    dyadicCoverUnion S ∩ dyadicCoverUnion T ⊆ dyadicCoverUnion (dyadicCoverOverlap S T) := by
  rintro x ⟨hxS, hxT⟩
  obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp hxS
  obtain ⟨R, hR, hxR⟩ := mem_iUnion₂.mp hxT
  rcases DyadicCell.le_or_le_of_mem hxQ hxR with hQR | hRQ
  · exact mem_iUnion₂.mpr ⟨Q, Or.inl ⟨hQ, R, hR, hQR⟩, hxQ⟩
  · exact mem_iUnion₂.mpr ⟨R, Or.inr ⟨hR, Q, hQ, hRQ⟩, hxR⟩

/-- For antichains, a cube in just one family belongs to exactly one of the maximal union
and the smaller overlaps. -/
theorem mem_dyadicCoverMaxima_union_iff
    {S T : Set DyadicCell} (hS : IsAntichain (· ≤ ·) S) (hT : IsAntichain (· ≤ ·) T)
    {Q : DyadicCell} :
    Q ∈ dyadicCoverMaxima (S ∪ T) ↔ (Q ∈ S ∧ Q ∈ T) ∨
      ((Q ∈ S ∨ Q ∈ T) ∧ Q ∉ dyadicCoverOverlap S T) := by
  constructor
  · intro hQ
    by_cases hboth : Q ∈ S ∧ Q ∈ T
    · exact Or.inl hboth
    refine Or.inr ⟨hQ.1, ?_⟩
    rintro (⟨hQS, R, hRT, hQR⟩ | ⟨hQT, R, hRS, hQR⟩)
    · have heq := le_antisymm hQR (hQ.2 (Or.inr hRT) hQR)
      exact hboth ⟨hQS, heq ▸ hRT⟩
    · have heq := le_antisymm hQR (hQ.2 (Or.inl hRS) hQR)
      exact hboth ⟨heq ▸ hRS, hQT⟩
  · rintro (⟨hQS, hQT⟩ | ⟨hQ, hnot⟩)
    · refine ⟨Or.inl hQS, fun R hR hQR ↦ ?_⟩
      rcases hR with hRS | hRT
      · exact (hS.eq hQS hRS hQR).symm.le
      · exact (hT.eq hQT hRT hQR).symm.le
    · refine ⟨hQ, fun R hR hQR ↦ ?_⟩
      rcases hQ with hQS | hQT <;> rcases hR with hRS | hRT
      · exact (hS.eq hQS hRS hQR).symm.le
      · exact False.elim (hnot (Or.inl ⟨hQS, R, hRT, hQR⟩))
      · exact False.elim (hnot (Or.inr ⟨hQT, R, hRS, hQR⟩))
      · exact (hT.eq hQT hRT hQR).symm.le

/-- Exact cost accounting for merging two disjoint dyadic covers. -/
theorem dyadicCoverCost_maxima_union_add_overlap
    (w : DyadicCell → ℝ≥0∞) {S T : Set DyadicCell}
    (hS : IsAntichain (· ≤ ·) S) (hT : IsAntichain (· ≤ ·) T) :
    dyadicCoverCost w (dyadicCoverMaxima (S ∪ T)) +
      dyadicCoverCost w (dyadicCoverOverlap S T) = dyadicCoverCost w S + dyadicCoverCost w T := by
  classical
  simp only [dyadicCoverCost, ← ENNReal.tsum_add]
  apply tsum_congr
  intro Q
  have hm := mem_dyadicCoverMaxima_union_iff hS hT (Q := Q)
  by_cases hQS : Q ∈ S <;> by_cases hQT : Q ∈ T
  · have ho : Q ∈ dyadicCoverOverlap S T := Or.inl ⟨hQS, Q, hQT, le_rfl⟩
    simp [hQS, hQT, ho, hm.mpr (Or.inl ⟨hQS, hQT⟩)]
  · by_cases ho : Q ∈ dyadicCoverOverlap S T <;> simp_all
  · by_cases ho : Q ∈ dyadicCoverOverlap S T <;> simp_all
  · have ho : Q ∉ dyadicCoverOverlap S T := by simp [dyadicCoverOverlap, hQS, hQT]
    simp_all

/-- Content obtained by taking the infimum over actual dyadic covers. -/
def dyadicCoverContent (w : DyadicCell → ℝ≥0∞)
    (E : Set (EuclideanSpace ℝ (Fin 2))) : ℝ≥0∞ :=
  ⨅ S : Set DyadicCell, ⨅ (_ : E ⊆ dyadicCoverUnion S), dyadicCoverCost w S

/-- Each covering family bounds the dyadic content. -/
theorem dyadicCoverContent_le_cost (w : DyadicCell → ℝ≥0∞)
    {E : Set (EuclideanSpace ℝ (Fin 2))} {S : Set DyadicCell}
    (hS : E ⊆ dyadicCoverUnion S) : dyadicCoverContent w E ≤ dyadicCoverCost w S :=
  iInf_le_of_le S (iInf_le_of_le hS le_rfl)

/-- Monotonicity follows directly from the covering definition. -/
theorem dyadicCoverContent_mono (w : DyadicCell → ℝ≥0∞) :
    Monotone (dyadicCoverContent w) := by
  intro E F hEF
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  exact dyadicCoverContent_le_cost w (hEF.trans hS)

/-- Near-optimal covers may be chosen to consist of pairwise incomparable cubes. -/
theorem exists_antichain_dyadicCoverCost_lt (w : DyadicCell → ℝ≥0∞)
    {E : Set (EuclideanSpace ℝ (Fin 2))} {b : ℝ≥0∞}
    (hb : dyadicCoverContent w E < b) :
    ∃ S : Set DyadicCell, IsAntichain (· ≤ ·) S ∧ E ⊆ dyadicCoverUnion S ∧
      dyadicCoverCost w S < b := by
  obtain ⟨S, hS⟩ := iInf_lt_iff.mp hb
  obtain ⟨hcover, hcost⟩ := iInf_lt_iff.mp hS
  refine ⟨dyadicCoverMaxima S, isAntichain_dyadicCoverMaxima S, ?_, ?_⟩
  · simpa only [dyadicCoverUnion_maxima] using hcover
  · exact (dyadicCoverCost_mono w (fun _ hQ ↦ hQ.1)).trans_lt hcost

/-- A merge preserves all of the covered points. -/
theorem dyadicCoverUnion_union (S T : Set DyadicCell) :
    dyadicCoverUnion (S ∪ T) = dyadicCoverUnion S ∪ dyadicCoverUnion T := by
  ext x
  simp only [dyadicCoverUnion, mem_iUnion, mem_union]
  aesop

/-- Cumulative covers, keeping only the maximal cubes after each merge. -/
def dyadicMergedCover (C : ℕ → Set DyadicCell) : ℕ → Set DyadicCell
  | 0 => dyadicCoverMaxima (C 0)
  | n + 1 => dyadicCoverMaxima (dyadicMergedCover C n ∪ C (n + 1))

/-- Every cumulative cover is an antichain. -/
theorem isAntichain_dyadicMergedCover (C : ℕ → Set DyadicCell) (n : ℕ) :
    IsAntichain (· ≤ ·) (dyadicMergedCover C n) := by
  cases n <;> exact isAntichain_dyadicCoverMaxima _

/-- A cumulative cover contains only cubes drawn from the input families. -/
theorem dyadicMergedCover_subset_iUnion (C : ℕ → Set DyadicCell) (n : ℕ) :
    dyadicMergedCover C n ⊆ ⋃ j, C j := by
  induction n with
  | zero => exact fun Q hQ ↦ mem_iUnion.mpr ⟨0, hQ.1⟩
  | succ n ih =>
    intro Q hQ
    rcases hQ.1 with hprev | hnew
    · exact ih hprev
    · exact mem_iUnion.mpr ⟨n + 1, hnew⟩

/-- Each cumulative cover covers the corresponding set in any increasing covered sequence. -/
theorem subset_dyadicCoverUnion_merged {C : ℕ → Set DyadicCell}
    {E : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hcover : ∀ n, E n ⊆ dyadicCoverUnion (C n)) (n : ℕ) :
    E n ⊆ dyadicCoverUnion (dyadicMergedCover C n) := by
  cases n with
  | zero => simpa only [dyadicMergedCover, dyadicCoverUnion_maxima] using hcover 0
  | succ n =>
    rw [dyadicMergedCover, dyadicCoverUnion_maxima, dyadicCoverUnion_union]
    exact (hcover (n + 1)).trans subset_union_right

/-- A globally maximal cube remains maximal in every subfamily containing it. -/
theorem mem_dyadicCoverMaxima_of_subset {S T : Set DyadicCell} (hST : S ⊆ T)
    {Q : DyadicCell} (hQ : Q ∈ dyadicCoverMaxima T) (hQS : Q ∈ S) :
    Q ∈ dyadicCoverMaxima S := ⟨hQS, fun _ hR hQR ↦ hQ.2 (hST hR) hQR⟩

/-- A maximal cube in the full union persists in every cumulative cover after its first entry. -/
theorem mem_dyadicMergedCover_of_maximal {C : ℕ → Set DyadicCell} {Q : DyadicCell}
    (hQ : Q ∈ dyadicCoverMaxima (⋃ j, C j)) {i : ℕ} (hi : Q ∈ C i) :
    ∀ n, i ≤ n → Q ∈ dyadicMergedCover C n := by
  intro n
  induction n with
  | zero =>
    intro hin
    have : i = 0 := Nat.eq_zero_of_le_zero hin
    subst i
    exact mem_dyadicCoverMaxima_of_subset (subset_iUnion C 0) hQ hi
  | succ n ih =>
    intro hin
    refine mem_dyadicCoverMaxima_of_subset ?_ hQ ?_
    · intro R hR
      rcases hR with hprev | hnew
      · exact dyadicMergedCover_subset_iUnion C n hprev
      · exact mem_iUnion.mpr ⟨n + 1, hnew⟩
    · rcases eq_or_lt_of_le hin with heq | hlt
      · exact Or.inr (heq ▸ hi)
      · exact Or.inl (ih (Nat.le_of_lt_succ hlt))

/-- The cost of the final maximal union is bounded by the supremum of the cumulative costs. -/
theorem dyadicCoverCost_maxima_iUnion_le (w : DyadicCell → ℝ≥0∞)
    (C : ℕ → Set DyadicCell) :
    dyadicCoverCost w (dyadicCoverMaxima (⋃ j, C j)) ≤
      ⨆ n, dyadicCoverCost w (dyadicMergedCover C n) := by
  classical
  let D := dyadicCoverMaxima (⋃ j, C j)
  have hentry (Q : DyadicCell) (hQ : Q ∈ D) : ∃ i, Q ∈ C i := mem_iUnion.mp hQ.1
  let entry (Q : DyadicCell) := if hQ : Q ∈ D then (hentry Q hQ).choose else 0
  have hstage (Q : DyadicCell) (hQ : Q ∈ D) (n : ℕ) (hn : entry Q ≤ n) :
      Q ∈ dyadicMergedCover C n := by
    have hi : Q ∈ C (entry Q) := by
      simpa only [entry, dif_pos hQ] using (hentry Q hQ).choose_spec
    exact mem_dyadicMergedCover_of_maximal hQ hi n hn
  rw [dyadicCoverCost, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro F
  have hsum : (∑ Q ∈ F, D.indicator w Q) ≤
      ∑ Q ∈ F, (dyadicMergedCover C (F.sup entry)).indicator w Q := by
    apply Finset.sum_le_sum
    intro Q hQF
    by_cases hQD : Q ∈ D
    · simp only [indicator_of_mem hQD, indicator_of_mem (hstage Q hQD _ (Finset.le_sup hQF))]
      exact le_rfl
    · simp only [indicator_of_notMem hQD, zero_le]
  exact hsum.trans ((ENNReal.sum_le_tsum F).trans
    (le_iSup (fun n ↦ dyadicCoverCost w (dyadicMergedCover C n)) (F.sup entry)))

/-- One merge pays only for the new cover after subtracting the content already covered. -/
theorem dyadicMergedCover_cost_step (w : DyadicCell → ℝ≥0∞)
    {C : ℕ → Set DyadicCell} {E : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hE : Monotone E) (hC : ∀ n, IsAntichain (· ≤ ·) (C n))
    (hcover : ∀ n, E n ⊆ dyadicCoverUnion (C n)) (n : ℕ) :
    dyadicCoverCost w (dyadicMergedCover C (n + 1)) + dyadicCoverContent w (E n) ≤
      dyadicCoverCost w (dyadicMergedCover C n) + dyadicCoverCost w (C (n + 1)) := by
  have hsub : E n ⊆ dyadicCoverUnion (dyadicCoverOverlap (dyadicMergedCover C n) (C (n + 1))) := by
    intro x hx
    apply inter_dyadicCoverUnion_subset_overlap _ _
    exact ⟨subset_dyadicCoverUnion_merged hcover n hx,
      hcover (n + 1) (hE (Nat.le_succ n) hx)⟩
  calc
    _ ≤ dyadicCoverCost w (dyadicMergedCover C (n + 1)) +
        dyadicCoverCost w (dyadicCoverOverlap (dyadicMergedCover C n) (C (n + 1))) :=
      add_le_add le_rfl (dyadicCoverContent_le_cost w hsub)
    _ = _ := dyadicCoverCost_maxima_union_add_overlap w
      (isAntichain_dyadicMergedCover C n) (hC (n + 1))

/-- Near-optimal cover errors telescope along an increasing sequence. -/
theorem dyadicMergedCover_cost_le (w : DyadicCell → ℝ≥0∞)
    {C : ℕ → Set DyadicCell} {E : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (hE : Monotone E) (hC : ∀ n, IsAntichain (· ≤ ·) (C n))
    (hcover : ∀ n, E n ⊆ dyadicCoverUnion (C n))
    (hfinite : ∀ n, dyadicCoverContent w (E n) ≠ ∞) {δ : ℕ → ℝ≥0∞}
    (hcost : ∀ n, dyadicCoverCost w (C n) ≤ dyadicCoverContent w (E n) + δ n) (n : ℕ) :
    dyadicCoverCost w (dyadicMergedCover C n) ≤
      dyadicCoverContent w (E n) + ∑ j ∈ Finset.range (n + 1), δ j := by
  induction n with
  | zero =>
    have hsub : dyadicMergedCover C 0 ⊆ C 0 := fun _ hQ ↦ hQ.1
    simpa only [Nat.zero_add, Finset.range_one, Finset.sum_singleton] using
      (dyadicCoverCost_mono w hsub).trans (hcost 0)
  | succ n ih =>
    apply ENNReal.le_of_add_le_add_right (hfinite n)
    calc
      _ ≤ dyadicCoverCost w (dyadicMergedCover C n) + dyadicCoverCost w (C (n + 1)) :=
        dyadicMergedCover_cost_step w hE hC hcover n
      _ ≤ (dyadicCoverContent w (E n) + ∑ j ∈ Finset.range (n + 1), δ j) +
          (dyadicCoverContent w (E (n + 1)) + δ (n + 1)) := add_le_add ih (hcost (n + 1))
      _ = _ := by rw [Finset.sum_range_succ δ (n + 1)]; ac_rfl

/-- Dyadic content is continuous on increasing unions, for arbitrary nonnegative cube weights.
The only geometric inputs are dyadic nesting and the absence of infinite ascending cube chains. -/
theorem dyadicCoverContent_iUnion (w : DyadicCell → ℝ≥0∞)
    {E : ℕ → Set (EuclideanSpace ℝ (Fin 2))} (hE : Monotone E) :
    dyadicCoverContent w (⋃ n, E n) = ⨆ n, dyadicCoverContent w (E n) := by
  classical
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hfinite
    obtain ⟨δ, hδpos, hδsum⟩ :=
      ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.mpr hε).ne' ℕ
    have hfin (n : ℕ) : dyadicCoverContent w (E n) ≠ ∞ :=
      ((le_iSup (fun n ↦ dyadicCoverContent w (E n)) n).trans_lt hfinite).ne
    have hnear (n : ℕ) : ∃ S : Set DyadicCell, IsAntichain (· ≤ ·) S ∧
        E n ⊆ dyadicCoverUnion S ∧
          dyadicCoverCost w S < dyadicCoverContent w (E n) + δ n :=
      exists_antichain_dyadicCoverCost_lt w
        (ENNReal.lt_add_right (hfin n) (ENNReal.coe_pos.mpr (hδpos n)).ne')
    choose C hC hcover hcost using hnear
    have hbound (n : ℕ) : dyadicCoverCost w (dyadicMergedCover C n) ≤
        (⨆ n, dyadicCoverContent w (E n)) + (ε : ℝ≥0∞) := by
      refine (dyadicMergedCover_cost_le w hE hC hcover hfin (fun n ↦ (hcost n).le) n).trans ?_
      exact add_le_add (le_iSup (fun n ↦ dyadicCoverContent w (E n)) n)
        ((ENNReal.sum_le_tsum _).trans hδsum.le)
    have hfinal : (⋃ n, E n) ⊆ dyadicCoverUnion (dyadicCoverMaxima (⋃ n, C n)) := by
      rw [dyadicCoverUnion_maxima]
      intro x hx
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
      obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp (hcover n hxn)
      exact mem_iUnion₂.mpr ⟨Q, mem_iUnion.mpr ⟨n, hQ⟩, hxQ⟩
    exact (dyadicCoverContent_le_cost w hfinal).trans
      ((dyadicCoverCost_maxima_iUnion_le w C).trans (iSup_le hbound))
  · exact iSup_le fun n ↦ dyadicCoverContent_mono w (subset_iUnion E n)

end FalconerPacking
