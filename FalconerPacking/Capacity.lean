/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Sequences

/-!
# Compact extraction for capacities on analytic sets

The capacity assumptions in this file are explicit hypotheses. In particular, no assertion
that Hausdorff content satisfies these assumptions is made here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FalconerPacking

/-- The monotonicity and sequential continuity properties used in compact extraction. -/
structure IsChoquetCapacity {α : Type*} [TopologicalSpace α]
    (c : Set α → ℝ≥0∞) : Prop where
  map_empty : c ∅ = 0
  monotone : Monotone c
  map_iUnion (S : ℕ → Set α) (hS : Monotone S) : c (⋃ n, S n) = ⨆ n, c (S n)
  map_iInter (K : ℕ → Set α) (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K)
    (hne : ∀ n, (K n).Nonempty) : c (⋂ n, K n) = ⨅ n, c (K n)

/-- An increasing exhaustion preserves any strict lower capacity bound at a finite stage. -/
theorem IsChoquetCapacity.exists_lt_of_iUnion {α : Type*} [TopologicalSpace α]
    {c : Set α → ℝ≥0∞} (hc : IsChoquetCapacity c) {S : ℕ → Set α}
    (hS : Monotone S) {a : ℝ≥0∞} (ha : a < c (⋃ n, S n)) : ∃ n, a < c (S n) := by
  rw [hc.map_iUnion S hS] at ha
  exact lt_iSup_iff.mp ha

/-- One Baire-space coordinate may be bounded while preserving a strict capacity bound. -/
theorem IsChoquetCapacity.exists_coordinate_cutoff {α : Type*} [TopologicalSpace α]
    {c : Set α → ℝ≥0∞} (hc : IsChoquetCapacity c) (f : (ℕ → ℕ) → α)
    (S : Set (ℕ → ℕ)) (n : ℕ) {a : ℝ≥0∞} (ha : a < c (f '' S)) :
    ∃ k : ℕ, a < c (f '' (S ∩ {x | x n ≤ k})) := by
  have hcover : (⋃ k : ℕ, S ∩ {x | x n ≤ k}) = S := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_setOf_eq]
    exact ⟨fun ⟨_, hx, _⟩ ↦ hx, fun hx ↦ ⟨x n, hx, le_rfl⟩⟩
  have hmono : Monotone (fun k : ℕ ↦ f '' (S ∩ {x | x n ≤ k})) := by
    intro k l hkl
    exact image_mono (inter_subset_inter_right S (fun _ hx ↦ hx.trans hkl))
  apply hc.exists_lt_of_iUnion hmono
  rwa [← image_iUnion, hcover]

/-- Repeated coordinate cutoffs preserve one fixed strict capacity margin. -/
theorem IsChoquetCapacity.exists_baire_restrictions {α : Type*} [TopologicalSpace α]
    {c : Set α → ℝ≥0∞} (hc : IsChoquetCapacity c) (f : (ℕ → ℕ) → α)
    (A : Set (ℕ → ℕ)) {a : ℝ≥0∞} (ha : a < c (f '' A)) :
    ∃ S : ℕ → Set (ℕ → ℕ), S 0 = A ∧ Antitone S ∧
      (∀ n, a < c (f '' S n)) ∧ (∀ i, ∃ M : ℕ, ∀ x ∈ S (i + 1), x i ≤ M) := by
  classical
  let X := {S : Set (ℕ → ℕ) // a < c (f '' S)}
  let step (n : ℕ) (S : X) : X :=
    ⟨S.1 ∩ {x | x n ≤ (hc.exists_coordinate_cutoff f S.1 n S.2).choose},
      (hc.exists_coordinate_cutoff f S.1 n S.2).choose_spec⟩
  let T : ℕ → X := Nat.rec ⟨A, ha⟩ step
  refine ⟨fun n ↦ (T n).1, rfl, ?_, fun n ↦ (T n).2, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    exact inter_subset_left
  · intro i
    refine ⟨(hc.exists_coordinate_cutoff f (T i).1 i (T i).2).choose, ?_⟩
    intro x hx
    exact hx.2

/-- A sequence in Baire space whose coordinates are eventually bounded has a convergent
subsequence. The finitely many early values are included in the compact product. -/
theorem exists_baire_subseq_tendsto_of_eventually_bounded
    (x : ℕ → ℕ → ℕ) (hbound : ∀ i, ∃ M N : ℕ, ∀ n ≥ N, x n i ≤ M) :
    ∃ z : ℕ → ℕ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 z) := by
  classical
  choose M N hMN using hbound
  let B : ℕ → ℕ := fun i ↦ max (M i) ((Finset.range (N i)).sup fun n ↦ x n i)
  have hB : ∀ n i, x n i ≤ B i := by
    intro n i
    by_cases hn : N i ≤ n
    · exact (hMN i n hn).trans (le_max_left _ _)
    · exact (Finset.le_sup (f := fun n ↦ x n i)
        (Finset.mem_range.mpr (lt_of_not_ge hn))).trans
        (le_max_right _ _)
  have hcompact : IsCompact {z : ℕ → ℕ | ∀ i, z i ∈ Iic (B i)} :=
    isCompact_pi_infinite fun i ↦ (finite_Iic (B i)).isCompact
  obtain ⟨z, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq fun n i ↦ hB n i
  exact ⟨z, φ, hφ, hlim⟩

/-- Successively bounding all source coordinates prevents limits of images from escaping
the range of a continuous map from Baire space. -/
theorem iInter_closure_image_subset_range_of_coordinate_bounds
    {α : Type*} [MetricSpace α] {f : (ℕ → ℕ) → α} (hf : Continuous f)
    (S : ℕ → Set (ℕ → ℕ)) (hS : Antitone S)
    (hbound : ∀ i, ∃ M : ℕ, ∀ x ∈ S (i + 1), x i ≤ M) :
    (⋂ n, closure (f '' S n)) ⊆ range f := by
  intro y hy
  have hex (n : ℕ) : ∃ x ∈ S n, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    obtain ⟨v, ⟨x, hx, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp (mem_iInter.mp hy n)
      (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨x, hx, by simpa only [dist_comm] using hv⟩
  choose x hx hdist using hex
  have hxb : ∀ i, ∃ M N : ℕ, ∀ n ≥ N, x n i ≤ M := by
    intro i
    obtain ⟨M, hM⟩ := hbound i
    exact ⟨M, i + 1, fun n hn ↦ hM (x n) (hS hn (hx n))⟩
  obtain ⟨z, φ, hφ, hlim⟩ := exists_baire_subseq_tendsto_of_eventually_bounded x hxb
  have himage : Tendsto (f ∘ x) atTop (𝓝 y) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn ↦ (hdist n).trans_le ?_⟩
    exact (one_div_le_one_div_of_le (by positivity : 0 < (N : ℝ) + 1)
      (by exact_mod_cast Nat.add_le_add_right hn 1)).trans hN.le
  have heq : f z = y := tendsto_nhds_unique (hf.tendsto z |>.comp hlim)
    (himage.comp hφ.tendsto_atTop)
  exact ⟨z, heq⟩

/-- A bounded part of a continuous Baire-space image can be compactly extracted without
losing any prescribed strict lower capacity bound. -/
theorem IsChoquetCapacity.exists_isCompact_subset_range_of_image_subset
    {α : Type*} [MetricSpace α] {c : Set α → ℝ≥0∞} (hc : IsChoquetCapacity c)
    {f : (ℕ → ℕ) → α} (hf : Continuous f) {A : Set (ℕ → ℕ)}
    {B : Set α} (hB : IsCompact B) (hAB : f '' A ⊆ B)
    {a : ℝ≥0∞} (ha : a < c (f '' A)) :
    ∃ K : Set α, IsCompact K ∧ K ⊆ range f ∧ a < c K := by
  obtain ⟨b, hab, hb⟩ := exists_between ha
  obtain ⟨S, hS0, hS, hSc, hSb⟩ := hc.exists_baire_restrictions f A hb
  let K : ℕ → Set α := fun n ↦ closure (f '' S n)
  have hKB (n : ℕ) : K n ⊆ B := by
    apply closure_minimal _ hB.isClosed
    exact (image_mono (hS (Nat.zero_le n))).trans (hS0 ▸ hAB)
  have hKc (n : ℕ) : IsCompact (K n) :=
    hB.of_isClosed_subset isClosed_closure (hKB n)
  have hKa : Antitone K := fun i j hij ↦ closure_mono (image_mono (hS hij))
  have hKcap (n : ℕ) : b < c (K n) :=
    (hSc n).trans_le (hc.monotone subset_closure)
  have hKne (n : ℕ) : (K n).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    have hpos := (bot_le : (0 : ℝ≥0∞) ≤ b).trans_lt (hKcap n)
    simp [hn, hc.map_empty] at hpos
  refine ⟨⋂ n, K n, (hKc 0).of_isClosed_subset
    (isClosed_iInter fun n ↦ isClosed_closure) (iInter_subset K 0), ?_, ?_⟩
  · exact iInter_closure_image_subset_range_of_coordinate_bounds hf S hS hSb
  · apply hab.trans_le
    rw [hc.map_iInter K hKc hKa hKne]
    exact le_iInf fun n ↦ (hKcap n).le

/-- Choquet compact extraction for analytic sets in a proper metric space. The three
capacity properties are hypotheses, not conclusions about a particular geometric content. -/
theorem IsChoquetCapacity.exists_isCompact_subset_of_analyticSet
    {α : Type*} [MetricSpace α] [ProperSpace α] {c : Set α → ℝ≥0∞}
    (hc : IsChoquetCapacity c) {A : Set α} (hA : AnalyticSet A)
    {a : ℝ≥0∞} (ha : a < c A) :
    ∃ K : Set α, IsCompact K ∧ K ⊆ A ∧ a < c K := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · simp [hc.map_empty] at ha
  let p : α := f fun _ ↦ 0
  have hcover : (⋃ n : ℕ, f '' (f ⁻¹' Metric.closedBall p n)) = range f := by
    rw [← image_iUnion, ← preimage_iUnion, Metric.iUnion_closedBall_nat, preimage_univ,
      image_univ]
  have hmono : Monotone (fun n : ℕ ↦ f '' (f ⁻¹' Metric.closedBall p n)) := by
    intro n m hnm
    exact image_mono (preimage_mono
      (Metric.closedBall_subset_closedBall (by exact_mod_cast hnm)))
  obtain ⟨n, hn⟩ := hc.exists_lt_of_iUnion hmono (hcover ▸ ha)
  exact hc.exists_isCompact_subset_range_of_image_subset hf
    (isCompact_closedBall p n) (image_preimage_subset f _) hn

/-- Borel sets in a proper Polish metric space satisfy compact extraction for any capacity
with the stated monotonicity and continuity properties. -/
theorem IsChoquetCapacity.exists_isCompact_subset_of_measurableSet
    {α : Type*} [MetricSpace α] [ProperSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {c : Set α → ℝ≥0∞}
    (hc : IsChoquetCapacity c) {A : Set α} (hA : MeasurableSet A)
    {a : ℝ≥0∞} (ha : a < c A) :
    ∃ K : Set α, IsCompact K ∧ K ⊆ A ∧ a < c K :=
  hc.exists_isCompact_subset_of_analyticSet hA.analyticSet ha

end FalconerPacking
