/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.FrostmanWeights
public import FalconerPacking.Restriction
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Finite regularization by restriction

The construction in this file selects subsets of terminal cells and never changes their weights.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace FalconerPacking

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

private lemma exists_weight_bin_aux {M v : ℝ} {D : ℕ} (hv : 0 < v) (hvM : v ≤ M)
    (hlarge : M < v * 2 ^ (D + 1)) :
    ∃ k ∈ range (D + 1), v * 2 ^ k ≤ M ∧ M < v * 2 ^ (k + 1) := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((one_le_div hv).2 hvM)
    (show (1 : ℝ) < 2 by norm_num)
  have hupper : v * 2 ^ k ≤ M := by nlinarith [(le_div_iff₀ hv).1 hk]
  have hlower : M < v * 2 ^ (k + 1) := by nlinarith [(div_lt_iff₀ hv).1 hk']
  refine ⟨k, mem_range.2 ?_, hupper, hlower⟩
  by_contra h
  have hp : (2 : ℝ) ^ (D + 1) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

omit [DecidableEq α] in
private lemma small_weights_sum_le_aux (S : Finset α) (w : α → ℝ) (D : ℕ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hcard : S.card ≤ 2 ^ D) :
    2 * ∑ x ∈ S.filter (fun x ↦ w x * 2 ^ (D + 1) ≤ ∑ y ∈ S, w y), w x ≤
      ∑ x ∈ S, w x := by
  let M := ∑ x ∈ S, w x
  let A := S.filter (fun x ↦ w x * 2 ^ (D + 1) ≤ M)
  have hM : 0 ≤ M := sum_nonneg hw
  have hsum : (∑ x ∈ A, w x) * 2 ^ (D + 1) ≤ A.card * M := by
    rw [sum_mul]
    calc
      ∑ x ∈ A, w x * 2 ^ (D + 1) ≤ ∑ _x ∈ A, M :=
        sum_le_sum fun x hx ↦ (mem_filter.1 hx).2
      _ = A.card * M := by simp
  have hAc : (A.card : ℝ) ≤ (2 : ℝ) ^ D := by
    exact_mod_cast (card_le_card (filter_subset _ S)).trans hcard
  have hp : 0 < (2 : ℝ) ^ D := by positivity
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hAc hM)
  change 2 * ∑ x ∈ A, w x ≤ M
  have hpow : (2 : ℝ) ^ (D + 1) = 2 ^ D * 2 := pow_succ _ _
  nlinarith

omit [DecidableEq α] in
private lemma large_weights_sum_le_bins_aux (S : Finset α) (w : α → ℝ) (D : ℕ)
    (hw : ∀ x ∈ S, 0 ≤ w x) :
    ∑ x ∈ S.filter (fun x ↦ ¬w x * 2 ^ (D + 1) ≤ ∑ y ∈ S, w y), w x ≤
      ∑ k ∈ range (D + 1),
        ∑ x ∈ S.filter (fun x ↦ w x * 2 ^ k ≤ ∑ y ∈ S, w y ∧
          ∑ y ∈ S, w y < w x * 2 ^ (k + 1)), w x := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_le_sum
  intro x hx
  by_cases h : w x * 2 ^ (D + 1) ≤ ∑ y ∈ S, w y
  · simp only [h, not_true_eq_false, if_false]
    exact sum_nonneg fun k _ ↦ by split_ifs <;> first | exact hw x hx | exact le_rfl
  · simp only [h, not_false_eq_true, if_true]
    have hxM : w x ≤ ∑ y ∈ S, w y := single_le_sum hw hx
    have hxpos : 0 < w x := by
      have hM := sum_nonneg hw
      have hp : 0 < (2 : ℝ) ^ (D + 1) := by positivity
      have h := lt_of_not_ge h
      nlinarith
    obtain ⟨k, hk, hbin⟩ := exists_weight_bin_aux hxpos hxM (lt_of_not_ge h)
    calc
      w x = if w x * 2 ^ k ≤ ∑ y ∈ S, w y ∧
          ∑ y ∈ S, w y < w x * 2 ^ (k + 1) then w x else 0 := (if_pos hbin).symm
      _ ≤ _ := single_le_sum (f := fun j ↦ if w x * 2 ^ j ≤ ∑ y ∈ S, w y ∧
        ∑ y ∈ S, w y < w x * 2 ^ (j + 1) then w x else 0)
        (fun j _ ↦ by split_ifs <;> positivity) hk

omit [DecidableEq α] in
/-- A bounded finite family has a comparable-weight subfamily retaining a polynomial fraction. -/
theorem exists_comparable_weight_subset (S : Finset α) (w : α → ℝ) (D : ℕ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hcard : S.card ≤ 2 ^ D) :
    ∃ A ⊆ S, (∑ x ∈ S, w x) ≤ 2 * (D + 1) * ∑ x ∈ A, w x ∧
      (∀ x ∈ A, 0 < w x) ∧ ∀ x ∈ A, ∀ y ∈ A, w x ≤ 2 * w y := by
  let M := ∑ x ∈ S, w x
  let B (k : ℕ) := S.filter (fun x ↦ w x * 2 ^ k ≤ M ∧ M < w x * 2 ^ (k + 1))
  have hs := small_weights_sum_le_aux S w D hw hcard
  have hl := large_weights_sum_le_bins_aux S w D hw
  have hsplit := sum_filter_add_sum_filter_not S
    (fun x ↦ w x * 2 ^ (D + 1) ≤ M) w
  have hsum : ∑ _k ∈ range (D + 1), M / (2 * (D + 1)) ≤
      ∑ k ∈ range (D + 1), ∑ x ∈ B k, w x := by
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hD : (0 : ℝ) < D + 1 := by positivity
    dsimp [B, M] at *
    field_simp
    nlinarith
  obtain ⟨k, hk, hkM⟩ := exists_le_of_sum_le ⟨0, mem_range.2 (by omega)⟩ hsum
  refine ⟨B k, filter_subset _ _, ?_, ?_, ?_⟩
  · have hD : (0 : ℝ) < 2 * (D + 1) := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hD).1 hkM
  · intro x hx
    have hM : 0 ≤ M := sum_nonneg hw
    have h := (mem_filter.1 hx).2.2
    have hp : 0 < (2 : ℝ) ^ (k + 1) := by positivity
    nlinarith
  · intro x hx y hy
    have hx' := (mem_filter.1 hx).2.1
    have hy' := (mem_filter.1 hy).2.2
    have hp : 0 < (2 : ℝ) ^ k := by positivity
    rw [pow_succ] at hy'
    nlinarith

omit [DecidableEq α] in
private lemma comparable_weights_ratio_aux (A : Finset α) (w : α → ℝ) (D : ℕ)
    (hcard : A.card ≤ 2 ^ D) (hpos : ∀ x ∈ A, 0 < w x)
    (hcomp : ∀ x ∈ A, ∀ y ∈ A, w x ≤ 2 * w y) :
    ∃ k ≤ D, ∀ x ∈ A,
      2 ^ k * w x ≤ 2 * ∑ y ∈ A, w y ∧
      (∑ y ∈ A, w y) ≤ 4 * 2 ^ k * w x := by
  by_cases hA : A.Nonempty
  · have hAc : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
    obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hAc (show (1 : ℝ) < 2 by norm_num)
    have hkD : k ≤ D := by
      have hAcD : (A.card : ℝ) ≤ (2 : ℝ) ^ D := by exact_mod_cast hcard
      exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 (hk.trans hAcD)
    refine ⟨k, hkD, fun x hx ↦ ⟨?_, ?_⟩⟩
    · have hs : (A.card : ℝ) * w x ≤ 2 * ∑ y ∈ A, w y := by
        simpa only [sum_const, nsmul_eq_mul, ← mul_sum] using
          (sum_le_sum fun y hy ↦ hcomp x hx y hy)
      exact (mul_le_mul_of_nonneg_right hk (hpos x hx).le).trans hs
    · have hs : (∑ y ∈ A, w y) ≤ A.card * (2 * w x) := by
        simpa only [sum_const, nsmul_eq_mul] using
          (sum_le_sum fun y hy ↦ hcomp y hy x hx)
      have h := mul_le_mul_of_nonneg_right hk'.le
        (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (hpos x hx).le)
      rw [pow_succ] at h
      nlinarith
  · exact ⟨0, Nat.zero_le D, fun x hx ↦ (hA ⟨x, hx⟩).elim⟩

omit [DecidableEq α] in
/-- One node can be pruned to weights with a common dyadic child-mass exponent. -/
theorem exists_regular_weight_subset (S : Finset α) (w : α → ℝ) (D : ℕ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hcard : S.card ≤ 2 ^ D) :
    ∃ A ⊆ S, ∃ k ≤ D,
      (∑ x ∈ S, w x) ≤ 2 * (D + 1) * ∑ x ∈ A, w x ∧
      (∀ x ∈ A, 0 < w x) ∧ ∀ x ∈ A,
        2 ^ k * w x ≤ 2 * ∑ y ∈ A, w y ∧
        (∑ y ∈ A, w y) ≤ 4 * 2 ^ k * w x := by
  obtain ⟨A, hAS, hmass, hpos, hcomp⟩ := exists_comparable_weight_subset S w D hw hcard
  obtain ⟨k, hk, hratio⟩ := comparable_weights_ratio_aux A w D
    ((card_le_card hAS).trans hcard) hpos hcomp
  exact ⟨A, hAS, k, hk, hmass, hpos, hratio⟩

private lemma selected_fiber_eq_aux (S : Finset α) (p : α → β) (A : β → Finset α)
    (c : β → ℕ) (k : ℕ) (hA : ∀ y, A y ⊆ S.filter (fun x ↦ p x = y)) (y : β) :
    (S.filter (fun x ↦ x ∈ A (p x) ∧ c (p x) = k)).filter (fun x ↦ p x = y) =
      if c y = k then A y else ∅ := by
  ext x
  by_cases hc : c y = k
  · simp only [mem_filter, hc, if_true]
    constructor
    · rintro ⟨⟨hxS, hxA, hxc⟩, hxy⟩
      simpa only [hxy] using hxA
    · intro hxA
      obtain ⟨hxS, hxy⟩ := mem_filter.1 (hA y hxA)
      exact ⟨⟨hxS, by simpa only [hxy] using hxA, by simpa only [hxy]⟩, hxy⟩
  · simp only [mem_filter, hc, if_false, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hxS, hxA, hxc⟩, hxy⟩
    exact hc (hxy ▸ hxc)

private lemma selected_fiber_sum_aux (S : Finset α) (p : α → β) (A : β → Finset α)
    (c : β → ℕ) (k : ℕ) (hA : ∀ y, A y ⊆ S.filter (fun x ↦ p x = y)) (w : α → ℝ) :
    ∑ x ∈ S.filter (fun x ↦ x ∈ A (p x) ∧ c (p x) = k), w x =
      ∑ y ∈ (S.image p).filter (fun y ↦ c y = k), ∑ x ∈ A y, w x := by
  rw [← sum_fiberwise_of_maps_to (t := S.image p) (g := p)
    (fun x hx ↦ mem_image_of_mem p (mem_filter.1 hx).1) w]
  simp only [selected_fiber_eq_aux S p A c k hA, sum_filter]
  apply sum_congr rfl
  intro y hy
  split_ifs <;> simp

/-- All parents can be pruned simultaneously with one common exponent and polynomial mass loss. -/
theorem exists_regular_fiber_subset (S : Finset α) (p : α → β) (w : α → ℝ) (D : ℕ)
    (hw : ∀ x ∈ S, 0 ≤ w x)
    (hcard : ∀ y, (S.filter (fun x ↦ p x = y)).card ≤ 2 ^ D) :
    ∃ A ⊆ S, ∃ k ≤ D,
      (∑ x ∈ S, w x) ≤ (2 * (D + 1) ^ 2) * ∑ x ∈ A, w x ∧
      (∀ x ∈ A, 0 < w x) ∧ ∀ x ∈ A,
        2 ^ k * w x ≤ 2 * ∑ y ∈ A.filter (fun y ↦ p y = p x), w y ∧
        (∑ y ∈ A.filter (fun y ↦ p y = p x), w y) ≤ 4 * 2 ^ k * w x := by
  choose A hA c hc hmass hpos hratio using fun y ↦
    exists_regular_weight_subset (S.filter (fun x ↦ p x = y)) w D
      (fun x hx ↦ hw x (mem_filter.1 hx).1) (hcard y)
  let R := ∑ y ∈ S.image p, ∑ x ∈ A y, w x
  have hR : (∑ x ∈ S, w x) ≤ 2 * (D + 1) * R := by
    rw [← sum_fiberwise_of_maps_to (fun x hx ↦ mem_image_of_mem p hx) w, mul_sum]
    exact sum_le_sum fun y _ ↦ hmass y
  have hD : (0 : ℝ) < D + 1 := by positivity
  obtain ⟨k, hk, hksum⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s := S.image p) (t := range (D + 1)) (f := c) (w := fun y ↦ ∑ x ∈ A y, w x)
    (b := R / (D + 1)) (fun y _ ↦ mem_range.2 (by have := hc y; omega))
    ⟨0, mem_range.2 (by omega)⟩ (by simp [R, hD.ne', mul_div_cancel₀])
  let B := S.filter (fun x ↦ x ∈ A (p x) ∧ c (p x) = k)
  have hBsum := selected_fiber_sum_aux S p A c k hA w
  have hRB : R ≤ (D + 1) * ∑ x ∈ B, w x := by
    rw [← hBsum] at hksum
    simpa only [mul_comm] using (div_le_iff₀ hD).1 hksum
  refine ⟨B, filter_subset _ _, k, by simpa using Nat.le_of_lt_succ (mem_range.1 hk),
    ?_, ?_, ?_⟩
  · calc
      (∑ x ∈ S, w x) ≤ 2 * (D + 1) * R := hR
      _ ≤ 2 * (D + 1) * ((D + 1) * ∑ x ∈ B, w x) :=
        mul_le_mul_of_nonneg_left hRB (by positivity)
      _ = _ := by ring
  · intro x hx
    exact hpos (p x) x (mem_filter.1 hx).2.1
  · intro x hx
    obtain ⟨hxA, hxc⟩ := (mem_filter.1 hx).2
    have hf : B.filter (fun y ↦ p y = p x) = A (p x) := by
      simpa only [hxc, if_true] using selected_fiber_eq_aux S p A c k hA (p x)
    rw [hf, ← hxc]
    exact hratio (p x) x hxA

/-- The mass at height `j` above a finite family of leaves. -/
def finiteTreeMass (S : Finset α) (w : α → ℝ) (p : α → α) (j : ℕ) (q : α) : ℝ :=
  ∑ x ∈ S.filter (fun x ↦ p^[j] x = q), w x

/-- Uniform factor-eight child-mass estimates, with one dyadic exponent at each height. -/
def FiniteTreeRegular (S : Finset α) (w : α → ℝ) (p : α → α) (L : ℕ)
    (k : ℕ → ℕ) : Prop :=
  ∀ j < L, ∀ x ∈ S,
    2 ^ (k j) * finiteTreeMass S w p j (p^[j] x) ≤
      2 * finiteTreeMass S w p (j + 1) (p^[j + 1] x) ∧
    finiteTreeMass S w p (j + 1) (p^[j + 1] x) ≤
      4 * 2 ^ (k j) * finiteTreeMass S w p j (p^[j] x)

private lemma tree_mass_zero_aux (S : Finset α) (w : α → ℝ) (p : α → α) (x : α)
    (hx : x ∈ S) : finiteTreeMass S w p 0 x = w x := by
  change (∑ y ∈ S.filter (fun y ↦ y = x), w y) = w x
  rw [filter_eq', if_pos hx, sum_singleton]

private lemma tree_mass_restrict_parent_aux (S A : Finset α) (w : α → ℝ) (p : α → α)
    (j : ℕ) (q : α) :
    finiteTreeMass (S.filter (fun x ↦ p x ∈ A)) w p (j + 1) q =
      finiteTreeMass A (finiteTreeMass S w p 1) p j q := by
  change (∑ x ∈ (S.filter (fun x ↦ p x ∈ A)).filter (fun x ↦ p^[j] (p x) = q), w x) =
    ∑ y ∈ A.filter (fun y ↦ p^[j] y = q), ∑ x ∈ S.filter (fun x ↦ p x = y), w x
  rw [← sum_fiberwise_of_maps_to (t := A.filter (fun x ↦ p^[j] x = q)) (g := p)
    (fun x hx ↦ mem_filter.2 ⟨(mem_filter.1 (mem_filter.1 hx).1).2,
      (mem_filter.1 hx).2⟩) w]
  apply sum_congr rfl
  intro y hy
  congr 1
  ext x
  obtain ⟨hyA, hyq⟩ := mem_filter.1 hy
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨⟨hxS, hxA⟩, hxq⟩, hxy⟩
    exact ⟨hxS, hxy⟩
  · rintro ⟨hxS, hxy⟩
    exact ⟨⟨⟨hxS, hxy ▸ hyA⟩, hxy ▸ hyq⟩, hxy⟩

private lemma tree_mass_first_restrict_aux (S A : Finset α) (w : α → ℝ) (p : α → α)
    (x : α) (hx : p x ∈ A) :
    finiteTreeMass (S.filter (fun x ↦ p x ∈ A)) w p 1 (p x) =
      finiteTreeMass S w p 1 (p x) := by
  unfold finiteTreeMass
  congr 1
  ext y
  simp only [mem_filter, Function.iterate_one]
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · exact fun h ↦ ⟨⟨h.1, h.2 ▸ hx⟩, h.2⟩

private lemma tree_branching_parent_aux (S B : Finset α) (p : α → α) (D L : ℕ)
    (hBS : B ⊆ S)
    (hcard : ∀ j < L + 1, ∀ y,
      ((S.image (p^[j])).filter (fun x ↦ p x = y)).card ≤ 2 ^ D) :
    ∀ j < L, ∀ y,
      (((B.image p).image (p^[j])).filter (fun x ↦ p x = y)).card ≤ 2 ^ D := by
  intro j hj y
  apply (card_le_card (filter_subset_filter _ ?_)).trans (hcard (j + 1) (by omega) y)
  rw [image_image]
  simpa only [Function.iterate_succ, Function.comp_def] using
    (image_subset_image (f := p^[j + 1]) hBS)

/-- A finite bounded-branching tree has a regular leaf restriction of controlled mass. -/
theorem exists_regular_tree_subset (S : Finset α) (w : α → ℝ) (p : α → α) (D L : ℕ)
    (hw : ∀ x ∈ S, 0 ≤ w x)
    (hcard : ∀ j < L, ∀ y,
      ((S.image (p^[j])).filter (fun x ↦ p x = y)).card ≤ 2 ^ D) :
    ∃ A ⊆ S, ∃ k : ℕ → ℕ, (∀ j < L, k j ≤ D) ∧
      (∑ x ∈ S, w x) ≤ (2 * (D + 1) ^ 2) ^ L * ∑ x ∈ A, w x ∧
      FiniteTreeRegular A w p L k := by
  induction L generalizing S w with
  | zero => exact ⟨S, Subset.rfl, fun _ ↦ 0, by simp, by simp, by simp [FiniteTreeRegular]⟩
  | succ L ih =>
    obtain ⟨B, hBS, k₀, hk₀, hBmass, hBpos, hBreg⟩ :=
      exists_regular_fiber_subset S p w D hw
        (by simpa only [Function.iterate_zero, image_id] using hcard 0 (by omega))
    let v := finiteTreeMass B w p 1
    have hv : ∀ y ∈ B.image p, 0 ≤ v y := fun y _ ↦
      sum_nonneg fun x hx ↦ hw x (hBS (mem_filter.1 hx).1)
    obtain ⟨A, hAB, k, hk, hmass, hreg⟩ := ih (B.image p) v hv
      (tree_branching_parent_aux S B p D L hBS hcard)
    let C := B.filter (fun x ↦ p x ∈ A)
    have hCmass : (∑ y ∈ A, v y) = ∑ x ∈ C, w x := by
      rw [← sum_fiberwise_eq_sum_filter B A p w]
      rfl
    have hBsum : (∑ y ∈ B.image p, v y) = ∑ x ∈ B, w x :=
      sum_fiberwise_of_maps_to (fun x hx ↦ mem_image_of_mem p hx) w
    refine ⟨C, (filter_subset _ _).trans hBS, (fun j ↦ if j = 0 then k₀ else k (j - 1)),
      ?_, ?_, ?_⟩
    · intro j hj
      by_cases hj₀ : j = 0
      · simpa only [hj₀, ite_true] using hk₀
      · simpa only [hj₀, if_false] using hk (j - 1) (by omega)
    · rw [hBsum, hCmass] at hmass
      calc
        (∑ x ∈ S, w x) ≤ 2 * (D + 1) ^ 2 * ∑ x ∈ B, w x := hBmass
        _ ≤ 2 * (D + 1) ^ 2 * ((2 * (D + 1) ^ 2) ^ L * ∑ x ∈ C, w x) :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
        _ = _ := by ring
    · intro j hj x hx
      obtain ⟨hxB, hxA⟩ := mem_filter.1 hx
      cases j with
      | zero =>
        simp only [ite_true, Function.iterate_zero_apply, zero_add, Function.iterate_one]
        rw [tree_mass_zero_aux C w p x hx, tree_mass_first_restrict_aux B A w p x hxA]
        exact hBreg x hxB
      | succ j =>
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [tree_mass_restrict_parent_aux, tree_mass_restrict_parent_aux]
        simpa only [Function.iterate_succ_apply] using hreg j (by omega) (p x) hxA

private lemma exists_disjoint_extraction_aux (S : Finset α) (w : α → ℝ)
    (R : Finset α → Prop) {C δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ x ∈ S, 0 ≤ w x)
    (hextract : ∀ U ⊆ S, ∃ A ⊆ U, R A ∧ (∑ x ∈ U, w x) ≤ C * ∑ x ∈ A, w x) :
    ∃ F : Finset (Finset α), (↑F : Set (Finset α)).PairwiseDisjoint id ∧
      (∀ A ∈ F, A ⊆ S ∧ R A ∧ δ ≤ C * ∑ x ∈ A, w x) ∧
      (∑ x ∈ S, w x) ≤ δ + ∑ A ∈ F, ∑ x ∈ A, w x := by
  classical
  revert hw hextract
  induction S using Finset.strongInductionOn
  rename_i S ih
  intro hw hextract
  by_cases hsmall : (∑ x ∈ S, w x) ≤ δ
  · exact ⟨∅, by simp, by simp, by simpa using hsmall⟩
  obtain ⟨A, hAS, hAR, hmass⟩ := hextract S Subset.rfl
  have hA : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty, mul_zero] at hmass
    exact hsmall (hmass.trans hδ.le)
  obtain ⟨F, hFd, hF, hFm⟩ := ih (S \ A) (sdiff_ssubset hAS hA)
    (fun x hx ↦ hw x (mem_sdiff.1 hx).1)
    (fun U hU ↦ hextract U (hU.trans sdiff_subset))
  have hAF : A ∉ F := by
    intro hAF
    obtain ⟨x, hx⟩ := hA
    exact (mem_sdiff.1 ((hF A hAF).1 hx)).2 hx
  refine ⟨insert A F, ?_, ?_, ?_⟩
  · intro B hB E hE hBE
    simp only [mem_coe, mem_insert] at hB hE
    rcases hB with rfl | hB <;> rcases hE with rfl | hE
    · exact (hBE rfl).elim
    · exact disjoint_left.2 fun x hxA hxE ↦ (mem_sdiff.1 ((hF E hE).1 hxE)).2 hxA
    · exact disjoint_left.2 fun x hxB hxA ↦ (mem_sdiff.1 ((hF B hB).1 hxB)).2 hxA
    · exact hFd hB hE hBE
  · intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · exact ⟨hAS, hAR, (lt_of_not_ge hsmall).le.trans hmass⟩
    · exact ⟨(hF B hB).1.trans sdiff_subset, (hF B hB).2⟩
  · rw [sum_insert hAF]
    have hsum := sum_sdiff (f := w) hAS
    linarith

private lemma disjoint_extraction_mass_aux (S : Finset α) (w : α → ℝ)
    (F : Finset (Finset α)) (hFd : (↑F : Set (Finset α)).PairwiseDisjoint id)
    (hF : ∀ A ∈ F, A ⊆ S) (hw : ∀ x ∈ S, 0 ≤ w x) :
    (∑ A ∈ F, ∑ x ∈ A, w x) ≤ ∑ x ∈ S, w x := by
  rw [← show (∑ x ∈ F.biUnion id, w x) = ∑ A ∈ F, ∑ x ∈ A, w x from
    sum_biUnion hFd]
  exact sum_le_sum_of_subset_of_nonneg
    (by intro x hx; obtain ⟨A, hAF, hxA⟩ := mem_biUnion.1 hx; exact hF A hAF hxA)
    (fun x hx _ ↦ hw x hx)

/-- Finite regular components cover all but the requested mass, with quantitative component size. -/
theorem exists_regular_tree_partition (S : Finset α) (w : α → ℝ) (p : α → α) (D L : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hw : ∀ x ∈ S, 0 ≤ w x)
    (hcard : ∀ j < L, ∀ y,
      ((S.image (p^[j])).filter (fun x ↦ p x = y)).card ≤ 2 ^ D) :
    ∃ F : Finset (Finset α), (↑F : Set (Finset α)).PairwiseDisjoint id ∧
      (∀ A ∈ F, A ⊆ S ∧ δ ≤ (2 * (D + 1) ^ 2) ^ L * ∑ x ∈ A, w x ∧
        ∃ k : ℕ → ℕ, (∀ j < L, k j ≤ D) ∧ FiniteTreeRegular A w p L k) ∧
      (∑ x ∈ S \ F.biUnion id, w x) ≤ δ ∧
      (F.card : ℝ) * δ ≤ (2 * (D + 1) ^ 2) ^ L * ∑ x ∈ S, w x := by
  classical
  let C : ℝ := (2 * (D + 1) ^ 2) ^ L
  let R (A : Finset α) := ∃ k : ℕ → ℕ, (∀ j < L, k j ≤ D) ∧
    FiniteTreeRegular A w p L k
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨F, hFd, hF, hFm⟩ := exists_disjoint_extraction_aux S w R hδ hw (by
    intro U hUS
    obtain ⟨A, hAU, k, hk, hm, hr⟩ := exists_regular_tree_subset U w p D L
      (fun x hx ↦ hw x (hUS hx)) (fun j hj y ↦
        (card_le_card (filter_subset_filter _ (image_subset_image hUS))).trans (hcard j hj y))
    exact ⟨A, hAU, ⟨k, hk, hr⟩, hm⟩)
  have hFU : F.biUnion id ⊆ S := by
    intro x hx
    obtain ⟨A, hAF, hxA⟩ := mem_biUnion.1 hx
    exact (hF A hAF).1 hxA
  have hbound := disjoint_extraction_mass_aux S w F hFd (fun A hA ↦ (hF A hA).1) hw
  refine ⟨F, hFd, (fun A hA ↦ ⟨(hF A hA).1, (hF A hA).2.2, (hF A hA).2.1⟩), ?_, ?_⟩
  · have hsum := sum_sdiff (f := w) hFU
    rw [sum_biUnion hFd] at hsum
    simp only [id_eq] at hsum
    linarith
  · have hsum : (F.card : ℝ) * δ ≤ C * ∑ A ∈ F, ∑ x ∈ A, w x := by
      simpa only [sum_const, nsmul_eq_mul, mul_sum] using
        (sum_le_sum fun A hA ↦ (hF A hA).2.2)
    exact hsum.trans (mul_le_mul_of_nonneg_left hbound hC.le)

/-- A block parent has at most `2^(2*T)` planar dyadic children. -/
theorem card_filter_ancestor_le (S : Finset (Fin 2 → ℤ)) (T : ℕ) (q : Fin 2 → ℤ) :
    (S.filter (fun k ↦ ancestor T k = q)).card ≤ 2 ^ (2 * T) := by
  let r (k : Fin 2 → ℤ) : Fin 2 → Fin (2 ^ T) := fun i ↦
    ⟨(k i % (2 : ℤ) ^ T).toNat, (Int.toNat_lt
      (Int.emod_nonneg _ (by positivity))).2 (by
        exact_mod_cast Int.emod_lt_of_pos (k i) (show 0 < (2 : ℤ) ^ T by positivity))⟩
  have hinj : Set.InjOn r (↑(S.filter (fun k ↦ ancestor T k = q))) := by
    intro x hx y hy hxy
    funext i
    apply Int.ext_ediv_emod
    · exact (congrFun (mem_filter.1 hx).2 i).trans (congrFun (mem_filter.1 hy).2 i).symm
    · have h := congrArg (fun f ↦ (f i).val) hxy
      have hx₀ := Int.emod_nonneg (x i) (show (2 : ℤ) ^ T ≠ 0 by positivity)
      have hy₀ := Int.emod_nonneg (y i) (show (2 : ℤ) ^ T ≠ 0 by positivity)
      dsimp [r] at h
      simpa only [Int.toNat_of_nonneg hx₀, Int.toNat_of_nonneg hy₀] using
        congrArg (fun n : ℕ ↦ (n : ℤ)) h
  have h := card_le_card_of_injOn (t := univ) r (fun _ _ ↦ mem_univ _) hinj
  simpa only [card_univ, Fintype.card_fun, Fintype.card_fin, ← pow_mul, Nat.mul_comm T 2]
    using h

private lemma ancestor_iterate_aux (T j : ℕ) : (ancestor T)^[j] = ancestor (T * j) := by
  funext x
  induction j with
  | zero => simp [ancestor_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, ancestor_ancestor, Nat.mul_succ]
    congr 1
    omega

/-- Regularization for actual weights on a finite family of terminal dyadic squares. -/
theorem exists_regular_dyadic_weight_partition (S : Finset (Fin 2 → ℤ))
    (w : (Fin 2 → ℤ) → ℝ) (T L : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ k ∈ S, 0 ≤ w k) :
    ∃ F : Finset (Finset (Fin 2 → ℤ)),
      (↑F : Set (Finset (Fin 2 → ℤ))).PairwiseDisjoint id ∧
      (∀ A ∈ F, A ⊆ S ∧ δ ≤ (2 * (2 * T + 1) ^ 2) ^ L * ∑ k ∈ A, w k ∧
        ∃ e : ℕ → ℕ, (∀ j < L, e j ≤ 2 * T) ∧
          FiniteTreeRegular A w (ancestor T) L e) ∧
      (∑ k ∈ S \ F.biUnion id, w k) ≤ δ ∧
      (F.card : ℝ) * δ ≤ (2 * (2 * T + 1) ^ 2) ^ L * ∑ k ∈ S, w k := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    exists_regular_tree_partition S w (ancestor T) (2 * T) L hδ hw
      (fun _ _ q ↦ card_filter_ancestor_le _ T q)

/-- The union of a finite family of dyadic squares at one fixed depth. -/
def finiteDyadicUnion (n : ℕ) (S : Finset (Fin 2 → ℤ)) :
    Set (EuclideanSpace ℝ (Fin 2)) := ⋃ k ∈ S, dyadicCube n k

theorem mem_finiteDyadicUnion_iff {n : ℕ} {S : Finset (Fin 2 → ℤ)}
    {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ finiteDyadicUnion n S ↔ cubeIndex n x ∈ S := by
  simp only [finiteDyadicUnion, Set.mem_iUnion, mem_dyadicCube_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact h ▸ hk
  · exact fun h ↦ ⟨cubeIndex n x, h, rfl⟩

theorem measurableSet_finiteDyadicUnion (n : ℕ) (S : Finset (Fin 2 → ℤ)) :
    MeasurableSet (finiteDyadicUnion n S) :=
  MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_dyadicCube n k

theorem finiteDyadicUnion_disjoint {n : ℕ} {A B : Finset (Fin 2 → ℤ)}
    (h : Disjoint A B) : Disjoint (finiteDyadicUnion n A) (finiteDyadicUnion n B) := by
  exact Set.disjoint_left.2 fun x hx hy ↦ Finset.disjoint_left.1 h
    (mem_finiteDyadicUnion_iff.1 hx) (mem_finiteDyadicUnion_iff.1 hy)

theorem finiteDyadicUnion_sdiff (n : ℕ) (A B : Finset (Fin 2 → ℤ)) :
    finiteDyadicUnion n (A \ B) = finiteDyadicUnion n A \ finiteDyadicUnion n B := by
  ext x
  simp [mem_finiteDyadicUnion_iff]

theorem measureReal_finiteDyadicUnion
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (n : ℕ) (S : Finset (Fin 2 → ℤ)) :
    μ.real (finiteDyadicUnion n S) = ∑ k ∈ S, μ.real (dyadicCube n k) := by
  rw [measureReal_def, finiteDyadicUnion,
    measure_biUnion_finset (fun _ _ _ _ h ↦ dyadicCube_disjoint h)
      (fun k _ ↦ measurableSet_dyadicCube n k),
    ENNReal.toReal_sum (fun k _ ↦ measure_ne_top μ _)]
  rfl

private lemma finiteDyadicUnion_filter_ancestor_aux (m h : ℕ)
    (A : Finset (Fin 2 → ℤ)) (q : Fin 2 → ℤ) :
    finiteDyadicUnion (m + h) (A.filter (fun k ↦ ancestor h k = q)) =
      finiteDyadicUnion (m + h) A ∩ dyadicCube m q := by
  ext x
  have hx : x ∈ dyadicCube m (ancestor h (cubeIndex (m + h) x)) :=
    dyadicCube_subset_ancestor m h _ (mem_dyadicCube_cubeIndex (m + h) x)
  have hi := mem_dyadicCube_iff.1 hx
  simp only [Set.mem_inter_iff, mem_finiteDyadicUnion_iff, mem_filter,
    mem_dyadicCube_iff, hi]

/-- Finite tree masses equal the original measure of a component intersected with a coarser cube. -/
theorem finiteTreeMass_dyadic_eq (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ] (n T j : ℕ) (hj : T * j ≤ n)
    (A : Finset (Fin 2 → ℤ)) (q : Fin 2 → ℤ) :
    finiteTreeMass A (fun k ↦ μ.real (dyadicCube n k)) (ancestor T) j q =
      μ.real (finiteDyadicUnion n A ∩ dyadicCube (n - T * j) q) := by
  rw [finiteTreeMass, ancestor_iterate_aux, ← measureReal_finiteDyadicUnion]
  have hn : n - T * j + T * j = n := Nat.sub_add_cancel hj
  rw [← hn, finiteDyadicUnion_filter_ancestor_aux]
  simp only [hn]

/-- The original measure itself admits the finite dyadic regular decomposition. -/
theorem exists_regular_dyadic_measure_partition
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (S : Finset (Fin 2 → ℤ)) (T L : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Finset (Finset (Fin 2 → ℤ)),
      (↑F : Set (Finset (Fin 2 → ℤ))).PairwiseDisjoint (finiteDyadicUnion (T * L)) ∧
      (∀ A ∈ F, A ⊆ S ∧
        δ ≤ (2 * (2 * T + 1) ^ 2) ^ L * μ.real (finiteDyadicUnion (T * L) A) ∧
        ∃ e : ℕ → ℕ, (∀ j < L, e j ≤ 2 * T) ∧
          FiniteTreeRegular A (fun k ↦ μ.real (dyadicCube (T * L) k)) (ancestor T) L e) ∧
      μ.real (finiteDyadicUnion (T * L) S \ finiteDyadicUnion (T * L) (F.biUnion id)) ≤ δ ∧
      (F.card : ℝ) * δ ≤
        (2 * (2 * T + 1) ^ 2) ^ L * μ.real (finiteDyadicUnion (T * L) S) := by
  obtain ⟨F, hFd, hF, hrem, hcard⟩ := exists_regular_dyadic_weight_partition S
    (fun k ↦ μ.real (dyadicCube (T * L) k)) T L hδ
    (fun _ _ ↦ measureReal_nonneg)
  refine ⟨F, (fun _ hA _ hB hAB ↦ finiteDyadicUnion_disjoint (hFd hA hB hAB)),
    ?_, ?_, ?_⟩
  · simpa only [measureReal_finiteDyadicUnion] using hF
  · simpa only [← finiteDyadicUnion_sdiff, measureReal_finiteDyadicUnion] using hrem
  · simpa only [measureReal_finiteDyadicUnion] using hcard

private lemma tree_mass_normalizedRestrict_aux
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (A : Finset (Fin 2 → ℤ)) (p : (Fin 2 → ℤ) → (Fin 2 → ℤ)) (j : ℕ) (q : Fin 2 → ℤ) :
    finiteTreeMass A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion n A)).real (dyadicCube n k)) p j q =
      (μ.real (finiteDyadicUnion n A))⁻¹ *
        finiteTreeMass A (fun k ↦ μ.real (dyadicCube n k)) p j q := by
  unfold finiteTreeMass
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hsub : dyadicCube n k ⊆ finiteDyadicUnion n A := by
    intro x hx
    apply mem_finiteDyadicUnion_iff.2
    rw [mem_dyadicCube_iff.1 hx]
    exact (mem_filter.1 hk).1
  simp only [measureReal_def, normalizedRestrict_apply _ _ _ (measurableSet_dyadicCube n k),
    Set.inter_eq_left.2 hsub, ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- The regularity estimates survive normalization of the original component measure. -/
theorem FiniteTreeRegular.normalizedRestrict
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {n T L : ℕ} {A : Finset (Fin 2 → ℤ)}
    {e : ℕ → ℕ}
    (h : FiniteTreeRegular A (fun k ↦ μ.real (dyadicCube n k)) (ancestor T) L e) :
    FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion n A)).real (dyadicCube n k))
      (ancestor T) L e := by
  intro j hj x hx
  rw [tree_mass_normalizedRestrict_aux, tree_mass_normalizedRestrict_aux]
  have hc : 0 ≤ (μ.real (finiteDyadicUnion n A))⁻¹ := inv_nonneg.2 measureReal_nonneg
  obtain ⟨h₁, h₂⟩ := h j hj x hx
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h₁ hc]
  · nlinarith [mul_le_mul_of_nonneg_left h₂ hc]

/-- The regular dyadic components can be retained as normalized original probability measures. -/
theorem exists_normalized_regular_dyadic_measure_partition
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (S : Finset (Fin 2 → ℤ)) (T L : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : Finset (Finset (Fin 2 → ℤ)),
      (↑F : Set (Finset (Fin 2 → ℤ))).PairwiseDisjoint (finiteDyadicUnion (T * L)) ∧
      (∀ A ∈ F, A ⊆ S ∧
        δ ≤ (2 * (2 * T + 1) ^ 2) ^ L * μ.real (finiteDyadicUnion (T * L) A) ∧
        IsProbabilityMeasure (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) ∧
        ∃ e : ℕ → ℕ, (∀ j < L, e j ≤ 2 * T) ∧
          FiniteTreeRegular A
            (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
              (dyadicCube (T * L) k)) (ancestor T) L e) ∧
      μ.real (finiteDyadicUnion (T * L) S \ finiteDyadicUnion (T * L) (F.biUnion id)) ≤ δ ∧
      (F.card : ℝ) * δ ≤
        (2 * (2 * T + 1) ^ 2) ^ L * μ.real (finiteDyadicUnion (T * L) S) := by
  obtain ⟨F, hFd, hF, hrem, hcard⟩ :=
    exists_regular_dyadic_measure_partition μ S T L hδ
  refine ⟨F, hFd, ?_, hrem, hcard⟩
  intro A hA
  obtain ⟨hAS, hmass, e, he, hreg⟩ := hF A hA
  have hpos : 0 < μ.real (finiteDyadicUnion (T * L) A) := by
    have hC : (0 : ℝ) < (2 * (2 * T + 1) ^ 2) ^ L := by positivity
    nlinarith
  exact ⟨hAS, hmass,
    isProbabilityMeasure_normalizedRestrict (measurableSet_finiteDyadicUnion _ _)
      (ENNReal.toReal_pos_iff.1 hpos).1.ne' (measure_ne_top μ _),
    e, he, hreg.normalizedRestrict⟩

end FalconerPacking
