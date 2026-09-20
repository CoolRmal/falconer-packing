/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Content

/-!
# The Frostman normalization on a finite dyadic tree

Frostman's lemma is built from a finite construction: put mass `2⁻ⁿᵈ` on each occupied cube of
generation `n`, then walk up the tree, and at each generation scale the weights inside a cube
down whenever its mass exceeds the allowance `2⁻ʲᵈ`.

This file carries out that walk on weights supported on a finite set of generation-`n` indices,
and proves the half that the construction is designed for: the resulting weights obey the dyadic
Frostman bound at *every* generation `j ≤ n`.  Weights only decrease along the walk, so a bound
established at one generation survives all later steps.

The complementary half — that the total mass stays comparable to the dyadic content of the set —
is the saturated-cube argument, and is not proved here.
-/

noncomputable section

open Finset

namespace FalconerPacking

variable (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : ℝ)

/-- The allowance of a generation-`j` cube: `2⁻ʲᵈ`. -/
def allowance (j : ℕ) (d : ℝ) : ℝ := (2 : ℝ) ^ (-(j : ℝ) * d)

theorem allowance_pos (j : ℕ) (d : ℝ) : 0 < allowance j d :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The mass of the generation-`j` cube with index `k`, for weights carried by generation-`n`
cubes. -/
def cubeMass (S : Finset (Fin 2 → ℤ)) (n j : ℕ) (w : (Fin 2 → ℤ) → ℝ) (k : Fin 2 → ℤ) : ℝ :=
  ∑ k' ∈ S.filter fun k' ↦ ancestor (n - j) k' = k, w k'

theorem cubeMass_nonneg {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ) (k : Fin 2 → ℤ) :
    0 ≤ cubeMass S n j w k :=
  Finset.sum_nonneg fun k' _ ↦ hw k'

theorem cubeMass_mono {w w' : (Fin 2 → ℤ) → ℝ} (h : ∀ k, w k ≤ w' k) (j : ℕ) (k : Fin 2 → ℤ) :
    cubeMass S n j w k ≤ cubeMass S n j w' k :=
  Finset.sum_le_sum fun k' _ ↦ h k'

/-- One normalization step at generation `j`: scale each weight by the factor attached to its
generation-`j` ancestor, so that the cube's mass falls to its allowance. -/
def normalizeStep (S : Finset (Fin 2 → ℤ)) (n j : ℕ) (d : ℝ) (w : (Fin 2 → ℤ) → ℝ) :
    (Fin 2 → ℤ) → ℝ := fun k' ↦
  if cubeMass S n j w (ancestor (n - j) k') ≤ allowance j d then w k'
  else w k' * (allowance j d / cubeMass S n j w (ancestor (n - j) k'))

theorem normalizeStep_nonneg {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ)
    (k' : Fin 2 → ℤ) : 0 ≤ normalizeStep S n j d w k' := by
  rw [normalizeStep]
  split
  · exact hw k'
  · rename_i hcon
    rw [not_le] at hcon
    have hm : 0 < cubeMass S n j w (ancestor (n - j) k') := (allowance_pos j d).trans hcon
    exact mul_nonneg (hw k') (div_nonneg (allowance_pos j d).le hm.le)

/-- The step never increases a weight. -/
theorem normalizeStep_le {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ) (k' : Fin 2 → ℤ) :
    normalizeStep S n j d w k' ≤ w k' := by
  rw [normalizeStep]
  split
  · exact le_rfl
  · rename_i hcon
    rw [not_le] at hcon
    have hm : 0 < cubeMass S n j w (ancestor (n - j) k') := (allowance_pos j d).trans hcon
    refine mul_le_of_le_one_right (hw k') ?_
    rw [div_le_one hm]
    exact hcon.le

/-- **The step enforces the allowance.**  After normalizing at generation `j`, every
generation-`j` cube has mass at most `2⁻ʲᵈ`. -/
theorem cubeMass_normalizeStep_le {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) (j : ℕ)
    (k : Fin 2 → ℤ) :
    cubeMass S n j (normalizeStep S n j d w) k ≤ allowance j d := by
  by_cases hle : cubeMass S n j w k ≤ allowance j d
  · refine le_trans (le_of_eq ?_) hle
    refine Finset.sum_congr rfl fun k' hk' ↦ ?_
    have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
    rw [normalizeStep, hanc, if_pos hle]
  · rw [not_le] at hle
    have hm : 0 < cubeMass S n j w k := (allowance_pos j d).trans hle
    have hsum : cubeMass S n j (normalizeStep S n j d w) k
        = cubeMass S n j w k * (allowance j d / cubeMass S n j w k) := by
      rw [cubeMass, cubeMass, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k' hk' ↦ ?_
      have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
      rw [normalizeStep, hanc, if_neg (not_le.2 hle), cubeMass]
    rw [hsum, mul_div_cancel₀ _ hm.ne']

/-- The normalization walk: process generations `j, j - 1, …, 0` in that order. -/
def normalizeDown (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : ℝ) :
    ℕ → ((Fin 2 → ℤ) → ℝ) → ((Fin 2 → ℤ) → ℝ)
  | 0, w => normalizeStep S n 0 d w
  | (j + 1), w => normalizeDown S n d j (normalizeStep S n (j + 1) d w)

theorem normalizeDown_nonneg :
    ∀ (j : ℕ) {w : (Fin 2 → ℤ) → ℝ}, (∀ k, 0 ≤ w k) → ∀ k, 0 ≤ normalizeDown S n d j w k
  | 0, w, hw => normalizeStep_nonneg S n d hw 0
  | (j + 1), w, hw =>
      normalizeDown_nonneg j (normalizeStep_nonneg S n d hw (j + 1))

/-- The walk never increases a weight. -/
theorem normalizeDown_le :
    ∀ (j : ℕ) {w : (Fin 2 → ℤ) → ℝ}, (∀ k, 0 ≤ w k) → ∀ k, normalizeDown S n d j w k ≤ w k
  | 0, w, hw => normalizeStep_le S n d hw 0
  | (j + 1), w, hw => by
      intro k
      refine le_trans (normalizeDown_le j (normalizeStep_nonneg S n d hw (j + 1)) k) ?_
      exact normalizeStep_le S n d hw (j + 1) k

/-- **The Frostman property of the construction.**  After walking down from generation `j`,
every generation `i ≤ j` obeys its allowance. -/
theorem cubeMass_normalizeDown_le :
    ∀ (j : ℕ) {w : (Fin 2 → ℤ) → ℝ}, (∀ k, 0 ≤ w k) → ∀ i ≤ j, ∀ k,
      cubeMass S n i (normalizeDown S n d j w) k ≤ allowance i d
  | 0, w, hw => by
      intro i hi k
      have hi0 : i = 0 := Nat.le_zero.1 hi
      subst hi0
      exact cubeMass_normalizeStep_le S n d hw 0 k
  | (j + 1), w, hw => by
      intro i hi k
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact cubeMass_normalizeDown_le j (normalizeStep_nonneg S n d hw (j + 1)) i
          (by omega) k
      · have hij : i = j + 1 := by omega
        subst hij
        refine le_trans (cubeMass_mono S n ?_ (j + 1) k)
          (cubeMass_normalizeStep_le S n d hw (j + 1) k)
        intro k'
        exact normalizeDown_le S n d j (normalizeStep_nonneg S n d hw (j + 1)) k'

section Saturation

variable {S n d}

/-- At the finest generation the mass of a cube is just the weight it carries. -/
theorem cubeMass_self (w : (Fin 2 → ℤ) → ℝ) (k : Fin 2 → ℤ) :
    cubeMass S n n w k = if k ∈ S then w k else 0 := by
  classical
  rw [cubeMass, Nat.sub_self]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
    refine Finset.sum_eq_single_of_mem k ?_ ?_
    · exact Finset.mem_filter.2 ⟨hk, by simp⟩
    · intro b hb hbk
      have : ancestor 0 b = k := (Finset.mem_filter.1 hb).2
      rw [ancestor_zero] at this
      exact absurd this hbk
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun b hb ↦ ?_
    have hbS : b ∈ S := (Finset.mem_filter.1 hb).1
    have hbk : ancestor 0 b = k := (Finset.mem_filter.1 hb).2
    rw [ancestor_zero] at hbk
    exact absurd (hbk ▸ hbS) hk

/-- The initial weights of the construction: every occupied cube of generation `n` carries its
own allowance. -/
def initialWeight (n : ℕ) (d : ℝ) : (Fin 2 → ℤ) → ℝ := fun _ ↦ allowance n d

theorem initialWeight_nonneg (n : ℕ) (d : ℝ) (k : Fin 2 → ℤ) : 0 ≤ initialWeight n d k :=
  (allowance_pos n d).le

/-- The initial weights saturate every occupied cube of the finest generation. -/
theorem cubeMass_initialWeight (S : Finset (Fin 2 → ℤ)) (n : ℕ) (d : ℝ) {k : Fin 2 → ℤ}
    (hk : k ∈ S) : cubeMass S n n (initialWeight n d) k = allowance n d := by
  rw [cubeMass_self, if_pos hk, initialWeight]

/-- **The step dichotomy.**  At each generation a cube is either left untouched by the
normalization, or it is saturated: its mass becomes exactly its allowance.  This is what makes
the saturated cubes of the finished walk a cover of the set. -/
theorem normalizeStep_dichotomy (w : (Fin 2 → ℤ) → ℝ) (j : ℕ) (k : Fin 2 → ℤ) :
    (∀ k' ∈ S.filter fun k' ↦ ancestor (n - j) k' = k, normalizeStep S n j d w k' = w k')
      ∨ cubeMass S n j (normalizeStep S n j d w) k = allowance j d := by
  by_cases hle : cubeMass S n j w k ≤ allowance j d
  · refine Or.inl fun k' hk' ↦ ?_
    have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
    rw [normalizeStep, hanc, if_pos hle]
  · refine Or.inr ?_
    rw [not_le] at hle
    have hm : 0 < cubeMass S n j w k := (allowance_pos j d).trans hle
    have hsum : cubeMass S n j (normalizeStep S n j d w) k
        = cubeMass S n j w k * (allowance j d / cubeMass S n j w k) := by
      rw [cubeMass, cubeMass, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k' hk' ↦ ?_
      have hanc : ancestor (n - j) k' = k := (Finset.mem_filter.1 hk').2
      rw [normalizeStep, hanc, if_neg (not_le.2 hle), cubeMass]
    rw [hsum, mul_div_cancel₀ _ hm.ne']

end Saturation

end FalconerPacking
