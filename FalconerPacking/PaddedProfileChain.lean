/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.BlockProfileChainScales

/-!
# Padding every profile chain to one fixed length

Zero-depth edges have zero profile cost and admissible physical scales. Thus the same
fixed length can be used in all packet rectangles and all analytic constants.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- A zero-ended list has zero depth at and after its endpoint. -/
theorem profileChainDepth_eq_zero_of_length_le {n : ℕ} {l : List ℕ}
    (hend : chainEnd n l = 0) {j : ℕ} (hj : l.length ≤ j) :
    profileChainDepth n l j = 0 := by
  rcases eq_or_lt_of_le hj with rfl | hj
  · simpa only [profileChainDepth_length] using hend
  · exact profileChainDepth_of_length_lt n l hj

/-- Padding to the prescribed maximum length preserves the full edge sum exactly. -/
theorem sum_edgeCost_padded_profileChainDepth (g : ℕ → ℝ) {n K : ℕ} {l : List ℕ}
    (hlen : l.length ≤ K) (hend : chainEnd n l = 0) :
    (∑ j ∈ Finset.range K,
      edgeCost g (profileChainDepth n l (j + 1)) (profileChainDepth n l j)) =
        chainCost g n l := by
  rw [← sum_edgeCost_profileChainDepth g n l]
  symm
  apply Finset.sum_subset (Finset.range_mono hlen)
  intro j _ hj
  have hj' : l.length ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  rw [profileChainDepth_eq_zero_of_length_le hend hj',
    profileChainDepth_eq_zero_of_length_le hend (by omega), edgeCost_self]

/-- Every edge, including added zero edges, remains admissible. -/
theorem profileChainDepth_admissible_padded {N n : ℕ} {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l))
    (hend : chainEnd n l = 0) (j : ℕ) :
    Admissible N (profileChainDepth n l (j + 1)) (profileChainDepth n l j) := by
  by_cases hj : j < l.length
  · exact (profileChainDepth_edge hl hj).2
  · rw [profileChainDepth_eq_zero_of_length_le hend (Nat.le_of_not_gt hj),
      profileChainDepth_eq_zero_of_length_le hend (by omega)]
    simp [Admissible]

/-- Padded physical edges have unit side lengths and full auxiliary angular depth. -/
theorem blockProfileChain_padded_scales {F T n : ℕ} {l : List ℕ}
    (hend : chainEnd n l = 0) {j : ℕ} (hj : l.length ≤ j) :
    T * profileChainDepth n l j = 0 ∧ T * profileChainDepth n l (j + 1) = 0 ∧
      blockProfileChainAngle F T n l (j + 1) = F ∧
      ((2 : ℝ) ^ (T * profileChainDepth n l (j + 1)))⁻¹ ≤
        (2 : ℝ) ^ F * (((2 : ℝ) ^ (T * profileChainDepth n l j))⁻¹) ^ 2 := by
  rw [profileChainDepth_eq_zero_of_length_le hend hj,
    profileChainDepth_eq_zero_of_length_le hend (by omega)]
  have he : blockProfileChainAngle F T n l (j + 1) = F := by
    simp only [blockProfileChainAngle, profileChainDepth_eq_zero_of_length_le hend hj,
      Nat.mul_zero, Nat.sub_zero]
  simp only [Nat.mul_zero, he, pow_zero, inv_one, one_pow, mul_one, true_and]
  exact one_le_pow₀ (by norm_num)

/-- All physical inequalities hold at every edge of the zero-padded block chain. -/
theorem blockProfileChain_scales_all_edges {N F T n s : ℕ} {l : List ℕ}
    (hNF : T * N ≤ F) (hn : n ≤ N)
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l))
    (hend : chainEnd n l = 0)
    (hs : Real.sqrt ((2 : ℝ) ^ (T * N)) ≤ (2 : ℝ) ^ s) (j : ℕ) :
    let a := ((2 : ℝ) ^ (T * profileChainDepth n l j))⁻¹
    let b := ((2 : ℝ) ^ (T * profileChainDepth n l (j + 1)))⁻¹
    0 < a ∧ a ≤ b ∧ b ≤ 1 ∧ b ≤ (2 : ℝ) ^ F * a ^ 2 ∧
      (2 : ℝ) ^ blockProfileChainAngle F T n l (j + 1) = (2 : ℝ) ^ F * a ∧
      ((2 : ℝ) ^ s)⁻¹ ≤ a / b := by
  by_cases hj : j < l.length
  · obtain ⟨_, _, _, _, _, _, hedge⟩ := blockProfileChain_scales hNF hn hl hend hs
    exact hedge j hj
  · obtain ⟨h₀, h₁, he, _⟩ := blockProfileChain_padded_scales (F := F) (T := T)
      hend (Nat.le_of_not_gt hj)
    dsimp only
    rw [h₀, h₁, he]
    simp only [pow_zero, inv_one, one_pow, mul_one, div_one]
    exact ⟨zero_lt_one, le_rfl, le_rfl, one_le_pow₀ (by norm_num), trivial,
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))⟩

end FalconerPacking
