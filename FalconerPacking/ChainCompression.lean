/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.UnforcedProfile

/-!
# Compressing admissible scale chains

Removing an intermediate scale whose two adjacent edges can be merged preserves admissibility
and does not increase the profile cost. A compressed chain has a complementary gap that more
than doubles every two steps, giving a length bound independent of the grid resolution.
-/

noncomputable section

namespace FalconerPacking

/-- Greedily remove a middle scale whenever the resulting edge is admissible. -/
def compressChain (N : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | _, [m] => [m]
  | n, m :: k :: rest =>
      if 2 * n ≤ N + k then compressChain N n (k :: rest)
      else m :: compressChain N m (k :: rest)

/-- No pair of consecutive edges in this chain can be merged admissibly. -/
def ChainIrreducible (N : ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | _, [_] => True
  | n, m :: k :: rest => ¬Admissible N k n ∧ ChainIrreducible N m (k :: rest)

/-- Compression retains only original scales, in their original order. -/
theorem compressChain_sublist (N : ℕ) :
    ∀ (n : ℕ) (l : List ℕ), (compressChain N n l).Sublist l
  | _, [] => List.Sublist.refl _
  | _, [_] => List.Sublist.refl _
  | n, m :: k :: rest => by
      rw [compressChain]
      split
      · exact (compressChain_sublist N n (k :: rest)).cons m
      · exact (compressChain_sublist N m (k :: rest)).cons_cons m

/-- Compression preserves the last endpoint exactly. -/
theorem chainEnd_compressChain (N : ℕ) :
    ∀ (n : ℕ) (l : List ℕ), chainEnd n (compressChain N n l) = chainEnd n l
  | _, [] => rfl
  | _, [_] => rfl
  | n, m :: k :: rest => by
      rw [compressChain]
      split
      · exact chainEnd_compressChain N n (k :: rest)
      · exact chainEnd_compressChain N m (k :: rest)

/-- Compression preserves strict descent and every retained edge's admissibility. -/
theorem isChain_compressChain (N : ℕ) :
    ∀ (n : ℕ) (l : List ℕ),
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) →
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: compressChain N n l)
  | _, [], h => h
  | _, [_], h => h
  | n, m :: k :: rest, h => by
      obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
      obtain ⟨hmk, hrest⟩ := List.isChain_cons_cons.mp htail
      rw [compressChain]
      split
      · exact isChain_compressChain N n (k :: rest)
          (List.isChain_cons_cons.mpr ⟨⟨hmk.1.trans hnm.1, by assumption⟩, hrest⟩)
      · exact List.isChain_cons_cons.mpr
          ⟨hnm, isChain_compressChain N m (k :: rest)
            (List.isChain_cons_cons.mpr ⟨hmk, hrest⟩)⟩

/-- The same compression decreases the cost for every profile. -/
theorem chainCost_compressChain_le (g : ℕ → ℝ) (N : ℕ) :
    ∀ (n : ℕ) (l : List ℕ), List.IsChain (fun n m ↦ m < n) (n :: l) →
      chainCost g n (compressChain N n l) ≤ chainCost g n l
  | _, [], _ => le_rfl
  | _, [_], _ => le_rfl
  | n, m :: k :: rest, h => by
      obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
      obtain ⟨hmk, hrest⟩ := List.isChain_cons_cons.mp htail
      rw [compressChain]
      split
      · refine (chainCost_compressChain_le g N n (k :: rest)
          (List.isChain_cons_cons.mpr ⟨hmk.trans hnm, hrest⟩)).trans ?_
        have hmerge := edgeCost_merge_le (g := g) hmk.le hnm.le
        simp only [chainCost]
        linarith
      · exact add_le_add le_rfl (chainCost_compressChain_le g N m (k :: rest)
          (List.isChain_cons_cons.mpr ⟨hmk, hrest⟩))

private theorem le_first_of_mem_aux {k p : ℕ} {rest : List ℕ}
    (h : List.IsChain (fun n m ↦ m < n) (k :: rest)) (hp : p ∈ k :: rest) : p ≤ k := by
  rcases List.mem_cons.mp hp with rfl | hp
  · exact le_rfl
  · exact (h.rel_cons hp).le

/-- Every surviving pair of consecutive edges fails the admissible merging test. -/
theorem chainIrreducible_compressChain (N : ℕ) :
    ∀ (n : ℕ) (l : List ℕ), List.IsChain (fun n m ↦ m < n) (n :: l) →
      ChainIrreducible N n (compressChain N n l)
  | _, [], _ => trivial
  | _, [_], _ => trivial
  | n, m :: k :: rest, h => by
      obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
      obtain ⟨hmk, hrest⟩ := List.isChain_cons_cons.mp htail
      rw [compressChain]
      split
      · exact chainIrreducible_compressChain N n (k :: rest)
          (List.isChain_cons_cons.mpr ⟨hmk.trans hnm, hrest⟩)
      · have hrec := chainIrreducible_compressChain N m (k :: rest)
          (List.isChain_cons_cons.mpr ⟨hmk, hrest⟩)
        cases heq : compressChain N m (k :: rest) with
        | nil => trivial
        | cons p tail =>
            refine ⟨?_, by simpa [heq] using hrec⟩
            have hp : p ∈ k :: rest := (compressChain_sublist N m (k :: rest)).subset
              (by simp [heq])
            have hpk := le_first_of_mem_aux hrest hp
            unfold Admissible at *
            omega

/-- Irreducibility passes to every tail of a chain. -/
theorem ChainIrreducible.tail {N n m : ℕ} {l : List ℕ}
    (h : ChainIrreducible N n (m :: l)) : ChainIrreducible N m l := by
  cases l with
  | nil => trivial
  | cons k rest => exact h.2

/-- Each surviving pair of edges more than doubles the complementary distance from `N`. -/
theorem ChainIrreducible.two_step_gap {N n m k : ℕ} {rest : List ℕ}
    (h : ChainIrreducible N n (m :: k :: rest)) (hn : n ≤ N) :
    2 * (N - n) < N - k := by
  have hnot := h.1
  unfold Admissible at hnot
  omega

/-- A prescribed number of doublings bounds the number of edges in an irreducible chain. -/
theorem ChainIrreducible.length_le_of_pow_gap {N : ℕ} :
    ∀ (k n : ℕ) (l : List ℕ), n ≤ N →
      List.IsChain (fun n m ↦ m < n) (n :: l) → ChainIrreducible N n l →
      N ≤ 2 ^ k * (N - n) → l.length ≤ 2 * k
  | 0, n, l, hn, hchain, _, hscale => by
      have hn0 : n = 0 := by
        simp only [pow_zero, one_mul] at hscale
        omega
      cases l with
      | nil => simp
      | cons m rest =>
          have hm := (List.isChain_cons_cons.mp hchain).1
          omega
  | k + 1, _, [], _, _, _, _ => by simp
  | k + 1, _, [_], _, _, _, _ => by simp; omega
  | k + 1, n, m :: p :: rest, hn, hchain, hirr, hscale => by
      have hnm := (List.isChain_cons_cons.mp hchain).1
      have hmp := (List.isChain_cons_cons.mp hchain.tail).1
      have hpN : p ≤ N := hmp.le.trans (hnm.le.trans hn)
      have hdouble := hirr.two_step_gap hn
      have hscale' : N ≤ 2 ^ k * (N - p) := hscale.trans (by
        calc
          2 ^ (k + 1) * (N - n) = 2 ^ k * (2 * (N - n)) := by ring
          _ ≤ 2 ^ k * (N - p) := Nat.mul_le_mul_left _ hdouble.le)
      have hlength := hirr.tail.tail.length_le_of_pow_gap k p rest hpN
        hchain.tail.tail hscale'
      simp only [List.length_cons] at *
      omega

/-- A fixed gap proportion supplies the power-of-two hypothesis uniformly in the grid depth. -/
theorem compressChain_length_le_of_gap_ratio {N n k : ℕ} {ζ : ℝ} (hζ : 0 < ζ)
    (hstart : (n : ℝ) ≤ (1 - ζ) * N) (hk : 1 ≤ (2 : ℝ) ^ k * ζ) {l : List ℕ}
    (hchain : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l)) :
    (compressChain N n l).length ≤ 2 * k := by
  have hnreal : (n : ℝ) ≤ N := by nlinarith [show (0 : ℝ) ≤ N by positivity]
  have hn : n ≤ N := by exact_mod_cast hnreal
  have hgap : ζ * N ≤ ((N - n : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; linarith
  have hscale : N ≤ 2 ^ k * (N - n) := by
    have hreal : (N : ℝ) ≤ (2 : ℝ) ^ k * ((N - n : ℕ) : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg N),
        mul_le_mul_of_nonneg_left hgap (show 0 ≤ (2 : ℝ) ^ k by positivity)]
    exact_mod_cast hreal
  have hdecr := hchain.imp (fun _ _ h ↦ h.1)
  exact (chainIrreducible_compressChain N n l hdecr).length_le_of_pow_gap k n _ hn
    ((isChain_compressChain N n l hchain).imp (fun _ _ h ↦ h.1)) hscale

/-- A compressed subchain keeps both endpoints and all admissible edges, never increases the
profile cost, and has at most twice the prescribed number of gap doublings. -/
theorem exists_compressed_chain (g : ℕ → ℝ) {N n k : ℕ} {l : List ℕ}
    (hn : n ≤ N) (hscale : N ≤ 2 ^ k * (N - n))
    (hchain : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l)) :
    ∃ l' : List ℕ, l'.Sublist l ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l') ∧
      chainEnd n l' = chainEnd n l ∧ chainCost g n l' ≤ chainCost g n l ∧
      ChainIrreducible N n l' ∧ l'.length ≤ 2 * k := by
  have hdecr := hchain.imp (fun _ _ h ↦ h.1)
  have hcompressed := isChain_compressChain N n l hchain
  have hirr := chainIrreducible_compressChain N n l hdecr
  exact ⟨compressChain N n l, compressChain_sublist N n l, hcompressed,
    chainEnd_compressChain N n l, chainCost_compressChain_le g N n l hdecr, hirr,
    hirr.length_le_of_pow_gap k n _ hn (hcompressed.imp (fun _ _ h ↦ h.1)) hscale⟩

/-- Compression has a bound depending only on the initial relative gap, not on the profile,
the original chain, or the grid depth. -/
theorem exists_uniform_compression_length {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : ℕ, ∀ (N n : ℕ) (l : List ℕ), (n : ℝ) ≤ (1 - ζ) * N →
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) →
      (compressChain N n l).length ≤ K := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ζ) (by norm_num : (1 : ℝ) < 2)
  have hk' : 1 ≤ (2 : ℝ) ^ k * ζ := (div_lt_iff₀ hζ).mp hk |>.le
  exact ⟨2 * k, fun _ _ _ hstart hchain ↦
    compressChain_length_le_of_gap_ratio hζ hstart hk' hchain⟩

end FalconerPacking
