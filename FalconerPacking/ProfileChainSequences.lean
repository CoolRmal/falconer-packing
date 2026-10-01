/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.StrictFiniteProfile

/-!
# Global sequences from the constructed finite profile chain

The actual finite depth list is extended by zero. Its real cost is exactly the sum of
its consecutive edge costs, and every genuine edge retains the original admissibility.
-/

noncomputable section

namespace FalconerPacking

/-- The actual depth list, extended by zero beyond its terminal entry. -/
def profileChainDepth : ℕ → List ℕ → ℕ → ℕ
  | n, _, 0 => n
  | _, [], _ + 1 => 0
  | _, m :: l, j + 1 => profileChainDepth m l j

@[simp]
theorem profileChainDepth_zero (n : ℕ) (l : List ℕ) : profileChainDepth n l 0 = n := rfl

/-- The endpoint is exactly the endpoint used by the finite-profile theorem. -/
theorem profileChainDepth_length (n : ℕ) (l : List ℕ) :
    profileChainDepth n l l.length = chainEnd n l := by
  induction l generalizing n with
  | nil => rfl
  | cons m l ih => simpa only [List.length_cons, profileChainDepth, chainEnd] using ih m

/-- Beyond its last entry, the sequence is literally zero. -/
theorem profileChainDepth_of_length_lt (n : ℕ) (l : List ℕ) {j : ℕ}
    (hj : l.length < j) : profileChainDepth n l j = 0 := by
  induction l generalizing n j with
  | nil => cases j <;> simp_all [profileChainDepth]
  | cons m l ih =>
    cases j with
    | zero => simp at hj
    | succ j =>
      simpa only [profileChainDepth] using ih m (by simpa only [List.length_cons,
        Nat.succ_lt_succ_iff] using hj)

/-- A decreasing actual list extends to a globally antitone sequence. -/
theorem antitone_profileChainDepth {n : ℕ} {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n) (n :: l)) :
    Antitone (profileChainDepth n l) := by
  apply antitone_nat_of_succ_le
  intro j
  induction l generalizing n j with
  | nil => cases j <;> simp [profileChainDepth]
  | cons m l ih =>
    have hh := List.isChain_cons_cons.mp hl
    cases j with
    | zero => simpa only [profileChainDepth] using hh.1.le
    | succ j => simpa only [profileChainDepth] using ih hh.2 j

/-- Every finite edge has exactly the strict decrease and curvature admissibility originally proved. -/
theorem profileChainDepth_edge {N n : ℕ} {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l))
    {j : ℕ} (hj : j < l.length) :
    profileChainDepth n l (j + 1) < profileChainDepth n l j ∧
      Admissible N (profileChainDepth n l (j + 1)) (profileChainDepth n l j) := by
  induction l generalizing n j with
  | nil => simp at hj
  | cons m l ih =>
    have hh := List.isChain_cons_cons.mp hl
    cases j with
    | zero => simpa only [profileChainDepth] using hh.1
    | succ j =>
      simpa only [profileChainDepth] using ih hh.2 (by simpa only [List.length_cons,
        Nat.succ_lt_succ_iff] using hj)

/-- The finite edge sum is the original profile cost, with no rounding or extra edge. -/
theorem sum_edgeCost_profileChainDepth (g : ℕ → ℝ) (n : ℕ) (l : List ℕ) :
    (∑ j ∈ Finset.range l.length,
      edgeCost g (profileChainDepth n l (j + 1)) (profileChainDepth n l j)) =
      chainCost g n l := by
  induction l generalizing n with
  | nil => simp [chainCost]
  | cons m l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [profileChainDepth]
    rw [ih]
    simp only [chainCost]
    ring

/-- The auxiliary angular depth is zero initially and then uses the preceding spatial depth. -/
def profileChainAngle (N n : ℕ) (l : List ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => N - profileChainDepth n l j

/-- Angular depths are globally monotone, while no spatial level is inserted at a crossing. -/
theorem monotone_profileChainAngle {N n : ℕ} {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n) (n :: l)) :
    Monotone (profileChainAngle N n l) := by
  apply monotone_nat_of_le_succ
  intro j
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    change N - profileChainDepth n l j ≤ N - profileChainDepth n l (j + 1)
    exact Nat.sub_le_sub_left ((antitone_profileChainDepth hl) (Nat.le_succ j)) N

/-- Every angular level is at most the terminal auxiliary depth N. -/
theorem profileChainAngle_le (N n : ℕ) (l : List ℕ) (j : ℕ) :
    profileChainAngle N n l j ≤ N := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j => exact Nat.sub_le _ _

/-- All constructed depths stay below their initial depth. -/
theorem profileChainDepth_le_initial {n : ℕ} {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n) (n :: l)) (j : ℕ) :
    profileChainDepth n l j ≤ n := by
  simpa only [profileChainDepth_zero] using
    antitone_profileChainDepth hl (Nat.zero_le j)

/-- The strict dimension cutoff supplies actual global sequences for the analytic chain.
The frequency depth may be any larger integer, which permits one fixed chain on a broad annulus. -/
theorem exists_strict_uniform_profile_sequences {s u ζ : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hζ : 0 < ζ) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧ ∃ K N₀ : ℕ, 0 < K ∧ 0 < N₀ ∧
      ∀ (N F n : ℕ) (g : ℕ → ℝ), N₀ ≤ N → N ≤ F →
        (∀ j, j < N → |g (j + 1) - g j| ≤ 1) →
        (∀ j, j ≤ N → (s - 1) * j - ε * N ≤ g j) →
        (∀ j, j ≤ N → g j ≤ (u - 1) * j + ε * N) →
        (n : ℝ) ≤ (1 - ζ) * N →
        ∃ (k : ℕ) (d e : ℕ → ℕ), k ≤ K ∧ Antitone d ∧ Monotone e ∧
          d 0 = n ∧ d k = 0 ∧ e 0 = 0 ∧ (∀ j, d j ≤ N ∧ e j ≤ F) ∧
          (∀ j, e (j + 1) = F - d j) ∧
          (∀ j, j < k → d (j + 1) < d j ∧ Admissible N (d (j + 1)) (d j)) ∧
          (∑ j ∈ Finset.range k, edgeCost g (d (j + 1)) (d j)) ≤
            (s - 1 - η) * N := by
  obtain ⟨ε, η, hε, hη, K, N₀, hK, hN₀, h⟩ :=
    exists_strict_uniform_finite_profile hs hs' hu hu' hζ
  refine ⟨ε, η, hε, hη, K, N₀, hK, hN₀, ?_⟩
  intro N F n g hN _hNF hlip hlo hup hstart
  obtain ⟨l, hlen, hl, hend, hcost⟩ := h N n g hN hlip hlo hup hstart
  have hl' : List.IsChain (fun n m ↦ m < n) (n :: l) :=
    hl.imp (fun _ _ hnm ↦ hnm.1)
  have hn : n ≤ N := by
    have : (n : ℝ) ≤ N := by
      nlinarith [mul_nonneg hζ.le (Nat.cast_nonneg N)]
    exact_mod_cast this
  refine ⟨l.length, profileChainDepth n l, profileChainAngle F n l, hlen,
    antitone_profileChainDepth hl', monotone_profileChainAngle hl', rfl, ?_, rfl,
    fun j ↦ ⟨(profileChainDepth_le_initial hl' j).trans hn,
      profileChainAngle_le F n l j⟩, fun j ↦ rfl,
    fun j hj ↦ profileChainDepth_edge hl hj, ?_⟩
  · simpa only [profileChainDepth_length] using hend
  · simpa only [sum_edgeCost_profileChainDepth] using hcost

end FalconerPacking
