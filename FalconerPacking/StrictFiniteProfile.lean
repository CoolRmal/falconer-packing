/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.HardGapThreshold
import FalconerPacking.FiniteHardGapProfile

/-!
# Strict finite-profile cost below the hard-gap cutoff

The scalar cutoff selects a valid hard-gap certificate. Its strict cost margin absorbs both
the finite-chain rounding constant and small additive errors in the profile barriers.
-/

noncomputable section

namespace FalconerPacking

private theorem exists_strict_hardGap_certificate_aux {s u : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) :
    ∃ b C : ℝ, u - 1 ≤ b ∧ s - 1 < b ∧ b < 1 ∧ C < s - 1 ∧
      ((b * (4 + 2 * (s - 1)) ≤ 1 + 2 * (s - 1) ∧
          twoGapGuard (s - 1) b ≤ 0 ∧ C = twoGapCost (s - 1) b) ∨
        (1 + 2 * (s - 1) ≤ b * (4 + 2 * (s - 1)) ∧
          C = singleGapCost (s - 1) b)) := by
  obtain ⟨b, hub, _, hb, hcase⟩ := exists_hardGap_barrier hs hs' hu hu'
  have hden : 0 < 4 + 2 * (s - 1) := by linarith
  rcases hcase with ⟨htrans, _, hguard, hcost⟩ | ⟨htrans, hcost⟩
  · refine ⟨b, twoGapCost (s - 1) b, hub, by linarith, hb, hcost, Or.inl ⟨?_, hguard, rfl⟩⟩
    exact (le_div_iff₀ hden).mp htrans
  · refine ⟨b, singleGapCost (s - 1) b, hub, by linarith, hb, hcost, Or.inr ⟨?_, rfl⟩⟩
    exact (div_le_iff₀ hden).mp htrans

/-- Strictly below the hard-gap cutoff, all sufficiently long admissible finite profiles
have a uniformly short chain whose cost is strictly below `(s-1)N`. The tolerance and the
cost margin are positive and independent of the profile and its length. -/
theorem exists_strict_uniform_finite_profile {s u ζ : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hζ : 0 < ζ) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧ ∃ K N₀ : ℕ, 0 < K ∧ 0 < N₀ ∧
      ∀ (N n : ℕ) (g : ℕ → ℝ), N₀ ≤ N →
        (∀ j, j < N → |g (j + 1) - g j| ≤ 1) →
        (∀ j, j ≤ N → (s - 1) * j - ε * N ≤ g j) →
        (∀ j, j ≤ N → g j ≤ (u - 1) * j + ε * N) →
        (n : ℝ) ≤ (1 - ζ) * N →
        ∃ l : List ℕ, l.length ≤ K ∧
          List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
          chainEnd n l = 0 ∧ chainCost g n l ≤ (s - 1 - η) * N := by
  obtain ⟨b, C, hub, hab, hb, hC, hcase⟩ :=
    exists_strict_hardGap_certificate_aux hs hs' hu hu'
  obtain ⟨K, hK, hbound⟩ := exists_uniform_finite_hardGap_chain_with_error hζ
  let gap : ℝ := s - 1 - C
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  let ε : ℝ := gap / (8 * K)
  let η : ℝ := gap / 2
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max 1 (8 * K / gap))
  have hN₀pos : 0 < N₀ := by
    have : (0 : ℝ) < N₀ := lt_trans (by positivity) hN₀
    exact_mod_cast this
  refine ⟨ε, η, by dsimp [ε]; positivity, by dsimp [η]; positivity,
    K, N₀, hK, hN₀pos, fun N n g hN₀N hlip hlo hup hstart ↦ ?_⟩
  have hN : 0 < N := hN₀pos.trans_le hN₀N
  have hupper : ∀ j, j ≤ N → g j ≤ b * j + ε * N := by
    intro j hj
    exact (hup j hj).trans (add_le_add
      (mul_le_mul_of_nonneg_right hub (Nat.cast_nonneg j)) le_rfl)
  obtain ⟨l, hlen, hl, he, hc⟩ := hbound N n (s - 1) b C ε g hN
    (by linarith) (by linarith) hab hb.le (by dsimp [ε]; positivity)
    hcase hlip hlo hupper hstart
  have hlarge : 8 * (K : ℝ) ≤ gap * N := by
    have hratio : 8 * (K : ℝ) / gap < N₀ := (le_max_right _ _).trans_lt hN₀
    have hmul := (div_lt_iff₀ hgap).mp hratio
    have hNN : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
    nlinarith [mul_le_mul_of_nonneg_left hNN hgap.le]
  have hε : 2 * ε * K = gap / 4 := by
    dsimp [ε]
    field_simp
    ring
  have herr : 2 * ε * N * K = (gap / 4) * N := by
    rw [show 2 * ε * N * K = (2 * ε * K) * N by ring, hε]
  refine ⟨l, hlen, hl, he, hc.trans ?_⟩
  rw [herr]
  dsimp [η, gap]
  dsimp [gap] at hlarge
  nlinarith

end FalconerPacking
