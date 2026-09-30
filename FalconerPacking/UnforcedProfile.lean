/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Profile

/-!
# Profile operations for the unforced chain argument

This file uses the existing integer-grid minimum and edge costs. It proves general merging,
upper-endpoint truncation, uniform stability along a fixed chain, and the endpoint-clipping
operation used before the hard-gap optimization. These are finite profile statements; the
hard-component identity and the analytic distance theorem are separate obligations.
-/

noncomputable section

namespace FalconerPacking

/-- Removing an intermediate point never increases the sum of the two edge costs. -/
theorem edgeCost_merge_le {g : ℕ → ℝ} {m p n : ℕ} (hmp : m ≤ p) (hpn : p ≤ n) :
    edgeCost g m n ≤ edgeCost g m p + edgeCost g p n := by
  rw [edgeCost_insert hmp hpn]
  have hmax : max (gMin g m p) (gMin g p n) ≤ g p :=
    max_le (gMin_le hmp le_rfl) (gMin_le le_rfl hpn)
  linarith

/-- Truncating the upper endpoint of an edge decreases its cost. -/
theorem edgeCost_le_of_right_le {g : ℕ → ℝ} {m n p : ℕ} (hmn : m ≤ n) (hnp : n ≤ p) :
    edgeCost g m n ≤ edgeCost g m p := by
  have hmin : gMin g m p ≤ gMin g m n :=
    le_gMin hmn fun k hmk hkn ↦ gMin_le hmk (hkn.trans hnp)
  unfold edgeCost
  linarith

/-- Upper-endpoint truncation preserves admissibility. -/
theorem admissible_of_right_le {N m n p : ℕ} (hnp : n ≤ p) (h : Admissible N m p) :
    Admissible N m n := by
  unfold Admissible at *
  omega

/-- A grid-Lipschitz profile's edge cost is at most its length. -/
theorem edgeCost_le_length {g : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) :
    edgeCost g m n ≤ (n : ℝ) - m := by
  have hmin : g m - ((n : ℝ) - m) ≤ gMin g m n := by
    refine le_gMin hmn fun k hmk hkn ↦ ?_
    have h := sub_le_of_lipschitz hmk hlip
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  unfold edgeCost
  linarith

/-- Clipping by a line of slope minus one can only increase every edge cost. -/
theorem edgeCost_le_clip {g : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) (c : ℝ) :
    edgeCost g m n ≤ edgeCost (fun k ↦ min (g k) (c - k)) m n := by
  by_cases hstart : g m ≤ c - m
  · have hmin : gMin (fun k ↦ min (g k) (c - k)) m n ≤ gMin g m n := by
      refine le_gMin hmn fun k hmk hkn ↦ ?_
      exact (gMin_le hmk hkn).trans (min_le_left _ _)
    simp only [edgeCost, min_eq_left hstart]
    linarith
  · have hstart' : c - (m : ℝ) ≤ g m := le_of_not_ge hstart
    have hmin : gMin (fun k ↦ min (g k) (c - k)) m n ≤ c - n :=
      (gMin_le hmn le_rfl).trans (min_le_right _ _)
    have hcost := edgeCost_le_length hmn hlip
    simp only [edgeCost, min_eq_right hstart']
    unfold edgeCost at hcost
    linarith

/-- An edgewise cost bound passes to every fixed decreasing chain. -/
theorem chainCost_mono_of_edgeCost {g h : ℕ → ℝ}
    (hedge : ∀ m n, m ≤ n → edgeCost g m n ≤ edgeCost h m n) :
    ∀ (n : ℕ) (l : List ℕ), List.IsChain (· > ·) (n :: l) →
      chainCost g n l ≤ chainCost h n l
  | _, [], _ => le_rfl
  | n, m :: rest, hc => by
    obtain ⟨hmn, hrest⟩ := List.isChain_cons_cons.mp hc
    exact add_le_add (hedge m n hmn.le) (chainCost_mono_of_edgeCost hedge m rest hrest)

/-- The same chain has no greater cost before endpoint clipping. -/
theorem chainCost_le_clip {g : ℕ → ℝ}
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) (c : ℝ)
    (n : ℕ) (l : List ℕ) (hc : List.IsChain (· > ·) (n :: l)) :
    chainCost g n l ≤ chainCost (fun k ↦ min (g k) (c - k)) n l :=
  chainCost_mono_of_edgeCost (fun _ _ hmn ↦ edgeCost_le_clip hmn hlip c) n l hc

/-- Uniform profile error costs at most twice the error per edge of a fixed chain. -/
theorem chainCost_perturb {g h : ℕ → ℝ} {δ : ℝ} (hδ : ∀ k, |g k - h k| ≤ δ) :
    ∀ (n : ℕ) (l : List ℕ), List.IsChain (· > ·) (n :: l) →
      |chainCost g n l - chainCost h n l| ≤ 2 * δ * l.length
  | _, [], _ => by simp [chainCost]
  | n, m :: rest, hc => by
    obtain ⟨hmn, hrest⟩ := List.isChain_cons_cons.mp hc
    have he := edgeCost_perturb hmn.le hδ
    have ht := chainCost_perturb hδ m rest hrest
    calc
      |chainCost g n (m :: rest) - chainCost h n (m :: rest)| =
          |(edgeCost g m n - edgeCost h m n) +
            (chainCost g m rest - chainCost h m rest)| := by
        simp only [chainCost]
        congr 1
        ring
      _ ≤ |edgeCost g m n - edgeCost h m n| +
          |chainCost g m rest - chainCost h m rest| := abs_add_le _ _
      _ ≤ 2 * δ + 2 * δ * rest.length := add_le_add he ht
      _ = 2 * δ * (m :: rest).length := by simp; ring

/-- The clipped profile retains the lower linear barrier up to its terminal depth. -/
theorem lower_barrier_le_clip {g : ℕ → ℝ} {a : ℝ} {N k : ℕ}
    (ha : -1 ≤ a) (hk : k ≤ N) (hlower : a * k ≤ g k) :
    a * k ≤ min (g k) ((1 + a) * N - k) := by
  refine le_min hlower ?_
  have hkn : (k : ℝ) ≤ N := by exact_mod_cast hk
  nlinarith [mul_nonneg (show 0 ≤ 1 + a by linarith) (sub_nonneg.mpr hkn)]

/-- At the terminal depth, clipping puts the profile exactly on the lower barrier. -/
theorem clip_endpoint {g : ℕ → ℝ} {a : ℝ} {N : ℕ} (h : a * N ≤ g N) :
    min (g N) ((1 + a) * N - N) = a * N := by
  have heq : (1 + a) * (N : ℝ) - N = a * N := by ring
  rw [heq, min_eq_right h]

/-- Endpoint clipping preserves the grid Lipschitz bound. -/
theorem clip_lipschitz {g : ℕ → ℝ}
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) (c : ℝ) (k : ℕ) :
    |min (g (k + 1)) (c - (k + 1 : ℕ)) - min (g k) (c - k)| ≤ 1 := by
  have hline : |(c - (k + 1 : ℕ)) - (c - k)| = 1 := by
    push_cast
    have : c - ((k : ℝ) + 1) - (c - k) = -1 := by ring
    rw [this]
    norm_num
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hlip k) hline.le)

/-- The endpoint-corrected half-variation bound holds for every decreasing grid chain. -/
theorem chainCost_le_half_variation {g : ℕ → ℝ}
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1)
    (n : ℕ) (l : List ℕ) (hc : List.IsChain (· > ·) (n :: l)) :
    chainCost g n l ≤ ((n : ℝ) - chainEnd n l + g (chainEnd n l) - g n) / 2 := by
  have h := chainCost_le_potential (g := g) (b := 1 / 2) (N := 0)
    (by norm_num) hlip n l hc
  dsimp [potential] at h
  convert h using 1
  ring

end FalconerPacking
