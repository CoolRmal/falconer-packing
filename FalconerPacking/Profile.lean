/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Statement
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite profiles and edge costs

Module 3 of the implementation ledger, in the finite formulation of Section 6.1: a profile is a
real sequence on the integer grid, an edge `[m, n]` costs `g m - min {g k : m ≤ k ≤ n}`, and the
cost of a chain is the sum of its edge costs.

This file proves the elementary part of the profile API:

* `gMin_eq_min` — minima split at an interior point;
* `edgeCost_nonneg`, `edgeCost_merge_of_zero` — nonnegativity, and that two zero-cost edges
  merge into a zero-cost edge;
* `potential_monotone` — the potential `2bk - bN - g k` is nondecreasing when `2b ≥ 1`;
* `posPart_le` — the discrete inequality `max (-Δg) 0 ≤ (2b - Δg) / (1 + 2b)` for `|Δg| ≤ 1`;
* `edgeCost_le_of_lipschitz` — the telescoped edge bound
  `edgeCost g m n ≤ (2b(n - m) - (g n - g m)) / (1 + 2b)`.

No analytic input is used: everything here is finite real arithmetic.
-/

noncomputable section

open Finset

namespace FalconerPacking

/-- The minimum of `g` over the integer interval `[m, n]`, totalized to `g m` when `n < m`. -/
def gMin (g : ℕ → ℝ) (m n : ℕ) : ℝ :=
  if h : (Finset.Icc m n).Nonempty then (Finset.Icc m n).inf' h g else g m

/-- The cost of the edge `[m, n]`: the drop from the left endpoint to the interval minimum. -/
def edgeCost (g : ℕ → ℝ) (m n : ℕ) : ℝ := g m - gMin g m n

theorem gMin_le {g : ℕ → ℝ} {m n k : ℕ} (hmk : m ≤ k) (hkn : k ≤ n) : gMin g m n ≤ g k := by
  have hne : (Finset.Icc m n).Nonempty := ⟨k, Finset.mem_Icc.2 ⟨hmk, hkn⟩⟩
  rw [gMin, dif_pos hne]
  exact Finset.inf'_le _ (Finset.mem_Icc.2 ⟨hmk, hkn⟩)

theorem le_gMin {g : ℕ → ℝ} {m n : ℕ} {c : ℝ} (hmn : m ≤ n)
    (h : ∀ k, m ≤ k → k ≤ n → c ≤ g k) : c ≤ gMin g m n := by
  have hne : (Finset.Icc m n).Nonempty := ⟨m, Finset.mem_Icc.2 ⟨le_rfl, hmn⟩⟩
  rw [gMin, dif_pos hne]
  exact Finset.le_inf' hne _ fun k hk ↦
    h k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2

/-- The minimum over `[m, n]` splits at any interior point. -/
theorem gMin_eq_min {g : ℕ → ℝ} {m p n : ℕ} (hmp : m ≤ p) (hpn : p ≤ n) :
    gMin g m n = min (gMin g m p) (gMin g p n) := by
  refine le_antisymm (le_min ?_ ?_) ?_
  · refine le_gMin hmp fun k hk hk' ↦ gMin_le hk (hk'.trans hpn)
  · refine le_gMin hpn fun k hk hk' ↦ gMin_le (hmp.trans hk) hk'
  · refine le_gMin (hmp.trans hpn) fun k hk hk' ↦ ?_
    rcases le_or_gt k p with h | h
    · exact (min_le_left _ _).trans (gMin_le hk h)
    · exact (min_le_right _ _).trans (gMin_le h.le hk')

theorem edgeCost_nonneg {g : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) : 0 ≤ edgeCost g m n :=
  sub_nonneg.2 (gMin_le le_rfl hmn)

/-- Two consecutive zero-cost edges merge into a zero-cost edge. -/
theorem edgeCost_merge_of_zero {g : ℕ → ℝ} {m p n : ℕ} (hmp : m ≤ p) (hpn : p ≤ n)
    (h₁ : edgeCost g m p = 0) (h₂ : edgeCost g p n = 0) : edgeCost g m n = 0 := by
  have h₁' : gMin g m p = g m := by rw [edgeCost, sub_eq_zero] at h₁; exact h₁.symm
  have h₂' : gMin g p n = g p := by rw [edgeCost, sub_eq_zero] at h₂; exact h₂.symm
  have hgp : g m ≤ g p := h₁' ▸ gMin_le hmp le_rfl
  rw [edgeCost, gMin_eq_min hmp hpn, h₁', h₂', min_eq_left hgp, sub_self]

section Potential

variable {g : ℕ → ℝ} {b : ℝ}

/-- The potential `L k = 2bk - bN - g k` is nondecreasing as soon as `2b ≥ 1` and `g` is
1-Lipschitz on the grid. -/
theorem potential_monotone (N : ℕ) (hb : 1 / 2 ≤ b)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) (k : ℕ) :
    2 * b * k - b * N - g k ≤ 2 * b * (k + 1) - b * N - g (k + 1) := by
  have h := abs_le.1 (hlip k)
  linarith [h.1, h.2]

/-- The discrete form of `(-g')₊ ≤ (2b - g') / (1 + 2b)`. -/
theorem posPart_le {Δ : ℝ} (hb : 1 / 2 ≤ b) (hΔ : |Δ| ≤ 1) :
    max (-Δ) 0 ≤ (2 * b - Δ) / (1 + 2 * b) := by
  have h := abs_le.1 hΔ
  have hpos : (0 : ℝ) < 1 + 2 * b := by linarith
  rcases le_or_gt 0 Δ with h₀ | h₀
  · rw [max_eq_right (by linarith)]
    exact div_nonneg (by linarith) hpos.le
  · rw [max_eq_left (by linarith)]
    rw [le_div_iff₀ hpos]
    nlinarith [h.1]

/-- The cost of an edge is at most the sum of the positive parts of the decrements. -/
theorem edgeCost_le_sum_posPart {m n : ℕ} (hmn : m ≤ n) :
    edgeCost g m n ≤ ∑ k ∈ Finset.Ico m n, max (g k - g (k + 1)) 0 := by
  have hne : (Finset.Icc m n).Nonempty := ⟨m, Finset.mem_Icc.2 ⟨le_rfl, hmn⟩⟩
  have hmin : ∃ j, m ≤ j ∧ j ≤ n ∧ gMin g m n = g j := by
    rw [gMin, dif_pos hne]
    obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_inf' hne g
    exact ⟨j, (Finset.mem_Icc.1 hj).1, (Finset.mem_Icc.1 hj).2, hj'⟩
  obtain ⟨j, hmj, hjn, hgj⟩ := hmin
  have htel : g m - g j = ∑ k ∈ Finset.Ico m j, (g k - g (k + 1)) := by
    rw [Finset.sum_Ico_eq_sub _ hmj]
    simp [Finset.sum_range_sub' fun i ↦ g i]
  have h₁ : edgeCost g m n = ∑ k ∈ Finset.Ico m j, (g k - g (k + 1)) := by
    rw [edgeCost, hgj, htel]
  rw [h₁]
  calc ∑ k ∈ Finset.Ico m j, (g k - g (k + 1))
      ≤ ∑ k ∈ Finset.Ico m j, max (g k - g (k + 1)) 0 :=
        Finset.sum_le_sum fun k _ ↦ le_max_left _ _
    _ ≤ ∑ k ∈ Finset.Ico m n, max (g k - g (k + 1)) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Ico_subset_Ico le_rfl hjn) fun k _ _ ↦ le_max_right _ _

/-- **The telescoped edge bound.**  For a 1-Lipschitz grid profile and `2b ≥ 1`, the cost of the
edge `[m, n]` is at most `(2b(n - m) - (g n - g m)) / (1 + 2b)`. -/
theorem edgeCost_le_of_lipschitz {m n : ℕ} (hmn : m ≤ n) (hb : 1 / 2 ≤ b)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) :
    edgeCost g m n ≤ (2 * b * (n - m : ℕ) - (g n - g m)) / (1 + 2 * b) := by
  have hpos : (0 : ℝ) < 1 + 2 * b := by linarith
  refine (edgeCost_le_sum_posPart hmn).trans ?_
  have hterm : ∀ k ∈ Finset.Ico m n,
      max (g k - g (k + 1)) 0 ≤ (2 * b - (g (k + 1) - g k)) / (1 + 2 * b) := fun k _ ↦ by
    simpa using posPart_le (b := b) hb (hlip k)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_div, div_le_div_iff_of_pos_right hpos]
  have htel : ∑ k ∈ Finset.Ico m n, (g (k + 1) - g k) = g n - g m := by
    rw [Finset.sum_Ico_eq_sub _ hmn]
    simp [Finset.sum_range_sub fun i ↦ g i]
  rw [Finset.sum_sub_distrib, htel, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  linarith

end Potential

section Chains

variable {g : ℕ → ℝ} {b : ℝ}

/-- The potential `L k = 2bk - bN - g k` of Lemma 3.2. -/
def potential (b : ℝ) (N : ℕ) (g : ℕ → ℝ) (k : ℕ) : ℝ := 2 * b * k - b * N - g k

/-- An edge `[m, n]` is admissible at scale `N` when `2n ≤ N + m`. -/
def Admissible (N m n : ℕ) : Prop := 2 * n ≤ N + m

/-- The cost of a chain that starts at `n` and then visits the points of `l` in order. -/
def chainCost (g : ℕ → ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | n, m :: rest => edgeCost g m n + chainCost g m rest

/-- The last point of a chain that starts at `n` and then visits the points of `l`. -/
def chainEnd : ℕ → List ℕ → ℕ
  | n, [] => n
  | _, m :: rest => chainEnd m rest

theorem chainCost_nonneg (g : ℕ → ℝ) :
    ∀ (n : ℕ) (l : List ℕ), List.Chain (· > ·) n l → 0 ≤ chainCost g n l
  | _, [], _ => le_rfl
  | n, m :: rest, h => by
    obtain ⟨hmn, hrest⟩ := List.chain_cons.1 h
    exact add_nonneg (edgeCost_nonneg hmn.le) (chainCost_nonneg g m rest hrest)

/-- A single edge costs at most the increment of the potential across it. -/
theorem edgeCost_le_potential {N m n : ℕ} (hmn : m ≤ n) (hb : 1 / 2 ≤ b)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) :
    edgeCost g m n ≤ (potential b N g n - potential b N g m) / (1 + 2 * b) := by
  have hcast : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hmn
  have h := edgeCost_le_of_lipschitz (g := g) (b := b) hmn hb hlip
  rw [hcast] at h
  refine h.trans (le_of_eq ?_)
  rw [potential, potential]
  ring_nf

/-- **The chain-cost bound.**  A descending chain costs at most the total increment of the
potential between its endpoints. -/
theorem chainCost_le_potential {N : ℕ} (hb : 1 / 2 ≤ b)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) :
    ∀ (n : ℕ) (l : List ℕ), List.Chain (· > ·) n l →
      chainCost g n l ≤ (potential b N g n - potential b N g (chainEnd n l)) / (1 + 2 * b)
  | n, [], _ => by simp [chainCost, chainEnd]
  | n, m :: rest, h => by
    obtain ⟨hmn, hrest⟩ := List.chain_cons.1 h
    have hstep := edgeCost_le_potential (N := N) (g := g) (b := b) hmn.le hb hlip
    have htail := chainCost_le_potential (N := N) hb hlip m rest hrest
    have : chainCost g n (m :: rest) = edgeCost g m n + chainCost g m rest := rfl
    rw [this, chainEnd]
    calc edgeCost g m n + chainCost g m rest
        ≤ (potential b N g n - potential b N g m) / (1 + 2 * b) +
            (potential b N g m - potential b N g (chainEnd m rest)) / (1 + 2 * b) :=
          add_le_add hstep htail
      _ = (potential b N g n - potential b N g (chainEnd m rest)) / (1 + 2 * b) := by ring

end Chains

section Descent

/-- One step of the greedy descent of Lemma 3.2: halve the remaining depth, but never pass the
barrier `q + 1`. -/
def descend (N q n : ℕ) : ℕ := max (q + 1) (2 * n - N)

theorem descend_lt {N q n : ℕ} (hq : q + 1 < n) (hn : n < N) : descend N q n < n := by
  refine max_lt hq ?_
  omega

theorem admissible_descend (N q n : ℕ) : Admissible N (descend N q n) n := by
  rw [Admissible, descend]
  rcases le_or_gt (2 * n) N with h | h
  · omega
  · have : 2 * n - N ≤ max (q + 1) (2 * n - N) := le_max_right _ _
    omega

/-- The depth after `m` doubling steps, capped at the maximal depth `M`. -/
def depthIter (M : ℕ) : ℕ → ℕ → ℕ
  | 0, D => D
  | (m + 1), D => depthIter M m (min (2 * D) M)

/-- Doubling the remaining depth reaches the cap in `m` steps once `2 ^ m * D ≥ M`: this is the
edge count of Lemma 3.2. -/
theorem min_le_depthIter (M : ℕ) : ∀ (m D : ℕ), min M (2 ^ m * D) ≤ depthIter M m D
  | 0, D => by simp [depthIter]
  | (m + 1), D => by
    refine le_trans ?_ (min_le_depthIter M m (min (2 * D) M))
    rcases le_or_gt M (2 * D) with h | h
    · rw [min_eq_right h]
      have : M ≤ 2 ^ m * M := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos m)
      omega
    · rw [min_eq_left h.le]
      have : 2 ^ (m + 1) * D = 2 ^ m * (2 * D) := by ring
      omega

theorem depthIter_eq_of_le {M m D : ℕ} (hD : D ≤ M) (h : M ≤ 2 ^ m * D) :
    depthIter M m D = M := by
  have hle : ∀ (m D : ℕ), D ≤ M → depthIter M m D ≤ M := by
    intro m
    induction m with
    | zero => intro D hD; simpa [depthIter] using hD
    | succ m ih => intro D _; exact ih _ (min_le_right _ _)
  have h₁ := min_le_depthIter M m D
  rw [min_eq_left h] at h₁
  exact le_antisymm (hle m D hD) h₁

/-- The greedy descent of Lemma 3.2, as a list of at most `k` points. -/
def descentChain (N q : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | (k + 1), n => if q + 1 < n then descend N q n :: descentChain N q k (descend N q n) else []

theorem descentChain_length (N q : ℕ) : ∀ (k n : ℕ), (descentChain N q k n).length ≤ k
  | 0, _ => by simp [descentChain]
  | (k + 1), n => by
    rw [descentChain]
    split
    · simpa using descentChain_length N q k (descend N q n)
    · simp

/-- Every step of the descent decreases the point and is an admissible edge. -/
theorem descentChain_chain (N q : ℕ) :
    ∀ (k n : ℕ), n < N →
      List.Chain (fun n m ↦ m < n ∧ Admissible N m n) n (descentChain N q k n)
  | 0, _, _ => by simp [descentChain, List.Chain.nil]
  | (k + 1), n, hn => by
    rw [descentChain]
    split
    · rename_i hq
      refine List.Chain.cons ⟨descend_lt hq hn, admissible_descend N q n⟩ ?_
      exact descentChain_chain N q k _ ((descend_lt hq hn).trans hn)
    · exact List.Chain.nil

/-- The descent is in particular a strictly decreasing chain. -/
theorem descentChain_decreasing (N q k n : ℕ) (hn : n < N) :
    List.Chain (· > ·) n (descentChain N q k n) :=
  List.Chain.imp (fun _ _ h ↦ h.1) (descentChain_chain N q k n hn)

/-- The remaining depth exactly doubles, capped at the barrier depth. -/
theorem sub_descend {N q n : ℕ} (hn : n ≤ N) :
    N - descend N q n = min (N - (q + 1)) (2 * (N - n)) := by
  rw [descend]
  omega

/-- **The descent reaches the barrier.**  If `2 ^ k` doublings of the remaining depth cover the
barrier depth, then `k` greedy steps end at or below `q + 1`. -/
theorem chainEnd_descentChain_le (N q : ℕ) (hqN : q + 1 ≤ N) :
    ∀ (k n : ℕ), n ≤ N → N - (q + 1) ≤ 2 ^ k * (N - n) →
      chainEnd n (descentChain N q k n) ≤ q + 1
  | 0, n, hn, hk => by
    simp only [descentChain, chainEnd]
    simp only [pow_zero, one_mul] at hk
    omega
  | (k + 1), n, hn, hk => by
    rw [descentChain]
    split
    · rename_i hq
      have hn' : descend N q n ≤ N := by rw [descend]; omega
      refine chainEnd_descentChain_le N q hqN k (descend N q n) hn' ?_
      rw [sub_descend hn]
      rcases le_or_gt (N - (q + 1)) (2 * (N - n)) with h | h
      · rw [min_eq_left h]
        exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos k)
      · rw [min_eq_right h.le]
        exact hk.trans (le_of_eq (by ring))
    · rename_i hq
      simpa [chainEnd] using Nat.not_lt.1 hq

/-- **The greedy descent of Lemma 3.2.**  From `n₀ < N`, once `2 ^ k` doublings of the remaining
depth cover the barrier depth, there is a decreasing chain of at most `k` admissible edges that
ends at or below `q + 1`, whose cost is at most the potential increment across it. -/
theorem exists_descent_chain {N q k n₀ : ℕ} {b : ℝ} {g : ℕ → ℝ} (hqN : q + 1 ≤ N)
    (hn : n₀ < N) (hb : 1 / 2 ≤ b) (hlip : ∀ j : ℕ, |g (j + 1) - g j| ≤ 1)
    (hk : N - (q + 1) ≤ 2 ^ k * (N - n₀)) :
    ∃ l : List ℕ, l.length ≤ k ∧
      List.Chain (fun n m ↦ m < n ∧ Admissible N m n) n₀ l ∧
      chainEnd n₀ l ≤ q + 1 ∧
      chainCost g n₀ l ≤
        (potential b N g n₀ - potential b N g (chainEnd n₀ l)) / (1 + 2 * b) :=
  ⟨descentChain N q k n₀, descentChain_length N q k n₀, descentChain_chain N q k n₀ hn,
    chainEnd_descentChain_le N q hqN k n₀ hn.le hk,
    chainCost_le_potential hb hlip n₀ _ (descentChain_decreasing N q k n₀ hn)⟩

end Descent

section Insertion

variable {g h : ℕ → ℝ}

/-- A nonnegative profile that vanishes at the origin gives a zero-cost edge down to `0`. -/
theorem edgeCost_zero_left {n : ℕ} (h0 : g 0 = 0) (hpos : ∀ k, k ≤ n → 0 ≤ g k) :
    edgeCost g 0 n = 0 := by
  have hmin : gMin g 0 n = 0 := by
    refine le_antisymm ?_ (le_gMin (Nat.zero_le n) fun k _ hk ↦ hpos k hk)
    have := gMin_le (g := g) (le_refl 0) (Nat.zero_le n)
    rwa [h0] at this
  rw [edgeCost, hmin, h0, sub_zero]

/-- **Midpoint insertion** (fact 5 of the profile API).  Splitting the edge `[m, n]` at `p`
increases the cost by exactly `g p - max (gMin g m p) (gMin g p n)`. -/
theorem edgeCost_insert {m p n : ℕ} (hmp : m ≤ p) (hpn : p ≤ n) :
    edgeCost g m p + edgeCost g p n
      = edgeCost g m n + (g p - max (gMin g m p) (gMin g p n)) := by
  rw [edgeCost, edgeCost, edgeCost, gMin_eq_min hmp hpn]
  rcases le_total (gMin g m p) (gMin g p n) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
  · rw [min_eq_right hle, max_eq_left hle]
    ring

/-- A uniform perturbation of the profile moves the interval minimum by at most `δ`. -/
theorem gMin_perturb {m n : ℕ} {δ : ℝ} (hmn : m ≤ n) (hδ : ∀ k, |g k - h k| ≤ δ) :
    |gMin g m n - gMin h m n| ≤ δ := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ m)
  have key : ∀ u v : ℕ → ℝ, (∀ k, |u k - v k| ≤ δ) → gMin u m n - gMin v m n ≤ δ := by
    intro u v huv
    obtain ⟨j, hj, hj', hgj⟩ : ∃ j, m ≤ j ∧ j ≤ n ∧ gMin v m n = v j := by
      have hne : (Finset.Icc m n).Nonempty := ⟨m, Finset.mem_Icc.2 ⟨le_rfl, hmn⟩⟩
      rw [gMin, dif_pos hne]
      obtain ⟨j, hjmem, hjeq⟩ := Finset.exists_mem_eq_inf' hne v
      exact ⟨j, (Finset.mem_Icc.1 hjmem).1, (Finset.mem_Icc.1 hjmem).2, hjeq⟩
    have h₁ : gMin u m n ≤ u j := gMin_le hj hj'
    have h₂ : u j - v j ≤ δ := (abs_le.1 (huv j)).2
    rw [hgj]
    linarith
  refine abs_le.2 ⟨?_, key g h hδ⟩
  have := key h g fun k ↦ by rw [abs_sub_comm]; exact hδ k
  linarith

/-- **Perturbation** (fact 6 of the profile API).  A uniform `δ`-perturbation of the profile
changes every edge cost by at most `2δ`. -/
theorem edgeCost_perturb {m n : ℕ} {δ : ℝ} (hmn : m ≤ n) (hδ : ∀ k, |g k - h k| ≤ δ) :
    |edgeCost g m n - edgeCost h m n| ≤ 2 * δ := by
  have h₁ := abs_le.1 (hδ m)
  have h₂ := abs_le.1 (gMin_perturb hmn hδ)
  rw [edgeCost, edgeCost]
  refine abs_le.2 ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩

end Insertion

section ZeroCost

variable {g : ℕ → ℝ}

/-- Shrinking an interval from the left cannot lower its minimum. -/
theorem gMin_le_gMin_of_le {m j n : ℕ} (hmj : m ≤ j) (hjn : j ≤ n) :
    gMin g m n ≤ gMin g j n :=
  le_gMin hjn fun k hk hk' ↦ gMin_le (hmj.trans hk) hk'

/-- The leftmost point of `[m, n]` at which `g` attains its minimum. -/
def argMinLeft (g : ℕ → ℝ) (m n : ℕ) : ℕ :=
  if h : ((Finset.Icc m n).filter fun k ↦ g k = gMin g m n).Nonempty then
    ((Finset.Icc m n).filter fun k ↦ g k = gMin g m n).min' h
  else m

theorem argMinLeft_spec {m n : ℕ} (hmn : m ≤ n) :
    m ≤ argMinLeft g m n ∧ argMinLeft g m n ≤ n ∧ g (argMinLeft g m n) = gMin g m n := by
  have hne : ((Finset.Icc m n).filter fun k ↦ g k = gMin g m n).Nonempty := by
    have hIcc : (Finset.Icc m n).Nonempty := ⟨m, Finset.mem_Icc.2 ⟨le_rfl, hmn⟩⟩
    obtain ⟨j, hjmem, hjeq⟩ := Finset.exists_mem_eq_inf' hIcc g
    refine ⟨j, Finset.mem_filter.2 ⟨hjmem, ?_⟩⟩
    rw [gMin, dif_pos hIcc, ← hjeq]
  rw [argMinLeft, dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  obtain ⟨hIcc, heq⟩ := Finset.mem_filter.1 hmem
  exact ⟨(Finset.mem_Icc.1 hIcc).1, (Finset.mem_Icc.1 hIcc).2, heq⟩

theorem argMinLeft_le_of_eq {m n k : ℕ} (hmn : m ≤ n) (hk : m ≤ k) (hk' : k ≤ n)
    (heq : g k = gMin g m n) : argMinLeft g m n ≤ k := by
  have hne : ((Finset.Icc m n).filter fun j ↦ g j = gMin g m n).Nonempty :=
    ⟨k, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk, hk'⟩, heq⟩⟩
  rw [argMinLeft, dif_pos hne]
  exact Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk, hk'⟩, heq⟩)

/-- The edge from `n` down to the leftmost minimum of `[m, n]` costs nothing. -/
theorem edgeCost_argMinLeft {m n : ℕ} (hmn : m ≤ n) : edgeCost g (argMinLeft g m n) n = 0 := by
  obtain ⟨hm, hn, heq⟩ := argMinLeft_spec (g := g) hmn
  have hle : gMin g (argMinLeft g m n) n ≤ g (argMinLeft g m n) := gMin_le le_rfl hn
  have hge : g (argMinLeft g m n) ≤ gMin g (argMinLeft g m n) n := by
    rw [heq]; exact gMin_le_gMin_of_le hm hn
  rw [edgeCost, le_antisymm hle hge, sub_self]

/-- If the left endpoint is no higher than the right one, the leftmost minimum comes strictly
before the right endpoint. -/
theorem argMinLeft_lt {m n : ℕ} (hmn : m < n) (hg : g m ≤ g n) : argMinLeft g m n < n := by
  obtain ⟨hm, hn, heq⟩ := argMinLeft_spec (g := g) hmn.le
  rcases lt_or_eq_of_le hn with h | h
  · exact h
  · have hmin_n : g n = gMin g m n := by rw [← heq, h]
    have hmin_le : gMin g m n ≤ g m := gMin_le le_rfl hmn.le
    have hge : g m ≤ gMin g m n := by rw [← hmin_n]; exact hg
    have hgm : g m = gMin g m n := le_antisymm hge hmin_le
    have := argMinLeft_le_of_eq (g := g) hmn.le le_rfl hmn.le hgm
    omega

/-- **The zero-cost region of Lemma 3.2.**  When the left endpoint of an admissible edge is no
higher than the right one, the edge can be replaced by a zero-cost admissible edge that still
descends. -/
theorem exists_zero_cost_edge {N m n : ℕ} (hmn : m < n) (hadm : Admissible N m n)
    (hg : g m ≤ g n) :
    ∃ j, m ≤ j ∧ j < n ∧ Admissible N j n ∧ edgeCost g j n = 0 := by
  refine ⟨argMinLeft g m n, (argMinLeft_spec (g := g) hmn.le).1, argMinLeft_lt hmn hg, ?_,
    edgeCost_argMinLeft hmn.le⟩
  have hm := (argMinLeft_spec (g := g) hmn.le).1
  rw [Admissible] at hadm ⊢
  omega

end ZeroCost

section Greedy

open scoped Classical

variable {g : ℕ → ℝ}

/-- The admissible zero-cost jumps available from `n` at scale `N`. -/
def jumpSet (g : ℕ → ℝ) (N n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun j ↦ Admissible N j n ∧ edgeCost g j n = 0

theorem mem_jumpSet {N n j : ℕ} :
    j ∈ jumpSet g N n ↔ j < n ∧ Admissible N j n ∧ edgeCost g j n = 0 := by
  simp [jumpSet, Finset.mem_filter, Finset.mem_range, and_assoc]

/-- The greedy step: the *smallest* admissible zero-cost jump from `n`. -/
def bestJump (g : ℕ → ℝ) (N n : ℕ) : ℕ :=
  if h : (jumpSet g N n).Nonempty then (jumpSet g N n).min' h else 0

theorem bestJump_mem {N n : ℕ} (h : (jumpSet g N n).Nonempty) :
    bestJump g N n ∈ jumpSet g N n := by
  rw [bestJump, dif_pos h]
  exact Finset.min'_mem _ h

theorem bestJump_le {N n j : ℕ} (h : j ∈ jumpSet g N n) : bestJump g N n ≤ j := by
  rw [bestJump, dif_pos ⟨j, h⟩]
  exact Finset.min'_le _ _ h

theorem bestJump_lt {N n : ℕ} (h : (jumpSet g N n).Nonempty) : bestJump g N n < n :=
  (mem_jumpSet.1 (bestJump_mem h)).1

theorem edgeCost_bestJump {N n : ℕ} (h : (jumpSet g N n).Nonempty) :
    edgeCost g (bestJump g N n) n = 0 :=
  (mem_jumpSet.1 (bestJump_mem h)).2.2

/-- **Two greedy steps more than double the remaining depth.**  This is the edge count of
Lemma 3.2, obtained from minimality instead of from a separate merging pass: if the second jump
were still admissible from `n`, the first jump would not have been the smallest one. -/
theorem two_step_double {N n : ℕ} (hn : n ≤ N)
    (h₁ : (jumpSet g N n).Nonempty) (h₂ : (jumpSet g N (bestJump g N n)).Nonempty) :
    2 * (N - n) < N - bestJump g N (bestJump g N n) := by
  set j₁ := bestJump g N n with hj₁
  set j₂ := bestJump g N j₁ with hj₂
  have hj₁n : j₁ < n := bestJump_lt h₁
  have hj₂j₁ : j₂ < j₁ := bestJump_lt h₂
  have hc₁ : edgeCost g j₁ n = 0 := edgeCost_bestJump h₁
  have hc₂ : edgeCost g j₂ j₁ = 0 := edgeCost_bestJump h₂
  have hmerge : edgeCost g j₂ n = 0 :=
    edgeCost_merge_of_zero hj₂j₁.le hj₁n.le hc₂ hc₁
  have hnot : ¬ Admissible N j₂ n := by
    intro hadm
    have : j₂ ∈ jumpSet g N n := mem_jumpSet.2 ⟨hj₂j₁.trans hj₁n, hadm, hmerge⟩
    have := bestJump_le this
    omega
  rw [Admissible] at hnot
  omega

/-- Below the midpoint, the jump straight to the origin is admissible and free. -/
theorem jumpSet_nonempty_of_le_half {N n : ℕ} (hn : 0 < n) (h2n : 2 * n ≤ N)
    (h0 : g 0 = 0) (hpos : ∀ k, k ≤ n → 0 ≤ g k) : (jumpSet g N n).Nonempty :=
  ⟨0, mem_jumpSet.2 ⟨hn, by rw [Admissible]; omega, edgeCost_zero_left h0 hpos⟩⟩

/-- Above the midpoint, where the potential is nonpositive, the leftmost minimum of
`[2n - N, n]` is an admissible zero-cost jump. -/
theorem jumpSet_nonempty_of_potential_nonpos {N n : ℕ} {b : ℝ} (hn : N < 2 * n) (hnN : n < N)
    (hL : potential b N g n ≤ 0) (hupper : ∀ k, k ≤ N → g k ≤ b * k) :
    (jumpSet g N n).Nonempty := by
  have hm_lt : 2 * n - N < n := by omega
  have hadm : Admissible N (2 * n - N) n := by rw [Admissible]; omega
  have hcast : ((2 * n - N : ℕ) : ℝ) = 2 * (n : ℝ) - N := by
    have : (N : ℕ) ≤ 2 * n := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hgm : g (2 * n - N) ≤ g n := by
    have h1 : g (2 * n - N) ≤ b * ((2 * n - N : ℕ) : ℝ) := hupper _ (by omega)
    rw [potential] at hL
    rw [hcast] at h1
    linarith
  obtain ⟨j, _, hjn, hjadm, hjcost⟩ := exists_zero_cost_edge hm_lt hadm hgm
  exact ⟨j, mem_jumpSet.2 ⟨hjn, hjadm, hjcost⟩⟩

/-- The greedy zero-cost chain: at most `k` smallest admissible zero-cost jumps. -/
def greedyChain (g : ℕ → ℝ) (N : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | (k + 1), n =>
      if h : (jumpSet g N n).Nonempty then
        bestJump g N n :: greedyChain g N k (bestJump g N n)
      else []

theorem greedyChain_length (g : ℕ → ℝ) (N : ℕ) : ∀ (k n : ℕ), (greedyChain g N k n).length ≤ k
  | 0, _ => by simp [greedyChain]
  | (k + 1), n => by
    rw [greedyChain]
    split
    · simpa using greedyChain_length g N k (bestJump g N n)
    · simp

/-- Every greedy step decreases the point and is an admissible edge. -/
theorem greedyChain_chain (g : ℕ → ℝ) (N : ℕ) :
    ∀ (k n : ℕ), List.Chain (fun n m ↦ m < n ∧ Admissible N m n) n (greedyChain g N k n)
  | 0, _ => by simp [greedyChain, List.Chain.nil]
  | (k + 1), n => by
    rw [greedyChain]
    split
    · rename_i h
      exact List.Chain.cons ⟨bestJump_lt h, (mem_jumpSet.1 (bestJump_mem h)).2.1⟩
        (greedyChain_chain g N k _)
    · exact List.Chain.nil

/-- The greedy chain is free. -/
theorem chainCost_greedyChain (g : ℕ → ℝ) (N : ℕ) :
    ∀ (k n : ℕ), chainCost g n (greedyChain g N k n) = 0
  | 0, _ => by simp [greedyChain, chainCost]
  | (k + 1), n => by
    rw [greedyChain]
    split
    · rename_i h
      have : chainCost g n (bestJump g N n :: greedyChain g N k (bestJump g N n))
          = edgeCost g (bestJump g N n) n
            + chainCost g (bestJump g N n) (greedyChain g N k (bestJump g N n)) := rfl
      rw [this, edgeCost_bestJump h, chainCost_greedyChain g N k (bestJump g N n), add_zero]
    · simp [chainCost]

theorem jumpSet_zero_eq_empty (g : ℕ → ℝ) (N : ℕ) : jumpSet g N 0 = ∅ := by
  ext j
  simp [mem_jumpSet]

/-- **The greedy chain reaches the origin.**  If an admissible zero-cost jump exists from every
positive point, then `2m` greedy steps suffice as soon as `2 ^ m` doublings of the remaining
depth cover `N`: two steps more than double the depth, and the depth cannot exceed `N`. -/
theorem chainEnd_greedyChain_eq_zero {N : ℕ} (g : ℕ → ℝ) :
    ∀ (m n : ℕ), n ≤ N → (∀ k, 0 < k → k ≤ n → (jumpSet g N k).Nonempty) →
      N ≤ 2 ^ m * (N - n) → chainEnd n (greedyChain g N (2 * m) n) = 0
  | 0, n, hn, _, hk => by
    have hn0 : n = 0 := by
      simp only [pow_zero, one_mul] at hk
      omega
    subst hn0
    simp [greedyChain, chainEnd]
  | (m + 1), n, hn, hjump, hk => by
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, greedyChain,
        dif_neg (by simp [jumpSet_zero_eq_empty])]
      rfl
    have h₁ := hjump n hn0 le_rfl
    set j₁ := bestJump g N n with hj₁
    have hj₁n : j₁ < n := bestJump_lt h₁
    have hstep : greedyChain g N (2 * (m + 1)) n = j₁ :: greedyChain g N (2 * m + 1) j₁ := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, greedyChain, dif_pos h₁]
    rcases Nat.eq_zero_or_pos j₁ with hj₁0 | hj₁0
    · have hzero : greedyChain g N (2 * m + 1) j₁ = [] := by
        rw [hj₁0, greedyChain, dif_neg (by simp [jumpSet_zero_eq_empty])]
      rw [hstep, chainEnd, hzero, chainEnd, hj₁0]
    have h₂ := hjump j₁ hj₁0 hj₁n.le
    set j₂ := bestJump g N j₁ with hj₂
    have hdouble : 2 * (N - n) < N - j₂ := two_step_double hn h₁ h₂
    have hstep₂ : greedyChain g N (2 * m + 1) j₁ = j₂ :: greedyChain g N (2 * m) j₂ := by
      rw [greedyChain, dif_pos h₂]
    have hj₂N : j₂ ≤ N := ((bestJump_lt h₂).le.trans hj₁n.le).trans hn
    have hk' : N ≤ 2 ^ m * (N - j₂) := by
      refine hk.trans ?_
      have : 2 ^ (m + 1) * (N - n) = 2 ^ m * (2 * (N - n)) := by ring
      rw [this]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [hstep, chainEnd, hstep₂, chainEnd]
    have hj₂n : j₂ < n := (bestJump_lt h₂).trans hj₁n
    exact chainEnd_greedyChain_eq_zero g m j₂ hj₂N
      (fun k hk0 hkj ↦ hjump k hk0 (hkj.trans hj₂n.le)) hk'

/-- **The free descent of Lemma 3.2.**  In the region where the potential is nonpositive, a
nonnegative profile below its upper barrier admits a zero-cost admissible chain from `n₀` all
the way to the origin, using at most `2m` edges whenever `2 ^ m` doublings of the remaining
depth cover `N`. -/
theorem exists_free_chain {N n₀ m : ℕ} {b : ℝ} {g : ℕ → ℝ}
    (h0 : g 0 = 0) (hnonneg : ∀ k, k ≤ N → 0 ≤ g k) (hupper : ∀ k, k ≤ N → g k ≤ b * k)
    (hL : ∀ k, k ≤ n₀ → potential b N g k ≤ 0) (hn₀ : n₀ < N)
    (hm : N ≤ 2 ^ m * (N - n₀)) :
    ∃ l : List ℕ, l.length ≤ 2 * m ∧
      List.Chain (fun n m ↦ m < n ∧ Admissible N m n) n₀ l ∧
      chainEnd n₀ l = 0 ∧ chainCost g n₀ l = 0 := by
  have hjump : ∀ k, 0 < k → k ≤ n₀ → (jumpSet g N k).Nonempty := by
    intro k hk0 hkn
    rcases le_or_gt (2 * k) N with h | h
    · exact jumpSet_nonempty_of_le_half hk0 h h0 fun j hj ↦ hnonneg j (by omega)
    · exact jumpSet_nonempty_of_potential_nonpos (b := b) h (by omega) (hL k hkn) hupper
  exact ⟨greedyChain g N (2 * m) n₀, greedyChain_length g N (2 * m) n₀,
    greedyChain_chain g N (2 * m) n₀,
    chainEnd_greedyChain_eq_zero g m n₀ hn₀.le hjump hm,
    chainCost_greedyChain g N (2 * m) n₀⟩

end Greedy

section Concat

variable {g : ℕ → ℝ} {b : ℝ}

theorem chainEnd_append : ∀ (n : ℕ) (l₁ l₂ : List ℕ),
    chainEnd n (l₁ ++ l₂) = chainEnd (chainEnd n l₁) l₂
  | _, [], _ => rfl
  | _, m :: rest, l₂ => by
    simpa [chainEnd] using chainEnd_append m rest l₂

theorem chainCost_append (g : ℕ → ℝ) : ∀ (n : ℕ) (l₁ l₂ : List ℕ),
    chainCost g n (l₁ ++ l₂) = chainCost g n l₁ + chainCost g (chainEnd n l₁) l₂
  | _, [], _ => by simp [chainCost, chainEnd]
  | n, m :: rest, l₂ => by
    have h : chainCost g n (m :: (rest ++ l₂))
        = edgeCost g m n + chainCost g m (rest ++ l₂) := rfl
    have h' : chainCost g n (m :: rest) = edgeCost g m n + chainCost g m rest := rfl
    simp only [List.cons_append, h, h', chainEnd]
    rw [chainCost_append g m rest l₂]
    ring

theorem chain_append {R : ℕ → ℕ → Prop} : ∀ (n : ℕ) (l₁ l₂ : List ℕ),
    List.Chain R n l₁ → List.Chain R (chainEnd n l₁) l₂ → List.Chain R n (l₁ ++ l₂)
  | _, [], _, _, h₂ => by simpa [chainEnd] using h₂
  | n, m :: rest, l₂, h₁, h₂ => by
    obtain ⟨hnm, hrest⟩ := List.chain_cons.1 h₁
    exact List.Chain.cons hnm (chain_append m rest l₂ hrest (by simpa [chainEnd] using h₂))

/-- The potential is nondecreasing along the grid. -/
theorem potential_mono {N : ℕ} (hb : 1 / 2 ≤ b) (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) :
    Monotone (potential b N g) := by
  refine monotone_nat_of_le_succ fun k ↦ ?_
  simpa [potential] using potential_monotone (g := g) (b := b) N hb hlip k

/-- A single grid step costs at most one, for a 1-Lipschitz profile. -/
theorem edgeCost_succ_le_one {k : ℕ} (hlip : ∀ j : ℕ, |g (j + 1) - g j| ≤ 1) :
    edgeCost g k (k + 1) ≤ 1 := by
  have h := abs_le.1 (hlip k)
  have hmin : min (g k) (g (k + 1)) ≤ gMin g k (k + 1) := by
    refine le_gMin (Nat.le_succ k) fun j hj hj' ↦ ?_
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have hjk : j = k := by omega
      subst hjk
      exact min_le_left _ _
    · have hjk : j = k + 1 := by omega
      subst hjk
      exact min_le_right _ _
  rcases le_total (g k) (g (k + 1)) with hle | hle
  · rw [min_eq_left hle] at hmin
    have : gMin g k (k + 1) ≤ g k := gMin_le le_rfl (Nat.le_succ k)
    rw [edgeCost]
    linarith [le_antisymm this hmin]
  · rw [min_eq_right hle] at hmin
    rw [edgeCost]
    linarith [h.1, h.2]

end Concat

section LemmaThreeTwo

variable {g : ℕ → ℝ} {b : ℝ}

/-- **Lemma 3.2, in its finite form.**  Below the barrier `q`, where the potential is already
nonpositive, the greedy descent from `n₀` joins the free descent to the origin across at most one
unit edge.  The resulting admissible chain has at most `m + 2m' + 1` edges and costs at most the
full potential difference plus one.

The manuscript states the cost as `(bN - g N) / (1 + 2b) + 3`; the potential form proved here is
what the argument actually uses, and it avoids the continuous rescaling step. -/
theorem exists_chain_to_zero {N n₀ q m m' : ℕ}
    (hb : 1 / 2 ≤ b) (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1)
    (h0 : g 0 = 0) (hnonneg : ∀ k, k ≤ N → 0 ≤ g k) (hupper : ∀ k, k ≤ N → g k ≤ b * k)
    (hn₀ : n₀ < N) (hq : q + 2 ≤ N) (hqL : potential b N g q ≤ 0)
    (hm : N - (q + 1) ≤ 2 ^ m * (N - n₀)) (hm' : N ≤ 2 ^ m' * (N - q)) :
    ∃ l : List ℕ, l.length ≤ m + 2 * m' + 1 ∧
      List.Chain (fun n k ↦ k < n ∧ Admissible N k n) n₀ l ∧
      chainEnd n₀ l = 0 ∧
      chainCost g n₀ l ≤ (potential b N g n₀ - potential b N g 0) / (1 + 2 * b) + 1 := by
  have hpos : (0 : ℝ) < 1 + 2 * b := by linarith
  have hmono := potential_mono (N := N) (g := g) (b := b) hb hlip
  obtain ⟨l₁, hlen₁, hchain₁, hend₁, hcost₁⟩ :=
    exists_descent_chain (N := N) (q := q) (k := m) (n₀ := n₀) (b := b) (g := g)
      (by omega) hn₀ hb hlip hm
  have hcost₁' : chainCost g n₀ l₁
      ≤ (potential b N g n₀ - potential b N g 0) / (1 + 2 * b) := by
    refine hcost₁.trans ((div_le_div_iff_of_pos_right hpos).2 ?_)
    have := hmono (Nat.zero_le (chainEnd n₀ l₁))
    linarith
  rcases Nat.eq_zero_or_pos (chainEnd n₀ l₁) with hp0 | hp0
  · exact ⟨l₁, by omega, hchain₁, hp0, by linarith⟩
  by_cases hpq : chainEnd n₀ l₁ = q + 1
  · -- one unit edge across the barrier, then the free descent
    have hqN : q < N := by omega
    have hqL' : ∀ k, k ≤ q → potential b N g k ≤ 0 := fun k hk ↦ (hmono hk).trans hqL
    obtain ⟨l₂, hlen₂, hchain₂, hend₂, hcost₂⟩ :=
      exists_free_chain (N := N) (n₀ := q) (m := m') (b := b) (g := g) h0 hnonneg hupper
        hqL' hqN hm'
    refine ⟨l₁ ++ q :: l₂, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · refine chain_append n₀ l₁ _ hchain₁ ?_
      rw [hpq]
      exact List.Chain.cons ⟨by omega, by rw [Admissible]; omega⟩ hchain₂
    · rw [chainEnd_append, hpq]
      simpa [chainEnd] using hend₂
    · rw [chainCost_append]
      have hstep : chainCost g (chainEnd n₀ l₁) (q :: l₂)
          = edgeCost g q (chainEnd n₀ l₁) + chainCost g q l₂ := rfl
      rw [hstep, hcost₂, hpq, add_zero]
      have := edgeCost_succ_le_one (g := g) (k := q) hlip
      linarith
  · -- already below the barrier: descend freely
    have hpq' : chainEnd n₀ l₁ ≤ q := by omega
    have hpN : chainEnd n₀ l₁ < N := by omega
    have hpL : ∀ k, k ≤ chainEnd n₀ l₁ → potential b N g k ≤ 0 := fun k hk ↦
      (hmono (hk.trans hpq')).trans hqL
    have hm'' : N ≤ 2 ^ m' * (N - chainEnd n₀ l₁) :=
      hm'.trans (Nat.mul_le_mul_left _ (by omega))
    obtain ⟨l₂, hlen₂, hchain₂, hend₂, hcost₂⟩ :=
      exists_free_chain (N := N) (n₀ := chainEnd n₀ l₁) (m := m') (b := b) (g := g) h0 hnonneg
        hupper hpL hpN hm''
    refine ⟨l₁ ++ l₂, ?_, chain_append n₀ l₁ l₂ hchain₁ hchain₂, ?_, ?_⟩
    · simp only [List.length_append]
      omega
    · rw [chainEnd_append]
      exact hend₂
    · rw [chainCost_append, hcost₂, add_zero]
      linarith

end LemmaThreeTwo

section Endpoint

variable {g : ℕ → ℝ} {a : ℝ}

/-- A 1-Lipschitz grid profile cannot drop faster than the grid distance. -/
theorem sub_le_of_lipschitz {m n : ℕ} (hmn : m ≤ n) (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) :
    g m - g n ≤ (n : ℝ) - (m : ℝ) := by
  have htel : ∑ k ∈ Finset.Ico m n, (g (k + 1) - g k) = g n - g m := by
    rw [Finset.sum_Ico_eq_sub _ hmn]
    simp [Finset.sum_range_sub fun i ↦ g i]
  have hbound : ∀ k ∈ Finset.Ico m n, -(1 : ℝ) ≤ g (k + 1) - g k := fun k _ ↦
    (abs_le.1 (hlip k)).1
  have hsum := Finset.sum_le_sum hbound
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, htel, Nat.cast_sub hmn] at hsum
  linarith

/-- The parabolic endpoint estimate: a value above both the linear barrier `a x` and the
Lipschitz cone `v - (x - l)` is at least `a (v + l) / (1 + a)`. -/
theorem barrier_cone_le {v x l G : ℝ} (ha : 0 < a) (h1 : a * x ≤ G) (h2 : v - (x - l) ≤ G) :
    a * (v + l) / (1 + a) ≤ G := by
  have hpos : (0 : ℝ) < 1 + a := by linarith
  rw [div_le_iff₀ hpos]
  rcases le_or_gt ((v + l) / (1 + a)) x with h | h
  · have hx : v + l ≤ x * (1 + a) := by rwa [div_le_iff₀ hpos] at h
    have e1 : a * (v + l) ≤ a * (x * (1 + a)) := mul_le_mul_of_nonneg_left hx ha.le
    have e2 : a * x * (1 + a) ≤ G * (1 + a) := mul_le_mul_of_nonneg_right h1 hpos.le
    nlinarith [e1, e2]
  · have hx : x * (1 + a) < v + l := by rwa [lt_div_iff₀ hpos] at h
    have e2 : (v - (x - l)) * (1 + a) ≤ G * (1 + a) := mul_le_mul_of_nonneg_right h2 hpos.le
    nlinarith [e2, hx]

/-- **Lemma 3.3, the insertion estimate.**  Inserting the point `l` into an edge that crosses it
raises the cost by at most `(g l - a * l) / (1 + a)`, for a profile above the barrier `a x`. -/
theorem insert_cost_le {m l n : ℕ} (ha : 0 < a) (hml : m ≤ l) (hln : l ≤ n)
    (hlip : ∀ k : ℕ, |g (k + 1) - g k| ≤ 1) (hlower : ∀ k : ℕ, a * k ≤ g k) :
    edgeCost g m l + edgeCost g l n - edgeCost g m n ≤ (g l - a * l) / (1 + a) := by
  have hpos : (0 : ℝ) < 1 + a := by linarith
  have hA₁ : a * (g l + l) / (1 + a) ≤ gMin g l n := by
    refine le_gMin hln fun x hx hx' ↦ ?_
    refine barrier_cone_le (a := a) (v := g l) (x := (x : ℝ)) (l := (l : ℝ)) ha (hlower x) ?_
    have := sub_le_of_lipschitz (g := g) hx hlip
    linarith
  have hins := edgeCost_insert (g := g) hml hln
  have hmax : gMin g l n ≤ max (gMin g m l) (gMin g l n) := le_max_right _ _
  have hstep : edgeCost g m l + edgeCost g l n - edgeCost g m n
      = g l - max (gMin g m l) (gMin g l n) := by linarith [hins]
  rw [hstep]
  have hfinal : g l - max (gMin g m l) (gMin g l n) ≤ g l - a * (g l + l) / (1 + a) := by
    have : a * (g l + l) / (1 + a) ≤ max (gMin g m l) (gMin g l n) := hA₁.trans hmax
    linarith
  refine hfinal.trans (le_of_eq ?_)
  field_simp
  ring

end Endpoint

end FalconerPacking
