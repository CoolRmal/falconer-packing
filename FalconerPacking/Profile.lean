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

end FalconerPacking
