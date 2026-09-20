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

end FalconerPacking
