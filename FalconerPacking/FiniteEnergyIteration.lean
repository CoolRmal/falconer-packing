/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Finite energy iteration with explicit errors

Each step contributes one threshold factor. The terminal coefficient is their product,
and each additive error is multiplied only by the preceding factors.
-/

@[expose] public section

namespace FalconerPacking

/-- Exact finite iteration of one-factor energy inequalities. -/
theorem finite_energy_iteration (E A e : ℕ → ℝ) (K : ℕ)
    (hA : ∀ j < K, 0 ≤ A j)
    (hstep : ∀ j < K, E j ≤ A j * E (j + 1) + e j) :
    E 0 ≤ (∏ j ∈ Finset.range K, A j) * E K +
      ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * e j := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hpre : 0 ≤ ∏ j ∈ Finset.range K, A j :=
      Finset.prod_nonneg fun j hj ↦ hA j (Nat.lt_succ_of_lt (Finset.mem_range.mp hj))
    have h := ih (fun j hj ↦ hA j (Nat.lt_succ_of_lt hj))
      (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj))
    have hnext := mul_le_mul_of_nonneg_left (hstep K (Nat.lt_succ_self K)) hpre
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    linarith

/-- A uniform polynomial factor bounds the accumulated rapidly decreasing errors. -/
theorem finite_energy_iteration_uniform_error (E A e : ℕ → ℝ) (K : ℕ)
    {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hA : ∀ j < K, 0 ≤ A j) (hAM : ∀ j < K, A j ≤ M)
    (he : ∀ j < K, e j ≤ δ)
    (hstep : ∀ j < K, E j ≤ A j * E (j + 1) + e j) :
    E 0 ≤ (∏ j ∈ Finset.range K, A j) * E K + K * M ^ K * δ := by
  apply (finite_energy_iteration E A e K hA hstep).trans
  apply add_le_add_right
  calc
    _ ≤ ∑ _j ∈ Finset.range K, M ^ K * δ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjK := Finset.mem_range.mp hj
      have hp₀ : 0 ≤ ∏ i ∈ Finset.range j, A i :=
        Finset.prod_nonneg fun i hi ↦ hA i ((Finset.mem_range.mp hi).trans hjK)
      have hp : (∏ i ∈ Finset.range j, A i) ≤ M ^ j := by
        calc
          _ ≤ ∏ _i ∈ Finset.range j, M :=
            Finset.prod_le_prod₀
              (fun i hi ↦ hA i ((Finset.mem_range.mp hi).trans hjK))
              (fun i hi ↦ hAM i ((Finset.mem_range.mp hi).trans hjK))
          _ = _ := by simp
      exact (mul_le_mul_of_nonneg_left (he j hjK) hp₀).trans
        (mul_le_mul_of_nonneg_right (hp.trans (pow_le_pow_right₀ hM hjK.le)) hδ)
    _ = _ := by simp [mul_assoc]

/-- The powers paid on individual edges add exactly, without a label-counting loss. -/
theorem prod_edge_thresholds {ι : Type*} (I : Finset ι)
    (C ε : ℝ) {R : ℝ} (hR : 0 < R) (cost : ι → ℝ) :
    (∏ i ∈ I, C * R ^ (ε + cost i)) =
      C ^ I.card * R ^ (I.card * ε + ∑ i ∈ I, cost i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.rpow_sum_of_pos hR]
  simp [Finset.sum_add_distrib]

end FalconerPacking
