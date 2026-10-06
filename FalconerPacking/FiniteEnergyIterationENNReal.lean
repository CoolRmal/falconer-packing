/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.ENNReal.Operations
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# Finite nonnegative energy iteration

The extended formulation applies directly to the localized Lebesgue energies, without
first proving finiteness or converting infinite integrals to real numbers.
-/

@[expose] public section

open scoped ENNReal

namespace FalconerPacking

/-- The exact finite recurrence keeps one threshold per edge and preceding factors on errors. -/
theorem finite_energy_iteration_ennreal (E A e : ℕ → ℝ≥0∞) (K : ℕ)
    (hstep : ∀ j < K, E j ≤ A j * E (j + 1) + e j) :
    E 0 ≤ (∏ j ∈ Finset.range K, A j) * E K +
      ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * e j := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hpre := ih (fun j hj ↦ hstep j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ (∏ j ∈ Finset.range K, A j) * E K +
          ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * e j := hpre
      _ ≤ (∏ j ∈ Finset.range K, A j) * (A K * E (K + 1) + e K) +
          ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * e j := by
        gcongr
        exact hstep K (Nat.lt_succ_self K)
      _ = _ := by rw [Finset.prod_range_succ, Finset.sum_range_succ]; ring

end FalconerPacking
