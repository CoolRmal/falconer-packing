/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.TubePairCounting
import Mathlib.Analysis.MeanInequalities

/-!
# Square-mass bounds for finite tube enlargements

Replacing each tube by a bounded union costs the product of the row and column multiplicities.
This applies to actual finite unions and retains diagonal masses.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- A finite sum has its exact cardinality as the Cauchy--Schwarz loss. -/
theorem ennreal_sq_sum_le_card_mul_sum_sq {ι : Type*}
    (I : Finset ι) (f : ι → ℝ≥0∞) :
    (∑ i ∈ I, f i) ^ 2 ≤ I.card * ∑ i ∈ I, f i ^ 2 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_two, ENNReal.rpow_one] using
    ENNReal.rpow_sum_le_const_mul_sum_rpow (s := I) (f := f) (p := (2 : ℝ)) (by norm_num)

/-- A relation with bounded row and column degrees controls the mass of the corresponding
actual unions without assuming that the original sets are disjoint. -/
theorem sum_measure_finite_expansion_sq_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (I : Finset ι) (S : ι → Set α) (R : ι → ι → Prop)
    (row col : ℕ)
    (hr : ∀ i ∈ I, (I.filter (R i)).card ≤ row)
    (hc : ∀ j ∈ I, (I.filter (fun i ↦ R i j)).card ≤ col) :
    (∑ i ∈ I, μ (⋃ j ∈ I.filter (R i), S j) ^ 2) ≤
      (row : ℝ≥0∞) * col * ∑ j ∈ I, μ (S j) ^ 2 := by
  have hm (i : ι) (hi : i ∈ I) :
      μ (⋃ j ∈ I.filter (R i), S j) ^ 2 ≤
        (row : ℝ≥0∞) * ∑ j ∈ I.filter (R i), μ (S j) ^ 2 := by
    apply (pow_le_pow_left' (measure_biUnion_finset_le _ _) 2).trans
    apply (ennreal_sq_sum_le_card_mul_sum_sq _ _).trans
    exact mul_le_mul' (Nat.cast_le.mpr (hr i hi)) le_rfl
  have he : (∑ i ∈ I, ∑ j ∈ I.filter (R i), μ (S j) ^ 2) =
      ∑ j ∈ I, ((I.filter (fun i ↦ R i j)).card : ℝ≥0∞) * μ (S j) ^ 2 := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ ∑ i ∈ I, (row : ℝ≥0∞) * ∑ j ∈ I.filter (R i), μ (S j) ^ 2 :=
      Finset.sum_le_sum hm
    _ = (row : ℝ≥0∞) *
        ∑ j ∈ I, ((I.filter (fun i ↦ R i j)).card : ℝ≥0∞) * μ (S j) ^ 2 := by
      rw [← Finset.mul_sum, he]
    _ ≤ (row : ℝ≥0∞) * ∑ j ∈ I, (col : ℝ≥0∞) * μ (S j) ^ 2 := by
      apply mul_le_mul' le_rfl
      exact Finset.sum_le_sum fun j hj ↦ mul_le_mul' (Nat.cast_le.mpr (hc j hj)) le_rfl
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

end FalconerPacking
