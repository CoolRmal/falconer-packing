/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AngularGridGeometry
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Explicit smooth angular weights

Unit-circle bumps cover all nonzero directions. Normalizing their finite sum gives
actual nonnegative smooth angular weights with a fixed overlap bound.
-/

@[expose] public section

noncomputable section

open Set Metric Filter Classical
open scoped ContDiff

namespace FalconerPacking

/-- The explicit direction bump for the j-th equal angular grid point. -/
def angularCapBump (N : ℕ) (hN : 0 < N) (j : ℕ) :
    ContDiffBump (angularDirection (angularGridPoint N j)) :=
  ⟨2 * Real.pi / N, 2 * (2 * Real.pi / N), by positivity,
    by
      have h : 0 < 2 * Real.pi / (N : ℝ) := by positivity
      linarith⟩

/-- The normalizing sum, evaluated on the actual direction of the frequency. -/
def angularCapDenominator (N : ℕ) (hN : 0 < N)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ j ∈ Finset.range N, angularCapBump N hN j (‖ξ‖⁻¹ • ξ)

/-- Actual smooth angular weights away from the origin. -/
def angularCapWeight (N : ℕ) (hN : 0 < N) (j : ℕ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  angularCapBump N hN j (‖ξ‖⁻¹ • ξ) / angularCapDenominator N hN ξ

/-- Some explicit bump equals one at every nonzero frequency direction. -/
theorem exists_angularCapBump_eq_one (N : ℕ) (hN : 0 < N)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) :
    ∃ j ∈ Finset.range N, angularCapBump N hN j (‖ξ‖⁻¹ • ξ) = 1 := by
  have hθ := radialAngle_mem ξ 0
  rw [← biUnion_angularGridCell hN] at hθ
  obtain ⟨j, hj, hθ⟩ := mem_iUnion₂.mp hθ
  refine ⟨j, hj, (angularCapBump N hN j).one_of_mem_closedBall ?_⟩
  have hd := circleGridCell_dist_le (by norm_num : (0 : ℝ) ≤ 1) hθ
  simpa only [one_smul, one_mul, angularDirection_radialAngle hξ, sub_zero,
    angularCapBump, mem_closedBall] using hd

/-- The denominator is bounded below uniformly away from the origin. -/
theorem one_le_angularCapDenominator (N : ℕ) (hN : 0 < N)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) :
    1 ≤ angularCapDenominator N hN ξ := by
  obtain ⟨j, hj, he⟩ := exists_angularCapBump_eq_one N hN hξ
  rw [← he]
  exact Finset.single_le_sum (fun i _ ↦ (angularCapBump N hN i).nonneg) hj

theorem angularCapDenominator_nonneg (N : ℕ) (hN : 0 < N)
    (ξ : EuclideanSpace ℝ (Fin 2)) : 0 ≤ angularCapDenominator N hN ξ :=
  Finset.sum_nonneg (fun j _ ↦ (angularCapBump N hN j).nonneg)

theorem angularCapWeight_nonneg (N : ℕ) (hN : 0 < N) (j : ℕ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : 0 ≤ angularCapWeight N hN j ξ :=
  div_nonneg (angularCapBump N hN j).nonneg (angularCapDenominator_nonneg N hN ξ)

/-- No weight exceeds one, even at the origin under the totalized division convention. -/
theorem angularCapWeight_le_one (N : ℕ) (hN : 0 < N) {j : ℕ} (hj : j < N)
    (ξ : EuclideanSpace ℝ (Fin 2)) : angularCapWeight N hN j ξ ≤ 1 := by
  by_cases hd : angularCapDenominator N hN ξ = 0
  · simp [angularCapWeight, hd]
  · apply (div_le_one (lt_of_le_of_ne (angularCapDenominator_nonneg N hN ξ) (Ne.symm hd))).mpr
    exact Finset.single_le_sum (fun i _ ↦ (angularCapBump N hN i).nonneg)
      (Finset.mem_range.mpr hj)

/-- The actual finite weights sum exactly to one at every nonzero frequency. -/
theorem sum_angularCapWeight (N : ℕ) (hN : 0 < N)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) :
    ∑ j ∈ Finset.range N, angularCapWeight N hN j ξ = 1 := by
  simp only [angularCapWeight, ← Finset.sum_div]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (one_le_angularCapDenominator N hN hξ)))

/-- Each weight is smooth at every nonzero frequency, without using an argument chart. -/
theorem contDiffAt_angularCapWeight (N : ℕ) (hN : 0 < N) (j : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) :
    ContDiffAt ℝ ∞ (angularCapWeight N hN j) ξ := by
  have hd : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 2) ↦ ‖x‖⁻¹ • x) ξ :=
    ((contDiffAt_norm ℝ hξ).inv (norm_ne_zero_iff.mpr hξ)).smul contDiffAt_id
  have hb (i : ℕ) : ContDiffAt ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ angularCapBump N hN i (‖x‖⁻¹ • x)) ξ :=
    (angularCapBump N hN i).contDiffAt.comp ξ hd
  exact (hb j).div (ContDiffAt.sum (fun i _ ↦ hb i))
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_angularCapDenominator N hN hξ)))

/-- Nonzero weights lie inside the actual outer direction balls of the explicit bumps. -/
theorem angularCapWeight_direction_support (N : ℕ) (hN : 0 < N) (j : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : angularCapWeight N hN j ξ ≠ 0) :
    ‖ξ‖⁻¹ • ξ ∈ ball (angularDirection (angularGridPoint N j)) (4 * Real.pi / N) := by
  have hb : angularCapBump N hN j (‖ξ‖⁻¹ • ξ) ≠ 0 := by
    intro he
    exact hξ (by simp only [angularCapWeight, he, zero_div])
  rw [← Function.mem_support, (angularCapBump N hN j).support_eq] at hb
  simpa only [angularCapBump, show 2 * (2 * Real.pi / (N : ℝ)) =
    4 * Real.pi / N by ring] using hb

/-- The number of nonzero angular weights has an absolute bound independent of N. -/
theorem card_angularCapWeight_support_le (N : ℕ) (hN : 0 < N)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun j ↦ angularCapWeight N hN j ξ ≠ 0)).card ≤
      Nat.ceil (6 * Real.pi) := by
  have hsub : (Finset.range N).filter (fun j ↦ angularCapWeight N hN j ξ ≠ 0) ⊆
      (Finset.range N).filter (fun j ↦
        ‖ξ‖⁻¹ • ξ ∈ ball (angularDirection (angularGridPoint N j)) (4 * Real.pi / N)) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
      angularCapWeight_direction_support N hN j (Finset.mem_filter.mp hj).2⟩
  apply (Finset.card_le_card hsub).trans
  simpa only [one_smul, mul_one, show 4 * Real.pi + 2 * Real.pi = 6 * Real.pi by ring]
    using card_circle_grid_balls_le N hN (by norm_num : (0 : ℝ) < 1)
      (by positivity : 0 ≤ 4 * Real.pi) (‖ξ‖⁻¹ • ξ)

end FalconerPacking
