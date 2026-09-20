/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.FrostmanWeights
import FalconerPacking.Restriction

/-!
# From Frostman weights to measures

The finite Frostman construction produces weights on the occupied cubes of one generation.  This
file turns them into an actual measure — a finite sum of point masses, one in each occupied cube
— and transfers the combinatorial bounds:

* the mass of a dyadic cube of any generation `i ≤ n` is exactly the combinatorial `cubeMass`;
* hence every such cube stays within its allowance;
* hence, through the cube-to-ball bridge, balls of radius at most `2⁻ⁿ⁻¹` satisfy a Frostman
  bound with constant `4`;
* and the total mass is the total weight.

What remains for the classical Frostman lemma is the weak limit as `n → ∞`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The measure carried by a weight assignment: one point mass in each occupied cube. -/
def weightMeasure (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → Plane) (w : (Fin 2 → ℤ) → ℝ) :
    Measure Plane :=
  ∑ k' ∈ S, ENNReal.ofReal (w k') • Measure.dirac (pt k')

theorem weightMeasure_apply (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → Plane)
    (w : (Fin 2 → ℤ) → ℝ) {A : Set Plane} (hA : MeasurableSet A) :
    weightMeasure S pt w A = ∑ k' ∈ S, if pt k' ∈ A then ENNReal.ofReal (w k') else 0 := by
  classical
  rw [weightMeasure, Measure.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k' _ ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  by_cases h : pt k' ∈ A <;> simp [h]

/-- The total mass is the total weight. -/
theorem weightMeasure_univ (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → Plane)
    {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) :
    weightMeasure S pt w univ = ENNReal.ofReal (∑ k' ∈ S, w k') := by
  rw [weightMeasure_apply _ _ _ MeasurableSet.univ,
    ENNReal.ofReal_sum_of_nonneg fun k' _ ↦ hw k']
  exact Finset.sum_congr rfl fun k' _ ↦ by simp

section CubeMass

variable {S : Finset (Fin 2 → ℤ)} {n : ℕ} {pt : (Fin 2 → ℤ) → Plane} {w : (Fin 2 → ℤ) → ℝ}

/-- A chosen point of an occupied cube lies in a cube of a coarser generation exactly when that
cube is its ancestor. -/
theorem mem_dyadicCube_iff_ancestor {i : ℕ} (hin : i ≤ n) {k' c : Fin 2 → ℤ}
    (hpt : pt k' ∈ dyadicCube n k') :
    pt k' ∈ dyadicCube i c ↔ ancestor (n - i) k' = c := by
  constructor
  · intro hmem
    have hanc : pt k' ∈ dyadicCube i (ancestor (n - i) k') := by
      have harith : i + (n - i) = n := by omega
      have := dyadicCube_subset_ancestor i (n - i) k'
      rw [harith] at this
      exact this hpt
    by_contra hne
    exact absurd (mem_dyadicCube_iff.1 hmem) (by
      rw [mem_dyadicCube_iff.1 hanc] at *
      exact fun h ↦ hne h)
  · intro hanc
    have harith : i + (n - i) = n := by omega
    have hsub := dyadicCube_subset_ancestor i (n - i) k'
    rw [harith] at hsub
    rw [← hanc]
    exact hsub hpt

/-- **The measure of a dyadic cube is its combinatorial mass.** -/
theorem weightMeasure_dyadicCube (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k') {i : ℕ} (hin : i ≤ n) (c : Fin 2 → ℤ) :
    weightMeasure S pt w (dyadicCube i c) = ENNReal.ofReal (cubeMass S n i w c) := by
  classical
  rw [weightMeasure_apply _ _ _ (measurableSet_dyadicCube i c), cubeMass,
    ENNReal.ofReal_sum_of_nonneg fun k' _ ↦ hw k']
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k' hk' ↦ ?_
  by_cases hmem : pt k' ∈ dyadicCube i c
  · rw [if_pos hmem, if_pos ((mem_dyadicCube_iff_ancestor hin (hpt k' hk')).1 hmem)]
  · rw [if_neg hmem, if_neg (fun h ↦ hmem ((mem_dyadicCube_iff_ancestor hin (hpt k' hk')).2 h))]

/-- The measure obeys the allowance of every generation. -/
theorem weightMeasure_dyadicCube_le {d : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) {i : ℕ} (hin : i ≤ n)
    (c : Fin 2 → ℤ) :
    weightMeasure S pt w (dyadicCube i c) ≤ ENNReal.ofReal (allowance i d) := by
  rw [weightMeasure_dyadicCube hw hpt hin c]
  exact ENNReal.ofReal_le_ofReal (hbound i hin c)

/-- **A Frostman bound on balls.**  Through the four-cube bridge, the measure of a ball of radius
at most `2⁻ⁿ⁻¹` is at most `4` times the allowance of generation `n`. -/
theorem weightMeasure_ball_le {d : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) (x : Plane) {r : ℝ}
    (hr : 0 < r) (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    weightMeasure S pt w (Metric.ball x r) ≤ 4 * ENNReal.ofReal (allowance n d) :=
  measure_ball_le_of_cube_bound hr hrn fun k ↦
    weightMeasure_dyadicCube_le hw hpt hbound le_rfl k

end CubeMass

end FalconerPacking
