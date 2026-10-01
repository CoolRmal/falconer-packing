/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialMomentCenters
import Mathlib.Analysis.MeanInequalities

/-!
# Summing comparisons over children of dyadic cubes

Disjointness bounds the total child mass in a parent. Regrouping then controls the parent
moment terms, while Hölder bounds the sum of square roots of the child masses.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The total mass of selected dyadic children of a given parent is at most the parent mass. -/
theorem sum_dyadic_child_mass_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (I : Finset (Fin 2 → ℤ)) (p : Fin 2 → ℤ) :
    ∑ k ∈ I with ancestor 1 k = p, μ (dyadicCube (n + 1) k) ≤
      μ (dyadicCube n p) := by
  classical
  rw [← measure_biUnion_finset
    (fun _ _ _ _ hne ↦ dyadicCube_disjoint hne)
    (fun k _ ↦ measurableSet_dyadicCube (n + 1) k)]
  apply measure_mono
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
  have hkp := (Finset.mem_filter.mp hk).2
  have hsub := dyadicCube_subset_ancestor n 1 k
  simpa only [hkp] using hsub hxk

/-- Regrouping child masses controls every nonnegative parent weight. -/
theorem sum_dyadic_child_parent_weight_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (I : Finset (Fin 2 → ℤ)) (w : (Fin 2 → ℤ) → ℝ≥0∞) :
    ∑ k ∈ I, μ (dyadicCube (n + 1) k) * w (ancestor 1 k) ≤
      ∑ p ∈ I.image (ancestor 1), μ (dyadicCube n p) * w p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := I) (t := I.image (ancestor 1)) (g := ancestor 1)
    (fun k hk ↦ Finset.mem_image_of_mem _ hk)
    (fun k ↦ μ (dyadicCube (n + 1) k) * w (ancestor 1 k))]
  apply Finset.sum_le_sum
  intro p hp
  calc
    _ = (∑ k ∈ I with ancestor 1 k = p, μ (dyadicCube (n + 1) k)) * w p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ ≤ μ (dyadicCube n p) * w p := mul_le_mul_left (sum_dyadic_child_mass_le μ n I p) _

/-- Square-root masses of a finite subfamily are bounded by the square root of its size. -/
theorem sum_sqrt_dyadic_mass_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (n : ℕ) (I : Finset (Fin 2 → ℤ)) :
    ∑ k ∈ I, μ (dyadicCube n k) ^ (1 / 2 : ℝ) ≤
      (I.card : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
  have hmass : ∑ k ∈ I, μ (dyadicCube n k) ≤ 1 := by
    simpa using sum_measure_le_measure_univ
      (fun k _ ↦ (measurableSet_dyadicCube n k).nullMeasurableSet)
      (fun _ _ _ _ hne ↦ (dyadicCube_disjoint hne).aedisjoint (μ := μ))
  have h := ENNReal.inner_le_Lp_mul_Lq I
    (fun k ↦ μ (dyadicCube n k) ^ (1 / 2 : ℝ)) (fun _ ↦ 1)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
  simp only [mul_one, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  apply h.trans
  have hp := ENNReal.rpow_le_rpow hmass (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [ENNReal.one_rpow, one_mul] using
    mul_le_mul_left hp ((I.card : ℝ≥0∞) ^ (1 / 2 : ℝ))

end FalconerPacking
