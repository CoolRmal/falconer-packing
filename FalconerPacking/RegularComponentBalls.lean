/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RegularMeasureProfile
public import FalconerPacking.TruncatedConditionalEnergy

/-!
# Ball masses of actual regularized components

Regularity is used only through the finite trees constructed by finite regularization. An
enlarged conditioning set contains an active cube, which controls its normalization mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Every positive-mass coarse cube of an original component is an ancestor of a selected leaf. -/
theorem exists_leaf_of_normalized_component_cube_pos
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {N n : ℕ} (hn : n ≤ N)
    (A : Finset (Fin 2 → ℤ)) (q : Fin 2 → ℤ)
    (hq : 0 < normalizedRestrict μ (finiteDyadicUnion N A) (dyadicCube n q)) :
    ∃ k ∈ A, ancestor (N - n) k = q := by
  have hinter : μ (dyadicCube n q ∩ finiteDyadicUnion N A) ≠ 0 := by
    intro hz
    rw [normalizedRestrict_apply _ _ _ (measurableSet_dyadicCube n q), hz, mul_zero] at hq
    exact hq.false
  obtain ⟨x, hx, hxA⟩ := nonempty_of_measure_ne_zero hinter
  refine ⟨cubeIndex N x, mem_finiteDyadicUnion_iff.mp hxA, ?_⟩
  have ha := dyadicCube_subset_ancestor n (N - n) (cubeIndex N x)
    (show x ∈ dyadicCube (n + (N - n)) (cubeIndex N x) by
      simpa only [Nat.add_sub_of_le hn] using mem_dyadicCube_cubeIndex N x)
  exact (mem_dyadicCube_iff.mp ha).symm.trans (mem_dyadicCube_iff.mp hx)

/-- The actual regular component's upper profile estimate holds on all cubes, including null ones. -/
theorem normalized_regular_component_cube_upper
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {j : ℕ} (hj : j ≤ L) (q : Fin 2 → ℤ) :
    normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * j) q) ≤
      (2 : ℝ≥0∞) ^ (-regularProfileExponent L e j + j) := by
  let σ := normalizedRestrict μ (finiteDyadicUnion (T * L) A)
  haveI := isProbabilityMeasure_normalizedRestrict
    (measurableSet_finiteDyadicUnion _ _) hA (measure_ne_top μ _)
  by_cases hz : σ (dyadicCube (T * j) q) = 0
  · change σ (dyadicCube (T * j) q) ≤ _
    rw [hz]
    exact bot_le
  obtain ⟨k, hk, hq⟩ := exists_leaf_of_normalized_component_cube_pos μ
    (Nat.mul_le_mul_left T hj) A q (pos_iff_ne_zero.mpr hz)
  rw [← Nat.mul_sub] at hq
  have h := (normalized_regular_component_cube_bounds μ hA hreg hroot hj hk).2
  rw [hq] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_ofNat] at h'
  exact h'

/-- A ball at a block-grid radius is controlled by the preceding grid, with a fixed block loss. -/
theorem normalized_regular_component_ball_upper
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} (hT : 0 < T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (he : ∀ j < L, e j ≤ 2 * T)
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {j : ℕ} (hj : j ≤ L) (x : EuclideanSpace ℝ (Fin 2)) :
    normalizedRestrict μ (finiteDyadicUnion (T * L) A)
        (Metric.ball x (dyadicRadius (T * j))) ≤
      4 * (2 : ℝ≥0∞) ^ (2 * T + j - regularProfileExponent L e j) := by
  let σ := normalizedRestrict μ (finiteDyadicUnion (T * L) A)
  haveI := isProbabilityMeasure_normalizedRestrict
    (measurableSet_finiteDyadicUnion _ _) hA (measure_ne_top μ _)
  cases j with
  | zero =>
      refine (prob_le_one (μ := σ)).trans ?_
      simp only [regularProfileExponent_zero, Nat.cast_zero, add_zero, sub_zero]
      apply one_le_mul (by norm_num)
      simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by positivity : (0 : ℝ) ≤ 2 * T)
  | succ j =>
      have hrad : dyadicRadius (T * (j + 1)) ≤
          (2 : ℝ) ^ (-(((T * j : ℕ) : ℝ) + 1)) := by
        unfold dyadicRadius
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
        push_cast
        nlinarith
      have hb := measure_ball_le_of_cube_bound (μ := σ) (x := x)
        (dyadicRadius_pos (T * (j + 1)))
        hrad
        (normalized_regular_component_cube_upper μ hA hreg hroot (by omega : j ≤ L))
      refine hb.trans (mul_le_mul_right ?_ 4)
      apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      have hej : (e (L - 1 - j) : ℝ) ≤ 2 * T := by
        exact_mod_cast he (L - 1 - j) (by omega)
      rw [regularProfileExponent_succ]
      push_cast
      linarith

/-- Every active cube of the original component has the lower mass prescribed by its profile. -/
theorem normalized_regular_component_cube_lower
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {j : ℕ} (hj : j ≤ L) (q : Fin 2 → ℤ)
    (hq : 0 < normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * j) q)) :
    (2 : ℝ≥0∞) ^ (-regularProfileExponent L e j - 2 * j) ≤
      normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * j) q) := by
  haveI := isProbabilityMeasure_normalizedRestrict
    (measurableSet_finiteDyadicUnion _ _) hA (measure_ne_top μ _)
  obtain ⟨k, hk, hkq⟩ := exists_leaf_of_normalized_component_cube_pos μ
    (Nat.mul_le_mul_left T hj) A q hq
  rw [← Nat.mul_sub] at hkq
  have h := (normalized_regular_component_cube_bounds μ hA hreg hroot hj hk).1
  rw [hkq] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_ofNat] at h'
  exact h'

/-- Conditioning on any enlargement containing an active cube has the finite profile ball bound.
No lower bound for a boundary sliver or geometric shape assumption on the enlargement is used. -/
theorem normalized_regular_conditional_ball_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} (hT : 0 < T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (he : ∀ j < L, e j ≤ 2 * T)
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {m k : ℕ} (hm : m ≤ L) (hk : k ≤ L)
    {q : Fin 2 → ℤ}
    (hq : 0 < normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * m) q))
    {X : Set (EuclideanSpace ℝ (Fin 2))} (hX : dyadicCube (T * m) q ⊆ X)
    (x : EuclideanSpace ℝ (Fin 2)) :
    normalizedRestrict (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) X
        (Metric.ball x (dyadicRadius (T * k))) ≤
      (4 * (2 : ℝ≥0∞) ^ (3 * (L : ℝ) + 2 * T)) *
        (2 : ℝ≥0∞) ^ (regularProfileExponent L e m - regularProfileExponent L e k) := by
  let σ := normalizedRestrict μ (finiteDyadicUnion (T * L) A)
  have hden : (2 : ℝ≥0∞) ^ (-regularProfileExponent L e m - 2 * m) ≤ σ X :=
    (normalized_regular_component_cube_lower μ hA hreg hroot hm q hq).trans (measure_mono hX)
  have hinv : (σ X)⁻¹ ≤
      (2 : ℝ≥0∞) ^ (regularProfileExponent L e m + 2 * m) := by
    have h := ENNReal.inv_le_inv.mpr hden
    rw [← ENNReal.rpow_neg] at h
    convert h using 1
    congr 1
    ring
  have hball := normalized_regular_component_ball_upper μ hT he hA hreg hroot hk x
  calc
    _ ≤ (σ X)⁻¹ * σ (Metric.ball x (dyadicRadius (T * k))) :=
      normalizedRestrict_ball_le σ X x _
    _ ≤ (2 : ℝ≥0∞) ^ (regularProfileExponent L e m + 2 * m) *
        (4 * (2 : ℝ≥0∞) ^ (2 * T + k - regularProfileExponent L e k)) :=
      mul_le_mul' hinv hball
    _ = 4 * (2 : ℝ≥0∞) ^
        ((regularProfileExponent L e m + 2 * m) +
          (2 * T + k - regularProfileExponent L e k)) := by
      rw [ENNReal.rpow_add (regularProfileExponent L e m + 2 * m)
        (2 * T + k - regularProfileExponent L e k) (by norm_num) (by norm_num)]
      ring
    _ ≤ 4 * (2 : ℝ≥0∞) ^ ((3 * L + 2 * T) +
        (regularProfileExponent L e m - regularProfileExponent L e k)) := by
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      have hm' : (m : ℝ) ≤ L := by exact_mod_cast hm
      have hk' : (k : ℝ) ≤ L := by exact_mod_cast hk
      linarith
    _ = _ := by rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), mul_assoc]

end FalconerPacking
