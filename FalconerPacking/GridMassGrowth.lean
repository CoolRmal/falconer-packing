/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dyadic
import FalconerPacking.SchwartzPotential
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi

/-!
# Quadratic mass growth from unit grid cells

A ball of integer radius meets at most `(2N+1)²` unit grid cells. Thus a uniform
cell-mass bound supplies the geometric hypothesis of the Schwartz potential estimate.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace FalconerPacking

/-- The explicit finite grid indices covering an integer-radius ball. -/
def integerBallGrid (x : EuclideanSpace ℝ (Fin 2)) (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (⌊x i⌋ - N) (⌊x i⌋ + N)

/-- The grid covering has exactly the quadratic cardinality. -/
theorem card_integerBallGrid (x : EuclideanSpace ℝ (Fin 2)) (N : ℕ) :
    (integerBallGrid x N).card = (2 * N + 1) ^ 2 := by
  have hcard (i : Fin 2) : (Finset.Icc (⌊x i⌋ - N) (⌊x i⌋ + N)).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    omega
  simp [integerBallGrid, Fintype.card_piFinset, hcard, pow_two]

/-- Every point of the ball belongs to a cell with one of these indices. -/
theorem ball_subset_integerBallGrid (x : EuclideanSpace ℝ (Fin 2)) (N : ℕ) :
    ball x (N : ℝ) ⊆ ⋃ k ∈ integerBallGrid x N, dyadicCube 0 k := by
  intro y hy
  apply mem_iUnion₂.mpr
  refine ⟨cubeIndex 0 y, ?_, mem_dyadicCube_cubeIndex 0 y⟩
  rw [integerBallGrid, Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hcoord : |y i - x i| < (N : ℝ) :=
    (abs_sub_coord_le_dist y x i).trans_lt (mem_ball.mp hy)
  have hlow := Int.floor_le_floor (show x i - (N : ℝ) ≤ y i by
    have h := (abs_lt.mp hcoord).1
    linarith)
  have hhigh := Int.floor_le_floor (show y i ≤ x i + (N : ℝ) by
    have h := (abs_lt.mp hcoord).2
    linarith)
  simpa [cubeIndex] using And.intro hlow hhigh

/-- Uniform unit-cell masses imply quadratic growth for every integer-radius ball. -/
theorem measure_ball_nat_le_of_unit_cube_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (M : ℝ≥0∞)
    (hM : ∀ k, μ (dyadicCube 0 k) ≤ M)
    (x : EuclideanSpace ℝ (Fin 2)) (N : ℕ) :
    μ (ball x (N : ℝ)) ≤ ((2 * N + 1 : ℕ) : ℝ≥0∞) ^ 2 * M := by
  calc
    _ ≤ μ (⋃ k ∈ integerBallGrid x N, dyadicCube 0 k) :=
      measure_mono (ball_subset_integerBallGrid x N)
    _ ≤ ∑ k ∈ integerBallGrid x N, μ (dyadicCube 0 k) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ integerBallGrid x N, M := Finset.sum_le_sum (fun k _ ↦ hM k)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, card_integerBallGrid, Nat.cast_pow]

/-- At dyadic radii, the growth constant is at most nine times the cell mass. -/
theorem measure_ball_dyadic_le_of_unit_cube_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (M : ℝ≥0∞)
    (hM : ∀ k, μ (dyadicCube 0 k) ≤ M)
    (x : EuclideanSpace ℝ (Fin 2)) (n : ℕ) :
    μ (ball x ((2 : ℝ) ^ n)) ≤ (9 * M) * (4 : ℝ≥0∞) ^ n := by
  have h := measure_ball_nat_le_of_unit_cube_mass μ M hM x (2 ^ n)
  have hN : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hcard : (2 * (2 ^ n) + 1) ^ 2 ≤ 9 * (2 ^ n) ^ 2 := by nlinarith
  have hcard' : (((2 * (2 ^ n) + 1) : ℕ) : ℝ≥0∞) ^ 2 ≤ 9 * (2 ^ n : ℝ≥0∞) ^ 2 := by
    exact_mod_cast hcard
  have heq : (2 ^ n : ℝ≥0∞) ^ 2 = 4 ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  refine h.trans ?_
  calc
    _ ≤ (9 * (2 ^ n : ℝ≥0∞) ^ 2) * M := mul_le_mul_left hcard' M
    _ = _ := by rw [heq]; ring

/-- A unit-grid mass bound yields a uniform potential for every actual Schwartz kernel. -/
theorem schwartz_potential_le_of_unit_cube_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (M : ℝ≥0∞)
    (hM : ∀ q, μ (dyadicCube 0 q) ≤ M) (x : EuclideanSpace ℝ (Fin 2)) :
    ∫⁻ y, ‖k (x - y)‖ₑ ∂μ ≤
      81 * ENNReal.ofReal
        (SchwartzMap.seminorm ℝ 0 0 k + SchwartzMap.seminorm ℝ 4 0 k) * M := by
  refine (schwartz_potential_le_of_dyadic_ball_growth μ k x (9 * M)
    (measure_ball_dyadic_le_of_unit_cube_mass μ M hM x)).trans_eq ?_
  ring

/-- The reflected convolution convention has the same uniform constant. -/
theorem schwartz_potential_sub_right_le_of_unit_cube_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (M : ℝ≥0∞)
    (hM : ∀ q, μ (dyadicCube 0 q) ≤ M) (x : EuclideanSpace ℝ (Fin 2)) :
    ∫⁻ y, ‖k (y - x)‖ₑ ∂μ ≤
      81 * ENNReal.ofReal
        (SchwartzMap.seminorm ℝ 0 0 k + SchwartzMap.seminorm ℝ 4 0 k) * M := by
  have h₀ := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) k
  have h₄ := apply_nonneg (SchwartzMap.seminorm ℝ 4 0) k
  have h := lintegral_le_of_dyadic_ball_growth μ x (fun y ↦ ‖k (y - x)‖)
    (add_nonneg h₀ h₄) (9 * M)
    (fun y ↦ (SchwartzMap.norm_le_seminorm ℝ k (y - x)).trans (le_add_of_nonneg_right h₄))
    (fun y ↦ by
      rw [dist_eq_norm]
      exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ k 4 (y - x)).trans
        (le_add_of_nonneg_left h₀)) (measure_ball_dyadic_le_of_unit_cube_mass μ M hM x)
  simp only [ofReal_norm] at h
  exact h.trans_eq (by ring)

end FalconerPacking
