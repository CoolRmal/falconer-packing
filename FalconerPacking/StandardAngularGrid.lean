/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicAngularCaps
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A standard angular grid compatible with dyadic refinement

The explicit power-of-two count has angular width comparable to inverse square-root
frequency. All coarser and finer dyadic counts divide one another exactly.
-/

@[expose] public section

namespace FalconerPacking

/-- The square root of an even dyadic frequency has its exact dyadic value. -/
theorem sqrt_even_dyadic_frequency (n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (2 * n)) = (2 : ℝ) ^ n := by
  rw [Nat.mul_comm 2 n, pow_mul, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

/-- One concrete dividing grid meets all hypotheses of the actual standard-cap construction. -/
theorem standard_dyadic_angular_grid_bounds (n : ℕ) :
    0 < 64 * 2 ^ n ∧
    Real.sqrt ((2 : ℝ) ^ (2 * n)) ≤ (64 * 2 ^ n : ℕ) ∧
    4 * Real.pi ≤ (64 * 2 ^ n : ℕ) ∧
    (64 * 2 ^ n : ℕ) ≤ 2 * Real.pi * 32 * Real.sqrt ((2 : ℝ) ^ (2 * n)) := by
  have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hp := Real.pi_gt_three
  have hq := Real.pi_lt_four
  rw [sqrt_even_dyadic_frequency]
  norm_cast
  constructor
  · positivity
  constructor
  · norm_cast at hn
    omega
  constructor
  · push_cast
    nlinarith
  · push_cast
    nlinarith [mul_nonneg (by linarith : 0 ≤ Real.pi - 1) (by positivity : 0 ≤ (2 : ℝ) ^ n)]

/-- Refinement by any number of dyadic levels preserves exact divisibility of the counts. -/
theorem standard_dyadic_angular_grid_dvd (n k : ℕ) :
    64 * 2 ^ n ∣ 64 * 2 ^ (n + k) := by
  refine ⟨2 ^ k, ?_⟩
  rw [pow_add, mul_assoc]

/-- The annuli with exponent four times a block length have one concrete admissible grid. -/
theorem standard_fourfold_angular_grid_bounds (T n : ℕ) :
    0 < 64 * 2 ^ (2 * T * n) ∧
    Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) ≤ (64 * 2 ^ (2 * T * n) : ℕ) ∧
    4 * Real.pi ≤ (64 * 2 ^ (2 * T * n) : ℕ) ∧
    (64 * 2 ^ (2 * T * n) : ℕ) ≤
      2 * Real.pi * 32 * Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) := by
  rw [show (4 * T) * n = 2 * (2 * T * n) by ring]
  exact standard_dyadic_angular_grid_bounds (2 * T * n)

end FalconerPacking
