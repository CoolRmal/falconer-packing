/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PaddedChainDecay

/-!
# Increasing the fixed chain constant

The actual embedding constant can be increased to at least one before applying the
uniform scalar estimate. Every preceding-edge product and every accumulated error
is monotone in the same constant.
-/

noncomputable section

open scoped ENNReal

namespace FalconerPacking

/-- The full literal chain coefficient is monotone in its common embedding constant,
including every prefix product that multiplies a spatial reconstruction error. -/
theorem chain_coefficient_mono_constant {c C : ℝ} (hc : c ≤ C)
    (K pwr : ℕ) (L : ℝ) (n : ℕ → ℕ) (H : ℕ → ℝ≥0∞) :
    (∏ j ∈ Finset.range K, ENNReal.ofReal c * ENNReal.ofReal (L ^ (8 * j + 14)) * H j) *
        ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
      ∑ j ∈ Finset.range K,
        (∏ i ∈ Finset.range j, ENNReal.ofReal c * ENNReal.ofReal (L ^ (8 * i + 14)) * H i) *
          (ENNReal.ofReal c * ENNReal.ofReal
            (((((2 : ℝ) ^ n j)⁻¹) ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2)) ≤
    (∏ j ∈ Finset.range K, ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j) *
        ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
      ∑ j ∈ Finset.range K,
        (∏ i ∈ Finset.range j, ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * i + 14)) * H i) *
          (ENNReal.ofReal C * ENNReal.ofReal
            (((((2 : ℝ) ^ n j)⁻¹) ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2)) := by
  gcongr

end FalconerPacking
