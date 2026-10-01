/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ChainThresholdProduct

/-!
# Every preceding factor in the finite-chain error

The actual global errors are bounded without dropping the product of thresholds from
preceding edges. All such products are bounded by the full product, since each threshold
factor is at least one.
-/

noncomputable section

open Finset
open scoped ENNReal

namespace FalconerPacking

/-- The complete numerical coefficient of the proved Fourier chain, including every error,
is bounded by its full threshold product and one explicit remainder. -/
theorem marked_chain_coefficient_le
    {C L : ℝ} (hC : 0 ≤ C) (hL : 1 ≤ L) (pwr K M : ℕ)
    (n : ℕ → ℕ) (A : ℕ → ℝ≥0∞) (hn : ∀ j < K, n j ≤ M)
    (hterminal : n K = 0) (hA : ∀ j < K, 1 ≤ A j) :
    (∏ j ∈ Finset.range K, A j) * ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
      (∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) *
        (ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ n j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
          ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))) ≤
      (∏ j ∈ Finset.range K, A j) *
        (49 + ENNReal.ofReal ((K : ℝ) * 49 * C * ((2 : ℝ) ^ M) ^ 2 *
          L ^ (4 * K + 8) * (L ^ pwr)⁻¹)) := by
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  let P := ∏ j ∈ Finset.range K, A j
  let V := 49 * C * ((2 : ℝ) ^ M) ^ 2 * L ^ (4 * K + 8) * (L ^ pwr)⁻¹
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hedge (j : ℕ) (hj : j < K) :
      ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ n j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
          ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) ≤ ENNReal.ofReal V := by
    rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [inv_pow, inv_inv]
    have hpow : L ^ ((2 * (j + 1) + 2) * 2) ≤ L ^ (4 * K + 8) :=
      pow_le_pow_right₀ hL (by omega)
    have hdepth : ((2 : ℝ) ^ n j) ^ 2 ≤ ((2 : ℝ) ^ M) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ (by norm_num) (hn j hj)) 2
    have hpow' : (L ^ (2 * (j + 1) + 2)) ^ 2 ≤ L ^ (4 * K + 8) := by
      simpa only [← pow_mul] using hpow
    calc
      _ ≤ C * (((2 : ℝ) ^ M) ^ 2 * (L ^ pwr)⁻¹) * (49 * L ^ (4 * K + 8)) := by
        gcongr
      _ = V := by dsimp [V]; ring
  have hsum : (∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) *
      (ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ n j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
        ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))) ≤
        P * ENNReal.ofReal ((K : ℝ) * V) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range K, P * ENNReal.ofReal V := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul
          (prod_range_le_prod_range_ennreal (Finset.mem_range.mp hj).le hA)
          (hedge j (Finset.mem_range.mp hj)) bot_le bot_le
      _ = P * ENNReal.ofReal ((K : ℝ) * V) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
        ring
  rw [hterminal]
  norm_num only [pow_zero, one_pow, mul_one, ENNReal.ofReal_ofNat]
  refine (add_le_add_right hsum (P * 49)).trans_eq ?_
  dsimp [V, P]
  rw [mul_add]
  congr 2
  congr 1
  ring

end FalconerPacking
