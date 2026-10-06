/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ChainEnergyRemainders
public import FalconerPacking.StrictShellParameters

/-!
# Absorbing the complete finite-chain remainder

A fixed sufficiently high kernel order makes the entire preceding-factor error no larger
than the full threshold product. The choice is uniform over all padded spatial chains.
-/

@[expose] public section

noncomputable section

open Filter
open scoped ENNReal

namespace FalconerPacking

/-- The exact scalar remainder in the chain estimate is eventually at most one. -/
theorem eventually_chain_remainder_le_one {C h : ℝ} (hC : 0 ≤ C)
    (K pwr : ℕ) {T : ℕ} (hT : 0 < T)
    (horder : 2 + h * ((4 * K + 8 : ℕ) - (pwr : ℝ)) < 0) :
    ∀ᶠ N : ℕ in atTop,
      (K : ℝ) * 49 * C * ((2 : ℝ) ^ (T * N)) ^ 2 *
        ((2 : ℝ) ^ (h * T * N)) ^ (4 * K + 8) *
        (((2 : ℝ) ^ (h * T * N)) ^ pwr)⁻¹ ≤ 1 := by
  let β : ℝ := 2 + h * ((4 * K + 8 : ℕ) - (pwr : ℝ))
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hβ : 0 < -β * T := mul_pos (neg_pos.mpr horder) hT'
  have hp := eventually_polynomial_le_dyadic hβ
    (show 0 ≤ (K : ℝ) * 49 * C by positivity) 0
  filter_upwards [hp] with N hN
  simp only [pow_zero, mul_one] at hN
  have hid : ((2 : ℝ) ^ (T * N)) ^ 2 *
      ((2 : ℝ) ^ (h * T * N)) ^ (4 * K + 8) *
      (((2 : ℝ) ^ (h * T * N)) ^ pwr)⁻¹ = (2 : ℝ) ^ (β * T * N) := by
    have htwo : ((2 : ℝ) ^ (T * N)) ^ 2 = (2 : ℝ) ^ (2 * (T : ℝ) * N) := by
      rw [← pow_mul, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [htwo, ← Real.rpow_mul_natCast (by norm_num),
      ← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_neg (by norm_num),
      ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    dsimp [β]
    push_cast
    ring
  calc
    _ = ((K : ℝ) * 49 * C) * (2 : ℝ) ^ (β * T * N) := by rw [← hid]; ring
    _ ≤ (2 : ℝ) ^ (-β * T * N) * (2 : ℝ) ^ (β * T * N) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = 1 := by rw [← Real.rpow_add (by norm_num)]; ring_nf; simp

/-- For one fixed sufficiently high order, the exact finite-chain coefficient is at most
fifty times its complete threshold product, uniformly over all padded chains. -/
theorem eventually_marked_chain_coefficient_le {C h : ℝ} (hC : 0 ≤ C) (hh : 0 ≤ h)
    (K pwr : ℕ) {T : ℕ} (hT : 0 < T)
    (horder : 2 + h * ((4 * K + 8 : ℕ) - (pwr : ℝ)) < 0) :
    ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ → ℕ) (A : ℕ → ℝ≥0∞),
      (∀ j < K, n j ≤ T * N) → n K = 0 → (∀ j < K, 1 ≤ A j) →
      let L := (2 : ℝ) ^ (h * T * N)
      (∏ j ∈ Finset.range K, A j) * ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
        (∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) *
          (ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ n j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))) ≤
        50 * ∏ j ∈ Finset.range K, A j := by
  filter_upwards [eventually_chain_remainder_le_one hC K pwr hT horder] with N hN
  intro n A hn hend hA
  dsimp only
  have hL : 1 ≤ (2 : ℝ) ^ (h * T * N) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  apply (marked_chain_coefficient_le hC hL pwr K (T * N) n A hn hend hA).trans
  have he : ENNReal.ofReal ((K : ℝ) * 49 * C * ((2 : ℝ) ^ (T * N)) ^ 2 *
      ((2 : ℝ) ^ (h * T * N)) ^ (4 * K + 8) *
      (((2 : ℝ) ^ (h * T * N)) ^ pwr)⁻¹) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hN
  calc
    _ ≤ (∏ j ∈ Finset.range K, A j) * (49 + 1) := by gcongr
    _ = _ := by norm_num; rw [mul_comm]

end FalconerPacking
