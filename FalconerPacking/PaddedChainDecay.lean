/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PaddedProfileChain
import FalconerPacking.ChainThresholdDecay
import FalconerPacking.ChainEnergyDecay

/-!
# The complete numerical coefficient for the actual padded profile

Both the main threshold product and every preceding-factor error are reduced to the
strict profile exponent. No list, scale, cost-sum, or terminal identity is assumed.
-/

noncomputable section

open Filter
open scoped ENNReal

namespace FalconerPacking

/-- Uniform shell reduction for the exact coefficient in the broad-annulus circle theorem.
The threshold lower bound is supplied by the actual choice of thresholds, while its upper
bound includes the full conditional-energy and geometric losses. -/
theorem eventually_padded_chain_coefficient_le
    {C D h v s η : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hh : 0 ≤ h) (hv : 0 ≤ v) (hη : 0 < η) (K pwr : ℕ) {T : ℕ} (hT : 0 < T)
    (hloss : (K : ℝ) * ((28 * K + 114) * h + v) * T + 3 * K ≤ η * T / 4)
    (horder : 2 + h * ((4 * K + 8 : ℕ) - (pwr : ℝ)) < 0) :
    ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (g : ℕ → ℝ) (l : List ℕ), n ≤ N → l.length ≤ K →
      List.IsChain (fun n m ↦ m < n) (n :: l) → chainEnd n l = 0 →
      chainCost g n l ≤ (s - 1 - η) * N → ∀ H : ℕ → ℝ≥0∞,
      (∀ j < K, 1 ≤ H j) →
      (∀ j < K, H j ≤ ENNReal.ofReal (D * (N + 1)) *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (20 * K + 100)) *
        (2 : ℝ≥0∞) ^ (v * T * N + 3 * N + 3 * T +
          T * edgeCost g (profileChainDepth n l (j + 1)) (profileChainDepth n l j))) →
      let d := fun j ↦ T * profileChainDepth n l j
      let L := (2 : ℝ) ^ (h * T * N)
      let A := fun j ↦ ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
      (∏ j ∈ Finset.range K, A j) * ENNReal.ofReal (49 * ((2 : ℝ) ^ d K) ^ 2) +
        (∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) *
          (ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ d j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))) ≤
        50 * (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N) := by
  have hC₀ := le_trans zero_le_one hC
  filter_upwards [eventually_marked_chain_threshold_product_le (s := s) hC hD hh hv hη K hT hloss,
    eventually_marked_chain_coefficient_le hC₀ hh K pwr hT horder] with N hprod herror
  intro n g l hn hlen hl hend hcost H hH₁ hH
  dsimp only
  let d := fun j ↦ T * profileChainDepth n l j
  let L := (2 : ℝ) ^ (h * T * N)
  let A := fun j ↦ ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
  have hd (j : ℕ) (_hj : j < K) : d j ≤ T * N :=
    Nat.mul_le_mul_left T ((profileChainDepth_le_initial hl j).trans hn)
  have hend' : d K = 0 := by
    dsimp [d]
    rw [profileChainDepth_eq_zero_of_length_le hend hlen, Nat.mul_zero]
  have hL : 1 ≤ L := Real.one_le_rpow (by norm_num) (by positivity)
  have hA (j : ℕ) (hj : j < K) : 1 ≤ A j := by
    dsimp [A]
    apply one_le_mul
    · apply one_le_mul
      · simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hC
      · simpa only [ENNReal.ofReal_one] using
          ENNReal.ofReal_le_ofReal (one_le_pow₀ hL : (1 : ℝ) ≤ L ^ (8 * j + 14))
    · exact hH₁ j hj
  have hfull := hprod K le_rfl
    (fun j ↦ edgeCost g (profileChainDepth n l (j + 1)) (profileChainDepth n l j)) H hH
    (by simpa only [sum_edgeCost_padded_profileChainDepth g hlen hend] using hcost)
  exact (herror d A hd hend' hA).trans (mul_le_mul_right hfull 50)

end FalconerPacking
