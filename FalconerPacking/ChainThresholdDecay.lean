/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ChainThresholdProduct
import FalconerPacking.StrictShellParameters

/-!
# Strict shell decay for the complete threshold product

The block size, width exponent, and threshold inflation are fixed before the shell depth.
The actual polynomial prefactor is then absorbed uniformly over all admissible profiles.
-/

noncomputable section

open Filter
open scoped ENNReal

namespace FalconerPacking

/-- The explicit finite-product majorant leaves half of the strict profile margin.
The term `3K` is the finite regularity loss and is made small by the fixed block size. -/
theorem eventually_chain_threshold_scalar_le
    {C D h v s η : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hη : 0 < η)
    (K : ℕ) {T : ℕ} (hT : 0 < T)
    (hloss : (K : ℝ) * ((28 * K + 114) * h + v) * T + 3 * K ≤ η * T / 4) :
    ∀ᶠ N : ℕ in atTop,
      (C * D * (N + 1)) ^ K *
          ((2 : ℝ) ^ (h * T * N)) ^ (K * (28 * K + 114)) *
          (2 : ℝ) ^ ((K : ℝ) * (v * T * N + 3 * N + 3 * T) +
            T * ((s - 1 - η) * N)) ≤
        (2 : ℝ) ^ ((s - 1 - η / 2) * T * N) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  let P := (C * D) ^ K * (2 : ℝ) ^ (3 * (K : ℝ) * T)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpoly := eventually_polynomial_le_dyadic
    (show 0 < η * T / 4 by positivity) hP K
  filter_upwards [hpoly] with N hN
  let α := h * T * (K * (28 * K + 114)) + K * v * T + 3 * K + (s - 1 - η) * T
  have hid :
      (C * D * (N + 1)) ^ K *
          ((2 : ℝ) ^ (h * T * N)) ^ (K * (28 * K + 114)) *
          (2 : ℝ) ^ ((K : ℝ) * (v * T * N + 3 * N + 3 * T) +
            T * ((s - 1 - η) * N)) =
        P * (N + 1) ^ K * (2 : ℝ) ^ (α * N) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by norm_num), mul_assoc,
      ← Real.rpow_add (by norm_num)]
    have he : h * T * N * (K * (28 * K + 114) : ℕ) +
        ((K : ℝ) * (v * T * N + 3 * N + 3 * T) + T * ((s - 1 - η) * N)) =
        3 * K * T + α * N := by
      dsimp [α]
      push_cast
      ring
    rw [he, Real.rpow_add (by norm_num)]
    dsimp [P]
    ring
  rw [hid]
  calc
    _ ≤ (2 : ℝ) ^ (η * T / 4 * N) * (2 : ℝ) ^ (α * N) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = (2 : ℝ) ^ ((η * T / 4 + α) * N) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hα : η * T / 4 + α ≤ (s - 1 - η / 2) * T := by
        dsimp [α]
        nlinarith
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg N)

/-- The actual ENNReal threshold product has a strict dyadic shell bound, uniformly over
all profiles and all chain lengths below the fixed maximum. -/
theorem eventually_marked_chain_threshold_product_le
    {C D h v s η : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hh : 0 ≤ h) (hv : 0 ≤ v) (hη : 0 < η) (K : ℕ) {T : ℕ} (hT : 0 < T)
    (hloss : (K : ℝ) * ((28 * K + 114) * h + v) * T + 3 * K ≤ η * T / 4) :
    ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ), k ≤ K → ∀ (c : ℕ → ℝ) (H : ℕ → ℝ≥0∞),
      (∀ j < k, H j ≤ ENNReal.ofReal (D * (N + 1)) *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (20 * K + 100)) *
        (2 : ℝ≥0∞) ^ (v * T * N + 3 * N + 3 * T + T * c j)) →
      (∑ j ∈ Finset.range k, c j) ≤ (s - 1 - η) * N →
      (∏ j ∈ Finset.range k, ENNReal.ofReal C *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (8 * j + 14)) * H j) ≤
          (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N) := by
  have hC₀ := le_trans zero_le_one hC
  have hD₀ := le_trans zero_le_one hD
  filter_upwards [eventually_chain_threshold_scalar_le (s := s) hC₀ hD₀ hη K hT hloss] with N hN
  intro k hk c H hH hcost
  have hL : 1 ≤ (2 : ℝ) ^ (h * T * N) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hp := marked_chain_threshold_product_le hC hD hL
    (show 0 ≤ v * T * N by positivity) hk c H hH hcost
  refine hp.trans ?_
  have hscalar := ENNReal.ofReal_le_ofReal hN
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos (by norm_num), ← ENNReal.ofReal_rpow_of_pos (by norm_num)] at hscalar
  norm_num only [ENNReal.ofReal_ofNat] at hscalar
  exact hscalar

/-- Applying the preceding result to the actual finite list uses its exact cost identity. -/
theorem eventually_profile_chain_threshold_product_le
    {C D h v s η : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hh : 0 ≤ h) (hv : 0 ≤ v) (hη : 0 < η) (K : ℕ) {T : ℕ} (hT : 0 < T)
    (hloss : (K : ℝ) * ((28 * K + 114) * h + v) * T + 3 * K ≤ η * T / 4) :
    ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (g : ℕ → ℝ) (l : List ℕ), l.length ≤ K →
      chainCost g n l ≤ (s - 1 - η) * N → ∀ H : ℕ → ℝ≥0∞,
      (∀ j < l.length, H j ≤ ENNReal.ofReal (D * (N + 1)) *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (20 * K + 100)) *
        (2 : ℝ≥0∞) ^ (v * T * N + 3 * N + 3 * T +
          T * edgeCost g (profileChainDepth n l (j + 1)) (profileChainDepth n l j))) →
      (∏ j ∈ Finset.range l.length, ENNReal.ofReal C *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (8 * j + 14)) * H j) ≤
          (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N) := by
  filter_upwards [eventually_marked_chain_threshold_product_le hC hD hh hv hη K hT hloss]
    with N hN
  intro n g l hlen hcost H hH
  exact hN l.length hlen _ H hH (by simpa only [sum_edgeCost_profileChainDepth] using hcost)

end FalconerPacking
