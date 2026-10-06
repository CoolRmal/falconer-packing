/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ScaledBandlimitedCutoff

/-!
# The initial circle multiplier for any bounded pin region

Rescaling the actual bandlimited cutoff accommodates an arbitrary fixed pin radius.
Frequency support remains inside the unit ball; no source or pin normalization is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- A fixed frequency multiplier adapted to the actual bound on the pins. -/
def initialCircleMultiplierRadius (B : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  𝓕 (scaledFourierCutoff (max 1 B) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) 0)

theorem support_initialCircleMultiplierRadius (B : ℝ) :
    Function.support (initialCircleMultiplierRadius B) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  apply (support_fourier_scaledFourierCutoff (max 1 B)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) 0).trans
  apply (ball_subset_ball _).trans ball_subset_closedBall
  exact inv_le_one_of_one_le₀ (le_max_left _ _)

theorem hasCompactSupport_initialCircleMultiplierRadius (B : ℝ) :
    HasCompactSupport (initialCircleMultiplierRadius B) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1)
    (support_initialCircleMultiplierRadius B)

theorem one_le_norm_fourierInv_initialCircleMultiplierRadius {B : ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : ‖x‖ ≤ B) :
    1 ≤ ‖(𝓕⁻ (initialCircleMultiplierRadius B)) x‖ := by
  simpa only [initialCircleMultiplierRadius, FourierTransform.fourierInv_fourier_eq] using
    one_le_norm_scaledFourierCutoff (max 1 B)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) 0 x
      (by simpa only [sub_zero] using hx.trans (le_max_right 1 B))

theorem lintegral_sq_initialCircleMultiplierRadius_lt_top (B : ℝ) :
    (∫⁻ ξ, ‖initialCircleMultiplierRadius B ξ‖ₑ ^ 2) < ⊤ := by
  have hi := ((initialCircleMultiplierRadius B).memLp 2 volume).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [hasFiniteIntegral_iff_enorm, enorm_pow, enorm_norm] using hi.hasFiniteIntegral

end FalconerPacking
