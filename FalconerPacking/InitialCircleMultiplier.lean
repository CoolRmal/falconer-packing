/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.BandlimitedCutoff

/-!
# A fixed multiplier for the initial circle estimate

The frequency multiplier is the Fourier transform of the constructed bandlimited spatial
cutoff. Its support lies in the unit ball, its inverse transform has modulus at least one
on the unit pin ball, and its square integral is finite.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- The fixed compact frequency multiplier used to recover spectral circle averages. -/
def initialCircleMultiplier : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  𝓕 localFourierCutoff

theorem support_initialCircleMultiplier :
    Function.support initialCircleMultiplier ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  support_fourier_localFourierCutoff.trans ball_subset_closedBall

theorem hasCompactSupport_initialCircleMultiplier : HasCompactSupport initialCircleMultiplier :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1)
    support_initialCircleMultiplier

/-- The actual inverse transform, rather than an assumed spatial cutoff, dominates one. -/
theorem one_le_norm_fourierInv_initialCircleMultiplier {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ ≤ 1) : 1 ≤ ‖(𝓕⁻ initialCircleMultiplier) x‖ := by
  simpa only [initialCircleMultiplier, FourierTransform.fourierInv_fourier_eq] using
    one_le_norm_localFourierCutoff hx

/-- The coefficient in the circle-energy bound is a finite real constant. -/
theorem lintegral_sq_initialCircleMultiplier_lt_top :
    (∫⁻ ξ, ‖initialCircleMultiplier ξ‖ₑ ^ 2) < ⊤ := by
  have hi := (initialCircleMultiplier.memLp 2 volume).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [hasFiniteIntegral_iff_enorm, enorm_pow, enorm_norm] using hi.hasFiniteIntegral

/-- A spectral average is bounded by its actual fixed spatially smoothed representative. -/
theorem norm_le_initialCircleMultiplier_mul {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ ≤ 1) (z : ℂ) : ‖z‖ ≤ ‖(𝓕⁻ initialCircleMultiplier) x * z‖ := by
  rw [norm_mul]
  exact le_mul_of_one_le_left (norm_nonneg z)
    (one_le_norm_fourierInv_initialCircleMultiplier hx)

end FalconerPacking
