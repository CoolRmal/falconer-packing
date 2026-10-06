/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleEnergyIntegration
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Omitted radial energy from an actual Fourier envelope

A bound on the actual Fourier transform outside a radial set bounds the normalized spectral
circle average there. The remaining positive radial integral is evaluated using translation
invariance and an integrable power. These lemmas do not assume an omitted-energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Normalized spectral circle averaging does not increase a uniform Fourier bound. -/
theorem norm_pinnedSpectralCircleAverage_le
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2)) (r D : ℝ)
    (hD : ∀ θ, ‖𝓕 f (r • angularDirection θ)‖ ≤ D) :
    ‖pinnedSpectralCircleAverage f y r‖ ≤ D := by
  rw [pinnedSpectralCircleAverage_eq_probability]
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := radialAngularProbability) (C := D)
      (f := fun θ ↦ 𝐞 (⟪y, r • angularDirection θ⟫) • 𝓕 f (r • angularDirection θ))
      (ae_of_all _ fun θ ↦ by simpa only [Circle.norm_smul] using hD θ)

/-- Translation moves the positive half-line to a half-line starting at the shift. -/
theorem lintegral_Ioi_zero_add (F : ℝ → ℝ≥0∞) (R : ℝ) :
    (∫⁻ r in Ioi (0 : ℝ), F (R + r)) = ∫⁻ t in Ioi R, F t := by
  calc
    _ = ∫⁻ r : ℝ, (Ioi R).indicator F (R + r) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro r
      by_cases hr : 0 < r
      · rw [indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
          indicator_of_mem (show R + r ∈ Ioi R by change R < R + r; linarith)]
      · rw [indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
          indicator_of_notMem (show R + r ∉ Ioi R by change ¬ R < R + r; linarith)]
    _ = ∫⁻ t : ℝ, (Ioi R).indicator F t := lintegral_add_left_eq_self _ R
    _ = _ := lintegral_indicator measurableSet_Ioi _

/-- The shifted radial majorant has its literal finite power integral. -/
theorem lintegral_shifted_rpow {R p : ℝ} (hR : 0 < R) (hp : 1 < p) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal ((R + r) ^ (1 - 2 * p))) =
      ENNReal.ofReal (R ^ (2 - 2 * p) / (2 * p - 2)) := by
  rw [lintegral_Ioi_zero_add (fun t ↦ ENNReal.ofReal (t ^ (1 - 2 * p))) R]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by linarith : 1 - 2 * p < -1) hR)]
  · rw [integral_Ioi_rpow_of_lt (by linarith : 1 - 2 * p < -1) hR]
    congr 1
    rw [show 1 - 2 * p + 1 = -(2 * p - 2) by ring, neg_div_neg_eq]
    congr 1
    congr 1
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hR.trans ht).le _

/-- One radial Jacobian is absorbed by the shifted frequency radius. -/
theorem radial_power_envelope_le {R p D r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    r * (D * (R + r) ^ (-p)) ^ 2 ≤ D ^ 2 * (R + r) ^ (1 - 2 * p) := by
  have ht : 0 < R + r := by positivity
  calc
    _ ≤ (R + r) * (D * (R + r) ^ (-p)) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = D ^ 2 * ((R + r) ^ (1 : ℝ) * ((R + r) ^ (-p)) ^ 2) := by
      rw [Real.rpow_one]
      ring
    _ = D ^ 2 * (R + r) ^ (1 - 2 * p) := by
      rw [← Real.rpow_natCast ((R + r) ^ (-p)) 2, ← Real.rpow_mul ht.le,
        ← Real.rpow_add ht]
      congr 2
      norm_num
      ring

/-- The full radial power envelope is finite, with its scale exponent made explicit. -/
theorem lintegral_radial_power_envelope_le {R p D : ℝ} (hR : 0 < R) (hp : 1 < p) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
      ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2)) ≤
        ENNReal.ofReal (D ^ 2 * R ^ (2 - 2 * p) / (2 * p - 2)) := by
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (D ^ 2) *
        ENNReal.ofReal ((R + r) ^ (1 - 2 * p)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (sq_nonneg D)]
      exact ENNReal.ofReal_le_ofReal (radial_power_envelope_le hR hr)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_shifted_rpow hR hp,
        ← ENNReal.ofReal_mul (sq_nonneg D)]
      congr 1
      ring

/-- A literal pointwise Fourier envelope outside any measurable radial set bounds the actual
pin-averaged omitted spectral energy. The pin-dependent sources need not share a Fourier transform. -/
theorem lintegral_omitted_circle_energy_le_of_fourier_envelope
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {S : Set ℝ} (hS : MeasurableSet S) {R p D : ℝ}
    (hR : 0 < R) (hp : 1 < p) (hD : 0 ≤ D)
    (hfourier : ∀ᵐ y ∂ν, ∀ ξ, ‖ξ‖ ∈ Ioi (0 : ℝ) \ S →
      ‖𝓕 (f y : EuclideanSpace ℝ (Fin 2) → ℂ) ξ‖ ≤ D * (R + ‖ξ‖) ^ (-p)) :
    (∫⁻ r in Ioi (0 : ℝ) \ S, ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
        ENNReal.ofReal (D ^ 2 * R ^ (2 - 2 * p) / (2 * p - 2)) := by
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ) \ S, ENNReal.ofReal r *
        ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff hS)] with r hr
      apply mul_le_mul_right
      have hb : ∀ᵐ y ∂ν, ‖pinnedSpectralCircleAverage (f y) y r‖ ≤
          D * (R + r) ^ (-p) := by
        filter_upwards [hfourier] with y hy
        apply norm_pinnedSpectralCircleAverage_le
        intro θ
        have hn : ‖r • angularDirection θ‖ = r := by
          rw [norm_smul, Real.norm_eq_abs, norm_angularDirection, mul_one, abs_of_pos hr.1]
        simpa only [hn] using hy (r • angularDirection θ) (by simpa only [hn] using hr)
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2) ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hb] with y hy
          exact ENNReal.ofReal_le_ofReal
            ((sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg hD (Real.rpow_nonneg (add_nonneg hR.le (show 0 < r from hr.1).le) _))).mpr hy)
        _ = _ := by simp
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2) := lintegral_mono_set sdiff_subset
    _ ≤ _ := lintegral_radial_power_envelope_le hR hp

end FalconerPacking
