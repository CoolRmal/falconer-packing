/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.LocalizedFourierOrthogonality
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# An actual bandlimited spatial cutoff

A normalized nonnegative frequency bump has inverse Fourier transform close to one on
a fixed spatial ball. This constructs the cutoff needed for local orthogonality.
-/

noncomputable section

open MeasureTheory Set Metric Filter FourierTransform SchwartzMap
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The normalized real bump, complexified as a Schwartz function. -/
def normalizedFrequencyBump (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (φ.hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero |>.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp φ.contDiff_normed)

/-- A normalized positive frequency bump has integral one. -/
theorem integral_normalizedFrequencyBump
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2))) :
    (∫ ξ, normalizedFrequencyBump φ ξ) = 1 := by
  change (∫ ξ, (φ.normed volume ξ : ℂ)) = 1
  rw [integral_complex_ofReal, φ.integral_normed]
  norm_num

/-- The inverse transform is quantitatively close to one near the origin. -/
theorem norm_fourierInv_normalizedFrequencyBump_sub_one_le
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖𝓕⁻ (normalizedFrequencyBump φ) x - 1‖ ≤ 2 * Real.pi * φ.rOut * ‖x‖ := by
  let χ := normalizedFrequencyBump φ
  let e (ξ : EuclideanSpace ℝ (Fin 2)) :=
    Complex.exp ((2 * Real.pi * ⟪ξ, x⟫ : ℝ) * Complex.I)
  have he : Continuous e := by dsimp only [e]; fun_prop
  have hi : Integrable (fun ξ ↦ e ξ * χ ξ) volume :=
    (he.mul χ.continuous).integrable_of_hasCompactSupport
      ((φ.hasCompactSupport_normed (μ := volume)).comp_left Complex.ofReal_zero).mul_left
  have hrepr : 𝓕⁻ χ x - 1 = ∫ ξ, (e ξ - 1) * χ ξ := by
    rw [fourierInv_coe, Real.fourierInv_eq']
    change (∫ ξ, e ξ * χ ξ) - 1 = _
    have hint : (∫ ξ, χ ξ) = 1 := integral_normalizedFrequencyBump φ
    rw [← hint, ← integral_sub hi χ.integrable]
    congr 1
    ext ξ
    rw [hint]
    ring
  rw [hrepr]
  calc
    _ ≤ ∫ ξ, (2 * Real.pi * φ.rOut * ‖x‖) * φ.normed volume ξ := by
      apply norm_integral_le_of_norm_le (φ.integrable_normed.const_mul _)
      exact Eventually.of_forall fun ξ ↦ by
        by_cases hχ : φ.normed volume ξ = 0
        · simp [χ, normalizedFrequencyBump, hχ]
        have hξ : ‖ξ‖ < φ.rOut := by
          have hmem : ξ ∈ Function.support (φ.normed volume) := hχ
          simpa only [φ.support_normed_eq, mem_ball, dist_zero_right] using hmem
        have hphase : ‖e ξ - 1‖ ≤ 2 * Real.pi * ‖ξ‖ * ‖x‖ := by
          have h := Real.norm_exp_I_mul_ofReal_sub_one_le
            (x := 2 * Real.pi * ⟪ξ, x⟫)
          have hi' := abs_real_inner_le_norm ξ x
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
          have heq : Complex.I * (2 * Real.pi * ⟪ξ, x⟫ : ℝ) =
              (2 * Real.pi * ⟪ξ, x⟫ : ℝ) * Complex.I := mul_comm _ _
          rw [heq] at h
          exact h.trans (by nlinarith [Real.pi_pos])
        rw [norm_mul]
        have hnorm : ‖χ ξ‖ = φ.normed volume ξ := by
          change ‖(φ.normed volume ξ : ℂ)‖ = _
          exact Complex.norm_of_nonneg (φ.nonneg_normed ξ)
        rw [hnorm]
        apply mul_le_mul_of_nonneg_right _ (φ.nonneg_normed ξ)
        exact hphase.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hξ.le (by positivity)) (norm_nonneg x))
    _ = _ := by rw [integral_const_mul, φ.integral_normed, mul_one]

/-- A specific small frequency bump for the unit spatial ball. -/
def localCutoffBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
  ⟨1 / 32, 1 / 16, by norm_num, by norm_num⟩

/-- An actual Schwartz function localized in frequency and bounded below in space. -/
def localFourierCutoff : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (2 : ℂ) • 𝓕⁻ (normalizedFrequencyBump localCutoffBump)

/-- Its Fourier support is contained in the unit ball. -/
theorem support_fourier_localFourierCutoff :
    Function.support (fun ξ ↦ 𝓕 localFourierCutoff ξ) ⊆
      ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  intro ξ hξ
  have hb : localCutoffBump.normed volume ξ ≠ 0 := by
    intro h
    apply hξ
    simp [localFourierCutoff, normalizedFrequencyBump, h]
  have hmem : ξ ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) localCutoffBump.rOut := by
    rwa [← localCutoffBump.support_normed_eq (μ := volume)]
  exact ball_subset_ball (by norm_num [localCutoffBump]) hmem

/-- Its modulus is at least one throughout the closed unit ball. -/
theorem one_le_norm_localFourierCutoff {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ ≤ 1) : 1 ≤ ‖localFourierCutoff x‖ := by
  have h := norm_fourierInv_normalizedFrequencyBump_sub_one_le localCutoffBump x
  have hπ := Real.pi_lt_four
  have hhalf : ‖𝓕⁻ (normalizedFrequencyBump localCutoffBump) x - 1‖ ≤ 1 / 2 := by
    apply h.trans
    dsimp only [localCutoffBump]
    nlinarith [Real.pi_pos, norm_nonneg x]
  have htri := norm_sub_norm_le
    (1 : ℂ) (𝓕⁻ (normalizedFrequencyBump localCutoffBump) x)
  rw [norm_sub_rev] at htri
  simp only [norm_one] at htri
  change 1 ≤ ‖(2 : ℂ) * 𝓕⁻ (normalizedFrequencyBump localCutoffBump) x‖
  rw [norm_mul]
  norm_num only [Complex.norm_ofNat]
  linarith

end FalconerPacking
