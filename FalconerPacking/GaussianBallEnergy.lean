/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.GaussianFrostman

/-!
# Fourier mass in a frequency ball

The Gaussian lower bound on a frequency ball turns the checked Gaussian estimate into
the local Fourier energy estimate used in polar-coordinate band decompositions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace FalconerPacking

/-- The Gaussian-weighted squared characteristic function of a probability is integrable. -/
theorem integrable_gaussian_charFun_energy
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2) volume := by
  have hg : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-b * ‖ξ‖ ^ 2)) volume := by
    have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by exact hb : 0 < (b : ℂ).re) 0 (0 : EuclideanSpace ℝ (Fin 2))
    have he (ξ : EuclideanSpace ℝ (Fin 2)) :
        (Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 + 0 * (inner ℝ (0 : EuclideanSpace ℝ (Fin 2)) ξ))).re =
          Real.exp (-b * ‖ξ‖ ^ 2) := by
      simp only [zero_mul, add_zero]
      rw [show -(b : ℂ) * ‖ξ‖ ^ 2 = ((-b * ‖ξ‖ ^ 2 : ℝ) : ℂ) by push_cast; rfl,
        ← Complex.ofReal_exp, Complex.ofReal_re]
    have h' := h.re
    change Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      (Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 + 0 *
        (inner ℝ (0 : EuclideanSpace ℝ (Fin 2)) ξ))).re) volume at h'
    simpa only [he] using h'
  apply hg.mono' (by fun_prop)
  exact Eventually.of_forall fun ξ ↦ by
    have hchar : ‖charFun μ ξ‖ ^ 2 ≤ 1 := by
      nlinarith [norm_charFun_le_one (μ := μ) ξ, norm_nonneg (charFun μ ξ)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2), mul_one] using
      mul_le_mul_of_nonneg_left hchar (Real.exp_nonneg _)

/-- A Gaussian bounded below on a frequency ball controls its unweighted Fourier mass. -/
theorem integral_charFun_norm_sq_ball_le_gaussian
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {b R : ℝ} (hb : 0 < b) (hR : 0 ≤ R) (hbR : b * R ^ 2 ≤ 1) :
    ∫ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ‖charFun μ ξ‖ ^ 2 ≤
      Real.exp 1 * ∫ ξ : EuclideanSpace ℝ (Fin 2),
        Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hfull := integrable_gaussian_charFun_energy μ hb
  have hbound (ξ) (hξ : ξ ∈ B) :
      ‖charFun μ ξ‖ ^ 2 ≤ Real.exp 1 *
        (Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2) := by
    have hnorm : ‖ξ‖ ≤ R :=
      (show ‖ξ‖ < R by simpa only [B, Metric.mem_ball, dist_zero_right] using hξ).le
    have he : 1 ≤ Real.exp 1 * Real.exp (-b * ‖ξ‖ ^ 2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have hs : ‖ξ‖ ^ 2 ≤ R ^ 2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hnorm
      nlinarith [mul_le_mul_of_nonneg_left hs hb.le]
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right he (sq_nonneg (‖charFun μ ξ‖))
  have hlocal : IntegrableOn (fun ξ ↦ ‖charFun μ ξ‖ ^ 2) B := by
    apply ((hfull.const_mul (Real.exp 1)).restrict).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem hB] with ξ hξ
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖charFun μ ξ‖))] using hbound ξ hξ
  calc
    ∫ ξ in B, ‖charFun μ ξ‖ ^ 2 ≤ ∫ ξ in B,
        Real.exp 1 * (Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2) := by
      exact integral_mono_ae hlocal (hfull.const_mul (Real.exp 1)).restrict
        ((ae_restrict_iff' hB).mpr (Eventually.of_forall hbound))
    _ ≤ ∫ ξ, Real.exp 1 * (Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2) :=
      setIntegral_le_integral (hfull.const_mul _) (Eventually.of_forall fun _ ↦ by positivity)
    _ = Real.exp 1 * ∫ ξ, Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 := integral_const_mul _ _

/-- Frequency balls obey the scale-dependent bound obtained from the Frostman exponent. -/
theorem integral_charFun_norm_sq_ball_le_of_isFrostman
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) {R : ℝ} (hR : 0 < R) :
    ∫ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ‖charFun μ ξ‖ ^ 2 ≤
      Real.exp 1 * (Real.pi / ((2 / R) ^ 2 / 4) *
        (max C 1 * (2 / R) ^ s * gaussianAnnulusConstant)) := by
  have hbR : ((2 / R) ^ 2 / 4) * R ^ 2 ≤ 1 := by
    field_simp
    norm_num
  exact (integral_charFun_norm_sq_ball_le_gaussian μ (by positivity) hR.le hbR).trans
    (mul_le_mul_of_nonneg_left
      (gaussian_fourier_energy_le_of_isFrostman μ hs hs₂ hfr (by positivity))
      (Real.exp_nonneg 1))

/-- The usual local Fourier growth estimate, with one constant independent of the radius. -/
theorem exists_fourier_ball_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 < R →
      ∫ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ‖charFun μ ξ‖ ^ 2 ≤
        A * R ^ (2 - s) := by
  let A := Real.exp 1 * Real.pi * max C 1 * (2 : ℝ) ^ s * gaussianAnnulusConstant
  have hA : 0 < A := by dsimp [A]; positivity [gaussianAnnulusConstant_pos]
  refine ⟨A, hA, fun R hR ↦ ?_⟩
  have hid : Real.exp 1 * (Real.pi / ((2 / R) ^ 2 / 4) *
      (max C 1 * (2 / R) ^ s * gaussianAnnulusConstant)) = A * R ^ (2 - s) := by
    dsimp [A]
    rw [Real.div_rpow (by norm_num) hR.le, Real.rpow_sub hR, Real.rpow_two]
    field_simp
    ring
  exact (integral_charFun_norm_sq_ball_le_of_isFrostman μ hs hs₂ hfr hR).trans_eq hid

end FalconerPacking
