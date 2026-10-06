/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.GaussianWeightedEnergy
public import FalconerPacking.PolarFourierEnergy

/-!
# Fourier band energy for bounded real weights

The signed-weight Gaussian comparison and the positive Gaussian lower bound on a ball yield
the same Frostman Fourier growth estimate, multiplied by the squared bound on the weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Bounded weights give continuous characteristic transforms. -/
theorem continuous_weightedCharFun
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : Measurable w)
    {r : ℝ} (hbound : ∀ᵐ x ∂μ, |w x| ≤ r) : Continuous (weightedCharFun μ w) := by
  apply continuous_of_dominated (bound := fun _ ↦ r)
  · intro ξ
    fun_prop
  · intro ξ
    filter_upwards [hbound] with x hx
    simpa [norm_mul, Real.norm_eq_abs] using hx
  · exact integrable_const r
  · exact Eventually.of_forall fun x ↦ by fun_prop

/-- The transform of a weight bounded by r has modulus at most r for a probability. -/
theorem norm_weightedCharFun_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} {r : ℝ}
    (hbound : ∀ᵐ x ∂μ, |w x| ≤ r) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖weightedCharFun μ w ξ‖ ≤ r := by
  apply (norm_integral_le_of_norm_le_const ?_).trans_eq
    (by simp : r * μ.real univ = r)
  filter_upwards [hbound] with x hx
  simpa [norm_mul, Real.norm_eq_abs] using hx

/-- The Gaussian-weighted square is integrable even when the weight is signed. -/
theorem integrable_gaussian_weightedCharFun_energy
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : Measurable w) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ᵐ x ∂μ, |w x| ≤ r) {b : ℝ} (hb : 0 < b) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2) volume := by
  have hg : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-b * ‖ξ‖ ^ 2)) volume := by
    simpa using integrable_gaussian_charFun_energy
      (Measure.dirac (0 : EuclideanSpace ℝ (Fin 2))) hb
  have hc := continuous_weightedCharFun μ hw hbound
  apply (hg.mul_const (r ^ 2)).mono' (by fun_prop)
  exact Eventually.of_forall fun ξ ↦ by
    have hs := (sq_le_sq₀ (norm_nonneg _) hr).mpr (norm_weightedCharFun_le μ hbound ξ)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2)] using
      mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)

/-- The Gaussian comparison controls weighted Fourier mass on a frequency ball. -/
theorem integral_weightedCharFun_norm_sq_ball_le_gaussian
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : Measurable w) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ᵐ x ∂μ, |w x| ≤ r) {b R : ℝ}
    (hb : 0 < b) (hR : 0 ≤ R) (hbR : b * R ^ 2 ≤ 1) :
    ∫ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
      ‖weightedCharFun μ w ξ‖ ^ 2 ≤
        Real.exp 1 * r ^ 2 * ∫ ξ : EuclideanSpace ℝ (Fin 2),
          Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 := by
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hc := continuous_weightedCharFun μ hw hbound
  have hfull := integrable_gaussian_weightedCharFun_energy μ hw hr hbound hb
  have hlocal : IntegrableOn (fun ξ ↦ ‖weightedCharFun μ w ξ‖ ^ 2) B :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall _ R)
      (hc.norm.pow 2).continuousOn).mono_set Metric.ball_subset_closedBall
  have hpoint (ξ) (hξ : ξ ∈ B) :
      ‖weightedCharFun μ w ξ‖ ^ 2 ≤ Real.exp 1 *
        (Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2) := by
    have hnorm : ‖ξ‖ ≤ R :=
      (show ‖ξ‖ < R by simpa only [B, Metric.mem_ball, dist_zero_right] using hξ).le
    have he : 1 ≤ Real.exp 1 * Real.exp (-b * ‖ξ‖ ^ 2) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have hs := (sq_le_sq₀ (norm_nonneg _) hR).mpr hnorm
      nlinarith [mul_le_mul_of_nonneg_left hs hb.le]
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right he (sq_nonneg (‖weightedCharFun μ w ξ‖))
  calc
    ∫ ξ in B, ‖weightedCharFun μ w ξ‖ ^ 2 ≤ ∫ ξ in B,
        Real.exp 1 * (Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2) :=
      integral_mono_ae hlocal (hfull.const_mul _).restrict
        ((ae_restrict_iff' hB).mpr (Eventually.of_forall hpoint))
    _ ≤ ∫ ξ, Real.exp 1 *
        (Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2) :=
      setIntegral_le_integral (hfull.const_mul _) (Eventually.of_forall fun _ ↦ by positivity)
    _ = Real.exp 1 * ∫ ξ,
        Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2 := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (integral_gaussian_weightedCharFun_norm_sq_le_ae μ hw hr hbound hb) (Real.exp_nonneg 1)

/-- One Fourier-ball constant works for every bounded real weight. -/
theorem exists_weighted_fourier_ball_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (w : EuclideanSpace ℝ (Fin 2) → ℝ), Measurable w →
      ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, |w x| ≤ r) → ∀ R : ℝ, 0 < R →
        ∫ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
          ‖weightedCharFun μ w ξ‖ ^ 2 ≤ A * r ^ 2 * R ^ (2 - s) := by
  let A := Real.exp 1 * Real.pi * max C 1 * (2 : ℝ) ^ s * gaussianAnnulusConstant
  refine ⟨A, by dsimp [A]; positivity [gaussianAnnulusConstant_pos], ?_⟩
  intro w hw r hr hbound R hR
  have hbR : ((2 / R) ^ 2 / 4) * R ^ 2 ≤ 1 := by field_simp; norm_num
  have h := (integral_weightedCharFun_norm_sq_ball_le_gaussian μ hw hr hbound
    (by positivity) hR.le hbR).trans (mul_le_mul_of_nonneg_left
      (gaussian_fourier_energy_le_of_isFrostman μ hs hs₂ hfr (r := 2 / R) (by positivity))
      (by positivity : 0 ≤ Real.exp 1 * r ^ 2))
  apply h.trans_eq
  dsimp [A]
  rw [Real.div_rpow (by norm_num) hR.le, Real.rpow_sub hR, Real.rpow_two]
  field_simp
  ring

/-- Polar integration converts weighted ball growth into a weighted angular band estimate. -/
theorem exists_weighted_angular_fourier_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (w : EuclideanSpace ℝ (Fin 2) → ℝ), Measurable w →
      ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, |w x| ≤ r) → ∀ R : ℝ, 0 < R →
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R),
          ENNReal.ofReal (‖weightedCharFun μ w (τ • angularDirection θ)‖ ^ 2) ≤
            ENNReal.ofReal (A * r ^ 2 * R ^ (1 - s)) := by
  obtain ⟨A, hA, hball⟩ := exists_weighted_fourier_ball_energy_bound μ hs hs₂ hfr
  refine ⟨2 * A * (2 : ℝ) ^ (2 - s), by positivity, ?_⟩
  intro w hw r hr hbound R hR
  have hc := continuous_weightedCharFun μ hw hbound
  have hpolar := lintegral_angular_band_le (R := 2 * R)
    (f := fun ξ ↦ ENNReal.ofReal (‖weightedCharFun μ w ξ‖ ^ 2)) (by fun_prop)
    (show 0 < R / 2 by positivity)
  have hlocal : IntegrableOn (fun ξ ↦ ‖weightedCharFun μ w ξ‖ ^ 2)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (2 * R)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
      (hc.norm.pow 2).continuousOn).mono_set Metric.ball_subset_closedBall
  have hint := ofReal_integral_eq_lintegral_ofReal hlocal
    (Eventually.of_forall fun ξ ↦ sq_nonneg (‖weightedCharFun μ w ξ‖))
  rw [← hint] at hpolar
  have he : (ENNReal.ofReal (R / 2))⁻¹ * ENNReal.ofReal (A * r ^ 2 * (2 * R) ^ (2 - s)) =
      ENNReal.ofReal ((2 * A * (2 : ℝ) ^ (2 - s)) * r ^ 2 * R ^ (1 - s)) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by norm_num) hR.le, show 2 - s = 1 + (1 - s) by ring,
      Real.rpow_add hR, Real.rpow_one]
    field_simp
  exact (hpolar.trans (mul_le_mul' le_rfl
    (ENNReal.ofReal_le_ofReal (hball w hw r hr hbound (2 * R) (by positivity))))).trans_eq he

end FalconerPacking
