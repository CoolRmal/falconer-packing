/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularDerivativeEnergy

/-!
# Uniform Frostman constants in Fourier band estimates

The constants below depend only on the exponent. Every dependence on the probability
measure is the explicitly displayed factor `max C 1`; the maximum is necessary because
`IsFrostman` controls only radii at most one.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The scalar Gaussian coefficient for Fourier balls. -/
def uniformFourierBallCoefficient (s : ℝ) : ℝ :=
  Real.exp 1 * Real.pi * (2 : ℝ) ^ s * gaussianAnnulusConstant

theorem uniformFourierBallCoefficient_pos (s : ℝ) : 0 < uniformFourierBallCoefficient s := by
  unfold uniformFourierBallCoefficient
  positivity [gaussianAnnulusConstant_pos]

/-- The scalar coefficient after polar integration on a dyadic frequency band. -/
def uniformFourierBandCoefficient (s : ℝ) : ℝ :=
  2 * uniformFourierBallCoefficient s * (2 : ℝ) ^ (2 - s)

theorem uniformFourierBandCoefficient_pos (s : ℝ) : 0 < uniformFourierBandCoefficient s := by
  unfold uniformFourierBandCoefficient
  positivity [uniformFourierBallCoefficient_pos s]

/-- Weighted Fourier-ball growth with its Frostman dependence exposed. -/
theorem uniform_weighted_fourier_ball_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : Measurable w)
    (r : ℝ) (hr : 0 ≤ r) (hbound : ∀ᵐ x ∂μ, |w x| ≤ r) (R : ℝ) (hR : 0 < R) :
    ∫ ξ in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
      ‖weightedCharFun μ w ξ‖ ^ 2 ≤
        uniformFourierBallCoefficient s * max C 1 * r ^ 2 * R ^ (2 - s) := by
  have hbR : ((2 / R) ^ 2 / 4) * R ^ 2 ≤ 1 := by field_simp; norm_num
  have h := (integral_weightedCharFun_norm_sq_ball_le_gaussian μ hw hr hbound
    (by positivity) hR.le hbR).trans (mul_le_mul_of_nonneg_left
      (gaussian_fourier_energy_le_of_isFrostman μ hs hs₂ hfr (r := 2 / R) (by positivity))
      (by positivity : 0 ≤ Real.exp 1 * r ^ 2))
  apply h.trans_eq
  unfold uniformFourierBallCoefficient
  rw [Real.div_rpow (by norm_num) hR.le, Real.rpow_sub hR, Real.rpow_two]
  field_simp
  ring

/-- Weighted angular bands with a coefficient independent of the source measure. -/
theorem uniform_weighted_angular_fourier_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : Measurable w)
    (r : ℝ) (hr : 0 ≤ r) (hbound : ∀ᵐ x ∂μ, |w x| ≤ r) (R : ℝ) (hR : 0 < R) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R),
      ENNReal.ofReal (‖weightedCharFun μ w (τ • angularDirection θ)‖ ^ 2) ≤
        ENNReal.ofReal (uniformFourierBandCoefficient s * max C 1 * r ^ 2 * R ^ (1 - s)) := by
  let A := uniformFourierBallCoefficient s * max C 1
  have hA : 0 < A := by dsimp [A]; positivity [uniformFourierBallCoefficient_pos s]
  have hball := uniform_weighted_fourier_ball_energy_bound μ hs hs₂ hfr
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
  have hout := (hpolar.trans (mul_le_mul' le_rfl
    (ENNReal.ofReal_le_ofReal (hball w hw r hr hbound (2 * R) (by positivity))))).trans_eq he
  apply hout.trans_eq
  congr 1
  dsimp [A, uniformFourierBandCoefficient]
  ring

/-- The constant weight recovers the ordinary characteristic function. -/
theorem weightedCharFun_one (μ : Measure (EuclideanSpace ℝ (Fin 2))) (ξ) :
    weightedCharFun μ (fun _ ↦ 1) ξ = charFun μ ξ := by
  simp only [weightedCharFun, charFun_apply, Complex.ofReal_one, one_mul]

/-- The same uniform angular-band estimate for the unweighted transform. -/
theorem uniform_angular_fourier_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) (R : ℝ) (hR : 0 < R) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R),
      ENNReal.ofReal (‖charFun μ (τ • angularDirection θ)‖ ^ 2) ≤
        ENNReal.ofReal (uniformFourierBandCoefficient s * max C 1 * R ^ (1 - s)) := by
  simpa only [weightedCharFun_one, one_pow, mul_one] using
    uniform_weighted_angular_fourier_band_bound μ hs hs₂ hfr (fun _ ↦ 1) measurable_const
      1 (by norm_num) (Eventually.of_forall fun _ ↦ by norm_num) R hR

/-- The actual angular derivative retains linear dependence on the Frostman constant. -/
theorem uniform_angular_derivative_fourier_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 ≤ r) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r) (R : ℝ) (hR : 0 < R) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R),
      ENNReal.ofReal (‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ ^ 2) ≤
        ENNReal.ofReal (16 * (uniformFourierBandCoefficient s * max C 1) *
          r ^ 2 * R ^ (3 - s)) := by
  let A := uniformFourierBandCoefficient s * max C 1
  have hA : 0 < A := by dsimp [A]; positivity [uniformFourierBandCoefficient_pos s]
  have hband := uniform_weighted_angular_fourier_band_bound μ hs hs₂ hfr
  let e₀ := Complex.orthonormalBasisOneI.repr (1 : ℂ)
  let e₁ := Complex.orthonormalBasisOneI.repr Complex.I
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  have he₁ : ‖e₁‖ = 1 := by simp [e₁]
  have hw₀ : ∀ᵐ x ∂μ, |⟪x, e₀⟫| ≤ r := by
    filter_upwards [hsource] with x hx
    exact (abs_real_inner_le_norm x e₀).trans (by simpa only [he₀, mul_one] using hx)
  have hw₁ : ∀ᵐ x ∂μ, |⟪x, e₁⟫| ≤ r := by
    filter_upwards [hsource] with x hx
    exact (abs_real_inner_le_norm x e₁).trans (by simpa only [he₁, mul_one] using hx)
  have hc₀ := continuous_weightedCharFun μ (w := fun x ↦ ⟪x, e₀⟫) (by fun_prop) hw₀
  have hc₁ := continuous_weightedCharFun μ (w := fun x ↦ ⟪x, e₁⟫) (by fun_prop) hw₁
  let f₀ := fun θ τ : ℝ ↦
    ENNReal.ofReal (‖weightedCharFun μ (fun x ↦ ⟪x, e₀⟫) (τ • angularDirection θ)‖ ^ 2)
  let f₁ := fun θ τ : ℝ ↦
    ENNReal.ofReal (‖weightedCharFun μ (fun x ↦ ⟪x, e₁⟫) (τ • angularDirection θ)‖ ^ 2)
  have hf₀ : Measurable (Function.uncurry f₀) := by dsimp [f₀]; fun_prop
  have hf₁ : Measurable (Function.uncurry f₁) := by dsimp [f₁]; fun_prop
  have h₀ := hband (fun x ↦ ⟪x, e₀⟫) (by fun_prop) r hr hw₀ R hR
  have h₁ := hband (fun x ↦ ⟪x, e₁⟫) (by fun_prop) r hr hw₁ R hR
  have hp (θ τ : ℝ) (hτ : τ ∈ Ioo (R / 2) (2 * R)) :
      ENNReal.ofReal (‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ ^ 2) ≤
        ENNReal.ofReal (8 * R ^ 2) * (f₀ θ τ + f₁ θ τ) := by
    dsimp [f₀, f₁]
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply (norm_deriv_angular_charFun_sq_le μ (memLp_id_of_ae_norm_le μ hsource 1) τ θ).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hτ₀ : 0 ≤ τ := by linarith [hτ.1]
    have ht := (sq_le_sq₀ hτ₀ (by positivity)).mpr hτ.2.le
    nlinarith
  calc
    _ ≤ ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R),
        ENNReal.ofReal (8 * R ^ 2) * (f₀ θ τ + f₁ θ τ) := by
      apply lintegral_mono
      intro θ
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
      exact hp θ τ hτ
    _ = ENNReal.ofReal (8 * R ^ 2) *
        ((∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R), f₀ θ τ) +
        (∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R), f₁ θ τ)) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left (hf₀.of_uncurry_left) (f₁ _)]
      rw [lintegral_add_left (by fun_prop)]
    _ ≤ ENNReal.ofReal (8 * R ^ 2) *
        (ENNReal.ofReal (A * r ^ 2 * R ^ (1 - s)) +
        ENNReal.ofReal (A * r ^ 2 * R ^ (1 - s))) := mul_le_mul_right (add_le_add h₀ h₁) _
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show 3 - s = 2 + (1 - s) by ring, Real.rpow_add hR, Real.rpow_two]
      ring

end FalconerPacking
