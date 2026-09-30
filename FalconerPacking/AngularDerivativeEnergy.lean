/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.WeightedBandEnergy
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Angular derivatives of characteristic functions

The actual angular derivative is a linear combination of two signed coordinate transforms.
Their weighted Fourier band estimates retain the source-radius gain before integration.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The unit tangent to the angular parametrization of the circle. -/
def angularTangent (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr (-Real.sin θ + Real.cos θ * Complex.I)

/-- Differentiating the circle parametrization gives the tangent vector. -/
theorem hasDerivAt_angularDirection (θ : ℝ) :
    HasDerivAt angularDirection (angularTangent θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).ofReal_comp).add
    (((Real.hasDerivAt_sin θ).ofReal_comp).mul_const Complex.I)
  simp only [Complex.ofReal_neg] at h
  exact Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt θ h

/-- The tangent is the quarter-turn of the unit direction. -/
theorem angularTangent_eq_direction (θ : ℝ) :
    angularTangent θ = angularDirection (θ + Real.pi / 2) := by
  simp [angularTangent, angularDirection, Real.cos_add, Real.sin_add]

@[simp]
theorem norm_angularTangent (θ : ℝ) : ‖angularTangent θ‖ = 1 := by
  rw [angularTangent_eq_direction, norm_angularDirection]

@[fun_prop]
theorem continuous_angularTangent : Continuous angularTangent := by
  unfold angularTangent
  fun_prop

/-- Bounded support supplies the finite moments needed to differentiate characteristic functions. -/
theorem memLp_id_of_ae_norm_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r : ℝ} (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r) (p : ℝ≥0∞) : MemLp id p μ :=
  MemLp.of_bound (by fun_prop) r hsource

/-- The directional derivative is the characteristic transform of the signed coordinate weight. -/
theorem fderiv_charFun_apply_eq_weightedCharFun
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) (ξ v : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (charFun μ) ξ v =
      Complex.I * weightedCharFun μ (fun x ↦ ⟪x, v⟫) ξ := by
  have h := iteratedFDeriv_charFun (μ := μ) (n := 1) (t := ξ)
    (by simpa using hm) (fun _ ↦ v)
  simpa only [iteratedFDeriv_one_apply, pow_one, Fin.prod_univ_one, weightedCharFun] using h

/-- The chain rule gives the derivative with respect to the actual direction angle. -/
theorem hasDerivAt_angular_charFun
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) (τ θ : ℝ) :
    HasDerivAt (fun t ↦ charFun μ (τ • angularDirection t))
      (fderiv ℝ (charFun μ) (τ • angularDirection θ) (τ • angularTangent θ)) θ := by
  have hc := (contDiff_charFun (μ := μ) (n := 1) (by simpa using hm)).differentiable
    (by norm_num)
  exact hc.differentiableAt.hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_angularDirection θ).const_smul τ)

/-- The angular derivative varies continuously with both angle and frequency. -/
theorem continuous_deriv_angular_charFun
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) :
    Continuous (fun p : ℝ × ℝ ↦ deriv (fun t ↦ charFun μ (p.2 • angularDirection t)) p.1) := by
  simp_rw [(hasDerivAt_angular_charFun μ hm _ _).deriv]
  have hc := (contDiff_charFun (μ := μ) (n := 1) (by simpa using hm)).continuous_fderiv
    (by norm_num)
  exact (hc.comp (by fun_prop)).clm_apply (by fun_prop)

/-- The angular derivative is bounded pointwise by the two fixed coordinate transforms. -/
theorem norm_deriv_angular_charFun_sq_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) (τ θ : ℝ) :
    ‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ ^ 2 ≤
      2 * τ ^ 2 *
        (‖weightedCharFun μ (fun x ↦ ⟪x, Complex.orthonormalBasisOneI.repr 1⟫)
          (τ • angularDirection θ)‖ ^ 2 +
        ‖weightedCharFun μ (fun x ↦ ⟪x, Complex.orthonormalBasisOneI.repr Complex.I⟫)
          (τ • angularDirection θ)‖ ^ 2) := by
  let e₀ := Complex.orthonormalBasisOneI.repr (1 : ℂ)
  let e₁ := Complex.orthonormalBasisOneI.repr Complex.I
  let z₀ := weightedCharFun μ (fun x ↦ ⟪x, e₀⟫) (τ • angularDirection θ)
  let z₁ := weightedCharFun μ (fun x ↦ ⟪x, e₁⟫) (τ • angularDirection θ)
  have ht : angularTangent θ = (-Real.sin θ) • e₀ + Real.cos θ • e₁ := by
    dsimp [angularTangent, e₀, e₁]
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    simp [Complex.real_smul]
  have hd : deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ =
      τ • ((-Real.sin θ) • (Complex.I * z₀) + Real.cos θ • (Complex.I * z₁)) := by
    rw [(hasDerivAt_angular_charFun μ hm τ θ).deriv, ht, map_smul, map_add,
      map_smul, map_smul, fderiv_charFun_apply_eq_weightedCharFun μ hm,
      fderiv_charFun_apply_eq_weightedCharFun μ hm]
  have hnorm : ‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ ≤
      |τ| * (‖z₀‖ + ‖z₁‖) := by
    rw [hd, norm_smul, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      ‖(-Real.sin θ) • (Complex.I * z₀) + Real.cos θ • (Complex.I * z₁)‖ ≤
          ‖(-Real.sin θ) • (Complex.I * z₀)‖ + ‖Real.cos θ • (Complex.I * z₁)‖ :=
        norm_add_le _ _
      _ = |Real.sin θ| * ‖z₀‖ + |Real.cos θ| * ‖z₁‖ := by
        simp only [norm_smul, norm_mul, Real.norm_eq_abs, abs_neg, Complex.norm_I, one_mul]
      _ ≤ ‖z₀‖ + ‖z₁‖ := by
        simpa only [one_mul] using add_le_add
          (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg z₀))
          (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg z₁))
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  change _ ≤ 2 * τ ^ 2 * (‖z₀‖ ^ 2 + ‖z₁‖ ^ 2)
  rw [mul_pow, sq_abs] at hs
  nlinarith [mul_nonneg (sq_nonneg τ) (sq_nonneg (‖z₀‖ - ‖z₁‖))]

/-- Source support of radius r gives an angular derivative band bound of order
`r² R^(3-s)`. The constant is independent of r and R. -/
theorem exists_angular_derivative_fourier_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ R : ℝ, 0 < R →
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in Ioo (R / 2) (2 * R),
          ENNReal.ofReal (‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ ^ 2) ≤
            ENNReal.ofReal (A * r ^ 2 * R ^ (3 - s)) := by
  obtain ⟨A, hA, hband⟩ := exists_weighted_angular_fourier_band_bound μ hs hs₂ hfr
  refine ⟨16 * A, by positivity, ?_⟩
  intro r hr hsource R hR
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

/-- The squared derivative is genuinely integrable on each bounded angle-frequency rectangle. -/
theorem integrable_angular_charFun_deriv_sq_band
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) (L R : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      ‖deriv (fun t ↦ charFun μ (p.2 • angularDirection t)) p.1‖ ^ 2)
      ((volume.restrict (Ioo (-Real.pi) Real.pi)).prod (volume.restrict (Ioo L R))) := by
  rw [Measure.prod_restrict]
  exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    ((continuous_deriv_angular_charFun μ hm).norm.pow 2).continuousOn).mono_set
      (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-- The angular derivative estimate also holds for the ordinary iterated integral. -/
theorem exists_angular_derivative_fourier_band_bound_real
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ A : ℝ, 0 < A ∧ ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ R : ℝ, 0 < R →
        ∫ θ in Ioo (-Real.pi) Real.pi, ∫ τ in Ioo (R / 2) (2 * R),
          ‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ ^ 2 ≤
            A * r ^ 2 * R ^ (3 - s) := by
  obtain ⟨A, hA, hband⟩ := exists_angular_derivative_fourier_band_bound μ hs hs₂ hfr
  refine ⟨A, hA, fun r hr hsource R hR ↦ ?_⟩
  have hm := memLp_id_of_ae_norm_le μ hsource 1
  have hint := integrable_angular_charFun_deriv_sq_band μ hm (R / 2) (2 * R)
  have he := ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun p ↦ sq_nonneg
      ‖deriv (fun t ↦ charFun μ (p.2 • angularDirection t)) p.1‖)
  rw [integral_prod _ hint, lintegral_prod _ (by
    have hc := (continuous_deriv_angular_charFun μ hm).norm.pow 2
    exact hc.measurable.ennreal_ofReal.aemeasurable)]
    at he
  have h := hband r hr hsource R hR
  rw [← he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Reversing radial frequency conjugates the angular derivative. -/
theorem deriv_angular_charFun_neg
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) (τ θ : ℝ) :
    deriv (fun t ↦ charFun μ ((-τ) • angularDirection t)) θ =
      star (deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ) := by
  have h := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_angular_charFun μ hm τ θ)
  have hd := h.deriv
  change deriv (fun t ↦ star (charFun μ (τ • angularDirection t))) θ =
    star (fderiv ℝ (charFun μ) (τ • angularDirection θ) (τ • angularTangent θ)) at hd
  simpa only [neg_smul, charFun_neg, starRingEnd_apply,
    (hasDerivAt_angular_charFun μ hm τ θ).deriv] using hd

/-- The squared angular derivative is even in radial frequency. -/
theorem norm_deriv_angular_charFun_neg
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (hm : MemLp id 1 μ) (τ θ : ℝ) :
    ‖deriv (fun t ↦ charFun μ ((-τ) • angularDirection t)) θ‖ =
      ‖deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ‖ := by
  rw [deriv_angular_charFun_neg μ hm, norm_star]

end FalconerPacking
