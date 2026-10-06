/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ProjectionDensity
public import FalconerPacking.CorrelatedFourierEnergy

/-!
# Plancherel comparison of actual projection densities

The inverse Fourier representatives agree almost everywhere with any nonnegative density
of the original finite measure. Linearity of the `L²` Fourier isometry therefore gives
the exact norm identity for differences, including translated orthogonal projections.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Any actual nonnegative density agrees with the inverse Fourier representative. -/
theorem density_ae_eq_measureFourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume)
    {f : ℝ → ℝ} (hf : AEMeasurable f volume) (hf₀ : ∀ x, 0 ≤ f x)
    (hd : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) :
    (fun x ↦ (f x : ℂ)) =ᵐ[volume] measureFourierDensity μ hμ := by
  have hr := Measure.rnDeriv_withDensity₀ volume hf.ennreal_ofReal
  rw [← hd] at hr
  filter_upwards [hr, rnDeriv_ae_eq_measureFourierDensity μ hμ] with x hx hx'
  simpa only [hx, ENNReal.toReal_ofReal (hf₀ x)] using hx'

/-- Plancherel preserves the norm of a difference of inverse measure Fourier transforms. -/
theorem norm_measureFourierDensity_sub
    (μ ν : Measure ℝ) (hμ : MemLp (measureFourier μ) 2 volume)
    (hν : MemLp (measureFourier ν) 2 volume) :
    ‖measureFourierDensity μ hμ - measureFourierDensity ν hν‖ =
      (eLpNorm (fun ξ ↦ measureFourier μ ξ - measureFourier ν ξ) 2 volume).toReal := by
  change ‖(Lp.fourierTransformₗᵢ ℝ ℂ).symm (hμ.toLp (measureFourier μ)) -
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm (hν.toLp (measureFourier ν))‖ = _
  rw [← map_sub, LinearIsometryEquiv.norm_map, ← MemLp.toLp_sub, Lp.norm_toLp]
  rfl

/-- The exact Fourier normalization for the squared difference of two characteristic functions. -/
theorem integral_norm_sq_measureFourier_sub (μ ν : Measure ℝ) :
    ∫ ξ, ‖measureFourier μ ξ - measureFourier ν ξ‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun μ ξ - charFun ν ξ‖ ^ 2 := by
  simp_rw [measureFourier_eq_charFun]
  rw [Measure.integral_comp_mul_left (fun ξ ↦ ‖charFun μ ξ - charFun ν ξ‖ ^ 2)
    (-2 * Real.pi)]
  congr 1
  rw [abs_inv, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos Real.pi_pos]
  norm_num

/-- The difference of two actual densities has exactly the Fourier difference energy. -/
theorem integral_density_sub_sq_eq_charFun
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : MemLp (charFun μ) 2 volume) (hν : MemLp (charFun ν) 2 volume)
    {f g : ℝ → ℝ} (hf : AEMeasurable f volume) (hg : AEMeasurable g volume)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x)
    (hfd : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hgd : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (g x))) :
    ∫ x, (f x - g x) ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun μ ξ - charFun ν ξ‖ ^ 2 := by
  let hμ' := (memLp_measureFourier_iff μ).mpr hμ
  let hν' := (memLp_measureFourier_iff ν).mpr hν
  let D := measureFourierDensity μ hμ' - measureFourierDensity ν hν'
  have heq : (fun x ↦ ((f x - g x : ℝ) : ℂ)) =ᵐ[volume] D := by
    filter_upwards [density_ae_eq_measureFourierDensity μ hμ' hf hf₀ hfd,
      density_ae_eq_measureFourierDensity ν hν' hg hg₀ hgd,
      Lp.coeFn_sub (measureFourierDensity μ hμ') (measureFourierDensity ν hν')]
      with x hx hx' hx''
    simpa only [D, Pi.sub_apply, ← hx, ← hx', Complex.ofReal_sub] using hx''.symm
  calc
    ∫ x, (f x - g x) ^ 2 = ∫ x, ‖D x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [← hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ‖D‖ ^ 2 := by
      rw [integral_norm_sq_eq_eLpNorm_two_sq (Lp.memLp D), ← Lp.norm_def]
    _ = (eLpNorm (fun ξ ↦ measureFourier μ ξ - measureFourier ν ξ) 2 volume).toReal ^ 2 := by
      dsimp only [D]
      rw [norm_measureFourierDensity_sub]
    _ = ∫ ξ, ‖measureFourier μ ξ - measureFourier ν ξ‖ ^ 2 :=
      (integral_norm_sq_eq_eLpNorm_two_sq (hμ'.sub hν')).symm
    _ = _ := integral_norm_sq_measureFourier_sub μ ν

/-- Translation of an absolutely continuous law translates its density. -/
theorem map_add_const_eq_withDensity (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hd : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (v : ℝ) :
    μ.map (fun x ↦ x + v) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (f (x - v))) := by
  refine Measure.ext_of_lintegral _ fun h hh ↦ ?_
  rw [lintegral_map hh (by fun_prop), hd,
    lintegral_withDensity_eq_lintegral_mul₀ hf.ennreal_ofReal.aemeasurable (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) hh.aemeasurable]
  have htrans := lintegral_add_right_eq_self (μ := volume)
    (fun x : ℝ ↦ ENNReal.ofReal (f (x - v)) * h x) v
  simpa only [add_sub_cancel_right, Pi.mul_apply] using htrans

/-- Translation changes the characteristic function only by a factor of modulus one. -/
theorem memLp_charFun_map_add_const (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : MemLp (charFun μ) 2 volume) (v : ℝ) :
    MemLp (charFun (μ.map (fun x ↦ x + v))) 2 volume := by
  apply hμ.congr_norm (by fun_prop)
  filter_upwards [] with ξ
  simp [charFun_map_add_const, Complex.norm_exp]

/-- The characteristic function of a translated orthogonal projection. -/
theorem charFun_translated_orthogonalProjection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (φ v τ : ℝ) :
    charFun ((μ.map (fun x ↦ ⟪x, angularDirection φ⟫)).map (fun x ↦ x + v)) τ =
      Complex.exp (Complex.I * (τ * v)) * charFun μ (τ • angularDirection φ) := by
  rw [charFun_map_add_const, charFun_orthogonalProjection, mul_comm]
  congr 1
  congr 1
  simp only [Real.inner_apply]
  push_cast
  ring

/-- Exact comparison for two actual projection densities, one of them translated. -/
theorem integral_orthogonalProjectionDensity_sub_sq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (θ φ v : ℝ)
    (hθ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection θ)) 2 volume)
    (hφ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection φ)) 2 volume) :
    ∫ t, (orthogonalProjectionDensity μ φ (t - v) -
      orthogonalProjectionDensity μ θ t) ^ 2 =
        (2 * Real.pi)⁻¹ * ∫ τ : ℝ,
          ‖Complex.exp (Complex.I * (τ * v)) * charFun μ (τ • angularDirection φ) -
            charFun μ (τ • angularDirection θ)‖ ^ 2 := by
  have hθ' : MemLp (charFun (orthogonalProjectionKernel μ θ)) 2 volume := by
    change MemLp (fun τ ↦ charFun (orthogonalProjectionKernel μ θ) τ) 2 volume
    simpa only [orthogonalProjectionKernel_apply, charFun_orthogonalProjection] using hθ
  have hφ' : MemLp (charFun (orthogonalProjectionKernel μ φ)) 2 volume := by
    change MemLp (fun τ ↦ charFun (orthogonalProjectionKernel μ φ) τ) 2 volume
    simpa only [orthogonalProjectionKernel_apply, charFun_orthogonalProjection] using hφ
  have hθd := kernelDensity_L2_of_memLp_charFun (orthogonalProjectionKernel μ) hθ'
  have hφd := kernelDensity_L2_of_memLp_charFun (orthogonalProjectionKernel μ) hφ'
  have hfm : Measurable (orthogonalProjectionDensity μ φ) := by
    exact (measurable_orthogonalProjectionDensity μ).comp
      (measurable_const.prodMk measurable_id)
  have hgm : Measurable (orthogonalProjectionDensity μ θ) := by
    exact (measurable_orthogonalProjectionDensity μ).comp
      (measurable_const.prodMk measurable_id)
  have hd := map_add_const_eq_withDensity (orthogonalProjectionKernel μ φ) hfm hφd.2.2.1 v
  have h := integral_density_sub_sq_eq_charFun
    ((orthogonalProjectionKernel μ φ).map (fun x ↦ x + v)) (orthogonalProjectionKernel μ θ)
    (memLp_charFun_map_add_const _ hφ' v) hθ' (by fun_prop) hgm.aemeasurable
    (fun x ↦ orthogonalProjectionDensity_nonneg μ φ (x - v))
    (orthogonalProjectionDensity_nonneg μ θ) hd hθd.2.2.1
  simpa only [orthogonalProjectionKernel_apply, charFun_translated_orthogonalProjection,
    charFun_orthogonalProjection] using h

/-- The translated projection difference is square-integrable whenever both fibers are. -/
theorem memLp_orthogonalProjectionDensity_sub
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (θ φ v : ℝ)
    (hθ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection θ)) 2 volume)
    (hφ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection φ)) 2 volume) :
    MemLp (fun t ↦ orthogonalProjectionDensity μ φ (t - v) -
      orthogonalProjectionDensity μ θ t) 2 volume := by
  have hθ' : MemLp (charFun (orthogonalProjectionKernel μ θ)) 2 volume := by
    change MemLp (fun τ ↦ charFun (orthogonalProjectionKernel μ θ) τ) 2 volume
    simpa only [orthogonalProjectionKernel_apply, charFun_orthogonalProjection] using hθ
  have hφ' : MemLp (charFun (orthogonalProjectionKernel μ φ)) 2 volume := by
    change MemLp (fun τ ↦ charFun (orthogonalProjectionKernel μ φ) τ) 2 volume
    simpa only [orthogonalProjectionKernel_apply, charFun_orthogonalProjection] using hφ
  have hφd := (kernelDensity_L2_of_memLp_charFun (orthogonalProjectionKernel μ) hφ').2.1
  have hθd := (kernelDensity_L2_of_memLp_charFun (orthogonalProjectionKernel μ) hθ').2.1
  have htrans := hφd.comp_measurePreserving (measurePreserving_add_right volume (-v))
  simpa only [Function.comp_def, Pi.sub_apply, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply,
    orthogonalProjectionDensity] using! htrans.sub hθd

/-- The squared comparison as a positive extended integral, suited to a second averaging measure. -/
theorem lintegral_orthogonalProjectionDensity_sub_sq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (θ φ v : ℝ)
    (hθ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection θ)) 2 volume)
    (hφ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection φ)) 2 volume) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((orthogonalProjectionDensity μ φ (t - v) -
      orthogonalProjectionDensity μ θ t) ^ 2) =
        ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ τ : ℝ,
          ‖Complex.exp (Complex.I * (τ * v)) * charFun μ (τ • angularDirection φ) -
            charFun μ (τ • angularDirection θ)‖ₑ ^ 2 := by
  have hθ' : MemLp (charFun (μ.map (fun x ↦ ⟪x, angularDirection θ⟫))) 2 volume := by
    change MemLp (fun τ ↦ charFun (μ.map (fun x ↦ ⟪x, angularDirection θ⟫)) τ) 2 volume
    simpa only [charFun_orthogonalProjection] using hθ
  have hφ' : MemLp (charFun (μ.map (fun x ↦ ⟪x, angularDirection φ⟫))) 2 volume := by
    change MemLp (fun τ ↦ charFun (μ.map (fun x ↦ ⟪x, angularDirection φ⟫)) τ) 2 volume
    simpa only [charFun_orthogonalProjection] using hφ
  have hFourier : MemLp (fun τ : ℝ ↦
      Complex.exp (Complex.I * (τ * v)) * charFun μ (τ • angularDirection φ) -
        charFun μ (τ • angularDirection θ)) 2 volume := by
    have hh := (memLp_charFun_map_add_const _ hφ' v).sub hθ'
    change MemLp (fun τ ↦ charFun
      ((μ.map (fun x ↦ ⟪x, angularDirection φ⟫)).map (fun x ↦ x + v)) τ -
        charFun (μ.map (fun x ↦ ⟪x, angularDirection θ⟫)) τ) 2 volume at hh
    simpa only [charFun_translated_orthogonalProjection, charFun_orthogonalProjection] using hh
  have hF := ofReal_integral_eq_lintegral_ofReal
    (memLp_orthogonalProjectionDensity_sub μ θ φ v hθ hφ).integrable_sq
    (Eventually.of_forall fun _ ↦ sq_nonneg _)
  have hG := ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hFourier.aestronglyMeasurable).mp hFourier)
    (Eventually.of_forall fun _ ↦ sq_nonneg _)
  rw [← hF, integral_orthogonalProjectionDensity_sub_sq μ θ φ v hθ hφ,
    ENNReal.ofReal_mul (by positivity), hG]
  simp only [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- An angle law dominated by angular Lebesgue measure avoids exceptional projection fibers. -/
theorem ae_memLp_charFun_composed_angle
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) (θ : α → ℝ) (A : ℝ≥0∞)
    (hθ : Measurable θ) (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi) :
    ∀ᵐ z ∂κ, MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection (θ z))) 2 volume := by
  have ha := ae_memLp_charFun_on_line μ hs hs₂ hfr
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc] at ha
  have hb := (ae_restrict_iff' measurableSet_Icc).mp ha
  have hc := ae_of_ae_map hθ.aemeasurable
    ((Measure.absolutelyContinuous_of_le_smul hdom).ae_le hb)
  filter_upwards [hc, hrange] with z hz hzrange
  exact hz hzrange

/-- Plancherel comparison remains valid for arbitrary correlated direction and shift maps. -/
theorem lintegral_correlated_projectionDensity_sub_sq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) :
    (∫⁻ z, ∫⁻ t : ℝ, ENNReal.ofReal ((orthogonalProjectionDensity μ (φ z) (t - v z) -
      orthogonalProjectionDensity μ (θ z) t) ^ 2) ∂volume ∂κ) =
        ENNReal.ofReal (2 * Real.pi)⁻¹ * ∫⁻ z, ∫⁻ τ : ℝ,
          ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
            charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ := by
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_congr_ae
  filter_upwards [ae_memLp_charFun_composed_angle μ hs hs₂ hfr κ θ A hθ hθdom
    (hrange.mono fun _ h ↦ h.1),
    ae_memLp_charFun_composed_angle μ hs hs₂ hfr κ φ A hφ hφdom
      (hrange.mono fun _ h ↦ h.2)] with z hz hz'
  exact lintegral_orthogonalProjectionDensity_sub_sq μ (θ z) (φ z) (v z) hz hz'

/-- The actual density comparison is jointly measurable, even on exceptional fibers. -/
@[fun_prop]
theorem measurable_correlated_projectionDensity_sub
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    {α : Type*} [MeasurableSpace α] {θ φ v : α → ℝ}
    (hθ : Measurable θ) (hφ : Measurable φ) (hv : Measurable v) :
    Measurable (fun p : α × ℝ ↦ orthogonalProjectionDensity μ (φ p.1) (p.2 - v p.1) -
      orthogonalProjectionDensity μ (θ p.1) p.2) := by
  exact ((measurable_orthogonalProjectionDensity μ).comp
    ((hφ.comp measurable_fst).prodMk (measurable_snd.sub (hv.comp measurable_fst)))).sub
      ((measurable_orthogonalProjectionDensity μ).comp
        ((hθ.comp measurable_fst).prodMk measurable_snd))

/-- The correlated Fourier estimate controls differences of the actual nonnegative densities. -/
theorem exists_correlated_projectionDensity_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) → (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) →
          (∫⁻ z, ∫⁻ t : ℝ,
            ENNReal.ofReal ((orthogonalProjectionDensity μ (φ z) (t - v z) -
              orthogonalProjectionDensity μ (θ z) t) ^ 2) ∂volume ∂κ) ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hbound⟩ := exists_correlated_shifted_charFun_energy_bound μ hs hs₂ hfr
  refine ⟨B / (2 * Real.pi), by positivity, ?_⟩
  intro r hr hsource α _ κ _ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound
  rw [lintegral_correlated_projectionDensity_sub_sq μ hs hs₂ hfr κ θ φ v A hθ hφ
    hθdom hφdom hrange]
  refine (mul_le_mul' le_rfl (hbound r hr hsource κ θ φ v A hθ hφ hv hθdom hφdom
    hrange hclose hvbound)).trans_eq ?_
  have hconst : ENNReal.ofReal (B / (2 * Real.pi) * r ^ (2 * s - 2)) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
    calc
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * (B * r ^ (2 * s - 2))) := by
        congr 1
        ring
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ENNReal.ofReal (B * r ^ (2 * s - 2)) := ENNReal.ofReal_mul (by positivity)
      _ = _ := by rw [ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [hconst]
  ac_rfl

end FalconerPacking
