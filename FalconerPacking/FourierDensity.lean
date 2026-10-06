/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SchwartzDensityCriterion
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Square-integrable Fourier transforms of finite measures

Fourier inversion, Fubini and Plancherel control integration against Schwartz functions.
Smooth cutoffs then give absolute continuity. The fundamental lemma for smooth tests
identifies the inverse `L²` Fourier transform with the Radon--Nikodym density. With the
probability normalization `charFun`, its squared `L²` norm is `(2π)⁻¹` times Fourier energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal ContDiff

namespace FalconerPacking

/-- The Fourier transform of a finite measure in mathlib's `2π` normalization. -/
def measureFourier (μ : Measure ℝ) (ξ : ℝ) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ ℝ) 1 ξ

/-- This normalization is obtained from the characteristic function by a frequency dilation. -/
theorem measureFourier_eq_charFun (μ : Measure ℝ) (ξ : ℝ) :
    measureFourier μ ξ = charFun μ (-2 * Real.pi * ξ) := by
  simp only [measureFourier, VectorFourier.fourierIntegral, innerₗ_apply_apply,
    Real.inner_apply, Circle.smul_def, Pi.one_apply, Real.fourierChar_apply, smul_eq_mul, mul_one,
    charFun_apply_real]
  congr 1
  funext x
  congr 1
  push_cast
  ring

theorem continuous_measureFourier (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (measureFourier μ) := by
  change Continuous (fun ξ ↦ measureFourier μ ξ)
  simp_rw [measureFourier_eq_charFun]
  exact continuous_charFun.comp (continuous_const.mul continuous_id)

/-- The choice between probability and `2π` Fourier normalization does not affect `L²`. -/
theorem memLp_measureFourier_iff (μ : Measure ℝ) [IsFiniteMeasure μ] :
    MemLp (measureFourier μ) 2 volume ↔ MemLp (charFun μ) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (continuous_measureFourier μ).aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm continuous_charFun.aestronglyMeasurable]
  simp_rw [measureFourier_eq_charFun]
  exact integrable_comp_mul_left_iff (fun x ↦ ‖charFun μ x‖ ^ 2)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

/-- The exact normalization factor for Fourier square energy on the real line. -/
theorem integral_norm_sq_measureFourier (μ : Measure ℝ) :
    ∫ ξ, ‖measureFourier μ ξ‖ ^ 2 =
      (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun μ ξ‖ ^ 2 := by
  simp_rw [measureFourier_eq_charFun]
  rw [Measure.integral_comp_mul_left (fun ξ ↦ ‖charFun μ ξ‖ ^ 2) (-2 * Real.pi)]
  congr 1
  rw [abs_inv, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), abs_of_pos Real.pi_pos]
  norm_num

/-- Fubini's identity holds for the actual measure Fourier integral. -/
theorem integral_measureFourier_schwartz (μ : Measure ℝ) [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℂ) :
    ∫ ξ, measureFourier μ ξ * φ ξ = ∫ x, (𝓕 φ) x ∂μ := by
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (μ := μ) (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar
    continuous_inner (integrable_const (1 : ℂ)) φ.integrable
  simpa only [hflip, measureFourier, smul_eq_mul, Pi.one_apply, one_mul,
    SchwartzMap.fourier_coe] using! h

/-- Fourier inversion on the test function identifies integration against the measure. -/
theorem integral_schwartz_eq_measureFourier (μ : Measure ℝ) [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℂ) :
    ∫ x, φ x ∂μ = ∫ ξ, measureFourier μ ξ * (𝓕⁻ φ) ξ := by
  rw [integral_measureFourier_schwartz, fourier_fourierInv_eq]

/-- Cauchy--Schwarz for the integral of a product, expressed through `eLpNorm`. -/
theorem norm_integral_mul_le_eLpNorm_two {f g : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖∫ x, f x * g x‖ ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    hg.aestronglyMeasurable hf.aestronglyMeasurable
  have hnorm : ‖∫ x, f x * g x‖ₑ ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    rw [eLpNorm_one_eq_lintegral_enorm
      (hg.aestronglyMeasurable.smul hf.aestronglyMeasurable)] at h
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, mul_comm] using h
  have hfin : eLpNorm f 2 volume * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  simpa only [ENNReal.toReal_mul, toReal_enorm] using ENNReal.toReal_mono hfin hnorm

/-- The Fourier `L²` norm controls every Schwartz test against the original measure. -/
theorem norm_integral_schwartz_le_measureFourier_L2
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    ‖∫ x, φ x ∂μ‖ ≤ (eLpNorm (measureFourier μ) 2 volume).toReal * ‖φ.toLp 2 volume‖ := by
  rw [integral_schwartz_eq_measureFourier]
  have h := norm_integral_mul_le_eLpNorm_two hμ ((𝓕⁻ φ).memLp 2 volume)
  have hnorm : ‖(𝓕⁻ φ).toLp 2 volume‖ = ‖φ.toLp 2 volume‖ := by
    simpa only [fourier_fourierInv_eq] using (norm_fourier_toL2_eq (𝓕⁻ φ)).symm
  simpa only [← SchwartzMap.norm_toLp, hnorm] using h

/-- The distributional Fourier transform of the measure is its actual Fourier integral. -/
theorem fourier_measure_toTemperedDistribution
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    𝓕 μ.toTemperedDistribution =
      (hμ.toLp (measureFourier μ) : TemperedDistribution ℝ ℂ) := by
  ext φ
  simp only [TemperedDistribution.fourier_apply, Measure.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  rw [← integral_measureFourier_schwartz]
  apply integral_congr_ae
  filter_upwards [hμ.coeFn_toLp] with x hx
  simp only [hx, smul_eq_mul, mul_comm]

/-- The inverse `L²` Fourier transform provides the candidate density. -/
def measureFourierDensity (μ : Measure ℝ) (hμ : MemLp (measureFourier μ) 2 volume) :
    Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ (hμ.toLp (measureFourier μ))

/-- The candidate density represents the original measure on every Schwartz test. -/
theorem measure_toTemperedDistribution_eq_fourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    μ.toTemperedDistribution = (measureFourierDensity μ hμ : TemperedDistribution ℝ ℂ) := by
  calc
    μ.toTemperedDistribution = 𝓕⁻ (𝓕 μ.toTemperedDistribution) :=
      (fourierInv_fourier_eq _).symm
    _ = 𝓕⁻ (hμ.toLp (measureFourier μ) : TemperedDistribution ℝ ℂ) := by
      rw [fourier_measure_toTemperedDistribution μ hμ]
    _ = (measureFourierDensity μ hμ : TemperedDistribution ℝ ℂ) :=
      Lp.fourierInv_toTemperedDistribution_eq _

theorem integral_schwartz_eq_fourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume)
    (φ : SchwartzMap ℝ ℂ) :
    ∫ x, φ x ∂μ = ∫ x, φ x * measureFourierDensity μ hμ x := by
  have h := congrArg (fun T : TemperedDistribution ℝ ℂ ↦ T φ)
    (measure_toTemperedDistribution_eq_fourierDensity μ hμ)
  simpa only [Measure.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] using h

/-- Plancherel gives the exact norm of the candidate density. -/
theorem norm_measureFourierDensity (μ : Measure ℝ) (hμ : MemLp (measureFourier μ) 2 volume) :
    ‖measureFourierDensity μ hμ‖ = (eLpNorm (measureFourier μ) 2 volume).toReal := by
  have h := (Lp.norm_fourier_eq (𝓕⁻ (hμ.toLp (measureFourier μ)))).symm
  simpa only [measureFourierDensity, fourier_fourierInv_eq, Lp.norm_toLp] using h

/-- Square-integrability of the measure Fourier transform implies absolute continuity. -/
theorem absolutelyContinuous_of_memLp_measureFourier
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    μ ≪ volume :=
  absolutelyContinuous_of_schwartz_L2_bound ENNReal.toReal_nonneg
    (norm_integral_schwartz_le_measureFourier_L2 μ hμ)

/-- Equivalently, a finite measure with square-integrable characteristic function is
absolutely continuous. -/
theorem absolutelyContinuous_of_memLp_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (charFun μ) 2 volume) : μ ≪ volume :=
  absolutelyContinuous_of_memLp_measureFourier μ ((memLp_measureFourier_iff μ).mpr hμ)

/-- The inverse Fourier candidate agrees almost everywhere with the Radon--Nikodym density. -/
theorem rnDeriv_ae_eq_measureFourierDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    (fun x ↦ ((μ.rnDeriv volume x).toReal : ℂ)) =ᵐ[volume] measureFourierDensity μ hμ := by
  have hac := absolutelyContinuous_of_memLp_measureFourier μ hμ
  have hr : Integrable (fun x ↦ (μ.rnDeriv volume x).toReal) volume := by
    simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := volume) (s := Set.univ)
        (measure_ne_top μ Set.univ))
  apply ae_eq_of_integral_contDiff_smul_eq hr.ofReal.locallyIntegrable
    ((Lp.memLp (measureFourierDensity μ hμ)).locallyIntegrable (by norm_num))
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have h := integral_schwartz_eq_fourierDensity μ hμ (hc'.toSchwartzMap hg')
  rw [← integral_rnDeriv_smul hac] at h
  convert h using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x <;>
    simp [RCLike.real_smul_eq_coe_mul, mul_comm]

/-- A finite measure with square-integrable Fourier transform has a nonnegative `L¹ ∩ L²`
density, with exactly the same `L²` norm in the `2π` Fourier normalization. -/
theorem exists_L2_density_of_memLp_measureFourier
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (measureFourier μ) 2 volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      eLpNorm f 2 volume = eLpNorm (measureFourier μ) 2 volume := by
  let f : ℝ → ℝ := fun x ↦ (μ.rnDeriv volume x).toReal
  have hm : AEStronglyMeasurable f volume :=
    (Measure.measurable_rnDeriv μ volume).ennreal_toReal.aestronglyMeasurable
  have hn : ∀ᵐ x ∂volume, ‖measureFourierDensity μ hμ x‖ = ‖f x‖ := by
    filter_upwards [rnDeriv_ae_eq_measureFourierDensity μ hμ] with x hx
    rw [← hx]
    simp only [f, Complex.norm_real, Real.norm_eq_abs]
  have hf := (Lp.memLp (measureFourierDensity μ hμ)).congr_norm hm hn
  refine ⟨f, fun _ ↦ ENNReal.toReal_nonneg, ?_, hf, ?_, ?_⟩
  · simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := volume) (s := Set.univ)
        (measure_ne_top μ Set.univ))
  · rw [← Measure.withDensity_rnDeriv_eq μ volume
      (absolutelyContinuous_of_memLp_measureFourier μ hμ)]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top μ volume] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  · rw [← eLpNorm_congr_norm_ae
      (Lp.memLp (measureFourierDensity μ hμ)).aestronglyMeasurable hm hn,
      ← Lp.enorm_def, ← ofReal_norm,
      norm_measureFourierDensity, ENNReal.ofReal_toReal hμ.eLpNorm_ne_top]

/-- The characteristic-function hypothesis yields an actual nonnegative `L²` density. -/
theorem exists_L2_density_of_memLp_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (charFun μ) 2 volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      eLpNorm f 2 volume = eLpNorm (measureFourier μ) 2 volume :=
  exists_L2_density_of_memLp_measureFourier μ ((memLp_measureFourier_iff μ).mpr hμ)

/-- Express a square integral directly through the finite `L²` seminorm. -/
theorem integral_norm_sq_eq_eLpNorm_two_sq {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : MemLp f 2 volume) :
    ∫ x, ‖f x‖ ^ 2 = (eLpNorm f 2 volume).toReal ^ 2 := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hf,
    ENNReal.toReal_ofReal (by positivity)]
  norm_num
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖f x‖))]

/-- The usual probability normalization gives the precise Plancherel constant for the density. -/
theorem exists_L2_density_of_memLp_charFun_sq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : MemLp (charFun μ) 2 volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      ∫ x, f x ^ 2 = (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun μ ξ‖ ^ 2 := by
  obtain ⟨f, hf₀, hfi, hf₂, hfd, hfn⟩ := exists_L2_density_of_memLp_charFun μ hμ
  refine ⟨f, hf₀, hfi, hf₂, hfd, ?_⟩
  calc
    ∫ x, f x ^ 2 = ∫ x, ‖f x‖ ^ 2 := by simp only [Real.norm_eq_abs, sq_abs]
    _ = (eLpNorm f 2 volume).toReal ^ 2 := integral_norm_sq_eq_eLpNorm_two_sq hf₂
    _ = (eLpNorm (measureFourier μ) 2 volume).toReal ^ 2 := by rw [hfn]
    _ = ∫ ξ, ‖measureFourier μ ξ‖ ^ 2 :=
      (integral_norm_sq_eq_eLpNorm_two_sq ((memLp_measureFourier_iff μ).mpr hμ)).symm
    _ = _ := integral_norm_sq_measureFourier μ

end FalconerPacking
