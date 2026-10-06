/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialPlancherel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circular averages and polar Plancherel

Full-turn angular integration is invariant under shifts. Polar integration therefore
turns the planar radialized Plancherel identity into equality of circular energies
with the exact planar radial weight.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Bochner integration over the fixed angular chart is invariant under periodic shifts. -/
theorem integral_radialAngularMeasure_comp_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Function.Periodic f (2 * Real.pi)) (c : ℝ) :
    (∫ θ, f (θ + c) ∂radialAngularMeasure) = ∫ θ, f θ ∂radialAngularMeasure := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  change (∫ θ in Ioc (-Real.pi) Real.pi, f (θ + c)) =
    ∫ θ in Ioc (-Real.pi) Real.pi, f θ
  rw [← intervalIntegral.integral_of_le hpi, ← intervalIntegral.integral_of_le hpi,
    intervalIntegral.integral_comp_add_right]
  convert hf.intervalIntegral_add_eq (-Real.pi + c) (-Real.pi) using 1 <;>
    congr 1 <;> ring

/-- Unit direction in exponential coordinates. -/
theorem angularDirection_eq_exp (θ : ℝ) :
    angularDirection θ =
      Complex.orthonormalBasisOneI.repr (Complex.exp (θ * Complex.I)) := by
  simp only [angularDirection, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- Actual planar rotations add the angular parameters. -/
theorem planarRotation_angularDirection (θ φ : ℝ) :
    planarRotation θ (angularDirection φ) = angularDirection (θ + φ) := by
  rw [planarRotation_apply, angularDirection_eq_exp, angularDirection_eq_exp]
  simp only [LinearIsometryEquiv.symm_apply_apply, Complex.ofReal_add, add_mul,
    Complex.exp_add]

/-- The normalized circle mean at radius `r`, including zero and negative radii. -/
def circularAverage (f : EuclideanSpace ℝ (Fin 2) → ℂ) (r : ℝ) : ℂ :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • ∫ θ, f (r • angularDirection θ) ∂radialAngularMeasure

/-- The radial average is the same circle mean at every angle. -/
theorem radialFourierAverage_smul_angularDirection
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (r φ : ℝ) :
    radialFourierAverage f (r • angularDirection φ) = circularAverage f r := by
  have hp : Function.Periodic (fun θ ↦ f (r • angularDirection θ)) (2 * Real.pi) := by
    intro θ
    simp only [angularDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]
  simp only [radialFourierAverage, circularAverage, map_smul,
    planarRotation_angularDirection]
  rw [integral_radialAngularMeasure_comp_add hp φ]

@[fun_prop]
theorem measurable_circularAverage {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Measurable f) : Measurable (circularAverage f) := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ ↦ f (p.1 • angularDirection p.2)) :=
    (by fun_prop : Measurable (fun p : ℝ × ℝ ↦ f (p.1 • angularDirection p.2))).stronglyMeasurable
  exact ((hm.integral_prod_right (f := fun r θ ↦ f (r • angularDirection θ))
    (ν := radialAngularMeasure)).const_smul ((((2 * Real.pi)⁻¹ : ℝ) : ℂ))).measurable

@[fun_prop]
theorem measurable_radialFourierAverage {f : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hf : Measurable f) : Measurable (radialFourierAverage f) := by
  have hm : StronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦ f (planarRotation p.2 p.1)) :=
    (hf.comp (continuous_planarRotation.comp continuous_swap).measurable).stronglyMeasurable
  exact ((hm.integral_prod_right (f := fun x θ ↦ f (planarRotation θ x))
    (ν := radialAngularMeasure)).const_smul ((((2 * Real.pi)⁻¹ : ℝ) : ℂ))).measurable

/-- Positive planar energy of the radial average is exactly `2π` times weighted circle energy. -/
theorem lintegral_sq_norm_radialFourierAverage
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (‖radialFourierAverage f x‖ ^ 2)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
          ENNReal.ofReal (‖circularAverage f r‖ ^ 2) := by
  rw [← lintegral_polar_euclidean]
  simp_rw [radialFourierAverage_smul_angularDirection]
  rw [Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]

/-- Weighted circular Plancherel for Schwartz functions, in nonnegative-integral form. -/
theorem circularAverage_plancherel_lintegral
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * ENNReal.ofReal (‖circularAverage f r‖ ^ 2)) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        ENNReal.ofReal (‖circularAverage (𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)) r‖ ^ 2) := by
  have h₁ := (memLp_radialFourierAverage f.integrable (f.memLp 2 volume)).integrable_norm_pow
    (by norm_num : 2 ≠ 0)
  have h₂ := (memLp_radialFourierAverage (𝓕 f).integrable
    ((𝓕 f).memLp 2 volume)).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have h := congrArg ENNReal.ofReal (radialFourierAverage_plancherel f)
  rw [ofReal_integral_eq_lintegral_ofReal h₁ (ae_of_all _ fun _ ↦ sq_nonneg _)] at h
  rw [← SchwartzMap.fourier_coe] at h
  rw [ofReal_integral_eq_lintegral_ofReal h₂ (ae_of_all _ fun _ ↦ sq_nonneg _),
    lintegral_sq_norm_radialFourierAverage f.continuous.measurable,
    lintegral_sq_norm_radialFourierAverage (𝓕 f).continuous.measurable] at h
  simpa only [SchwartzMap.fourier_coe] using
    (ENNReal.mul_right_inj (by positivity) ENNReal.ofReal_ne_top).1 h

/-- The weighted circle energy is finite for any measurable `L¹ ∩ L²` source. -/
theorem lintegral_weighted_circularAverage_lt_top
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f)
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
      ENNReal.ofReal (‖circularAverage f r‖ ^ 2)) < ⊤ := by
  have hi := (memLp_radialFourierAverage hf₁ hf₂).integrable_norm_pow
    (by norm_num : 2 ≠ 0)
  have hfin := (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ sq_nonneg _)).1 hi.2
  rw [lintegral_sq_norm_radialFourierAverage hf] at hfin
  rcases ENNReal.mul_lt_top_iff.1 hfin with h | h | h
  · exact h.2
  · exact False.elim ((by positivity : ENNReal.ofReal (2 * Real.pi) ≠ 0) h)
  · rw [h]
    exact ENNReal.zero_lt_top

/-- Convert the positive weighted circle energy to its real integral. -/
theorem integral_weighted_circularAverage_eq_toReal
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) :
    (∫ r in Ioi (0 : ℝ), r * ‖circularAverage f r‖ ^ 2) =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        ENNReal.ofReal (‖circularAverage f r‖ ^ 2)).toReal := by
  rw [← integral_toReal (by fun_prop) (ae_of_all _ fun _ ↦
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The radius-weighted squared circle mean is an actual integrable function. -/
theorem integrableOn_weighted_circularAverage
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f)
    (hf₁ : Integrable f volume) (hf₂ : MemLp f 2 volume) :
    IntegrableOn (fun r ↦ r * ‖circularAverage f r‖ ^ 2) (Ioi (0 : ℝ)) volume := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun r ↦ r * ‖circularAverage f r‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg hr.le (sq_nonneg _)
  refine ⟨(by fun_prop : Measurable (fun r ↦ r * ‖circularAverage f r‖ ^ 2)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal hnonneg).2 ?_⟩
  convert lintegral_weighted_circularAverage_lt_top hf hf₁ hf₂ using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact ENNReal.ofReal_mul hr.le

/-- The exact weighted circular Plancherel formula with ordinary finite real integrals. -/
theorem circularAverage_plancherel
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    (∫ r in Ioi (0 : ℝ), r * ‖circularAverage f r‖ ^ 2) =
      ∫ r in Ioi (0 : ℝ), r *
        ‖circularAverage (𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)) r‖ ^ 2 := by
  rw [integral_weighted_circularAverage_eq_toReal f.continuous.measurable,
    integral_weighted_circularAverage_eq_toReal
      (show Measurable (𝓕 (f : EuclideanSpace ℝ (Fin 2) → ℂ)) from
        (SchwartzMap.fourier_coe f) ▸ (𝓕 f).continuous.measurable),
    circularAverage_plancherel_lintegral f]

end FalconerPacking
