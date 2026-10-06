/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionWeakMoment
public import FalconerPacking.SmoothProjectionDensity
public import FalconerPacking.RieszFourier2D

/-!
# Trace bounds for actual smooth projection densities

The Fourier transform of each positive Schwartz line density is identified with the
characteristic function of the corresponding projected source measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SchwartzMap FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The inverse Fourier transform of a positive real Schwartz density is its characteristic
function in the matching normalization. This is a pointwise identity. -/
theorem fourierInv_positive_schwartz_eq_charFun
    (φ : SchwartzMap ℝ ℂ) (hpos : ∀ x, 0 ≤ (φ x).re) (him : ∀ x, (φ x).im = 0)
    (ξ : ℝ) :
    (𝓕⁻ φ) ξ = charFun (volume.withDensity (fun x ↦ ENNReal.ofReal (φ x).re))
      (2 * Real.pi * ξ) := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, charFun_apply_real,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hx : ((φ x).re : ℂ) = φ x := by
    simpa only [him x, Complex.ofReal_zero, zero_mul, add_zero] using Complex.re_add_im (φ x)
  simp only [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply,
    ENNReal.toReal_ofReal (hpos x), Complex.real_smul, smul_eq_mul]
  rw [← hx, mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- The Fourier identity for an actual positive Schwartz density of a planar projection. -/
theorem fourierInv_positive_schwartz_projection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℂ) (v : EuclideanSpace ℝ (Fin 2))
    (hpos : ∀ x, 0 ≤ (φ x).re) (him : ∀ x, (φ x).im = 0)
    (hdensity : μ.map (fun x ↦ ⟪x, v⟫) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (φ t).re)) (ξ : ℝ) :
    (𝓕⁻ φ) ξ = charFun μ ((2 * Real.pi * ξ) • v) := by
  rw [fourierInv_positive_schwartz_eq_charFun φ hpos him,
    ← hdensity, charFun_orthogonalProjection]

/-- Riesz energy transforms by the exact spatial-dilation factor. -/
theorem rieszEnergy_map_smul_planar
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] (c t : ℝ) :
    rieszEnergy (μ.map (fun x ↦ c • x)) t =
      ENNReal.ofReal |c| ^ (-t) * rieszEnergy μ t := by
  unfold rieszEnergy rieszKernel
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hmap (x : EuclideanSpace ℝ (Fin 2)) :
      (∫⁻ y, ENNReal.ofReal (dist x y) ^ (-t) ∂μ.map (fun z ↦ c • z)) =
      ∫⁻ y, ENNReal.ofReal (dist x (c • y)) ^ (-t) ∂μ :=
    lintegral_map (by fun_prop) (by fun_prop)
  simp_rw [hmap]
  simp only [dist_smul₀, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg c),
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  have hconst (x : EuclideanSpace ℝ (Fin 2)) :=
    lintegral_const_mul (ENNReal.ofReal |c| ^ (-t))
      (show Measurable (fun y ↦ ENNReal.ofReal (dist x y) ^ (-t)) from by fun_prop)
      (μ := μ)
  simp_rw [hconst]
  rw [lintegral_const_mul _ (by fun_prop)]

/-- Averaged linewise Sobolev energy in the normalization used by Schwartz inversion. -/
theorem lintegral_angular_charFun_scaled_rpow
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht₂ : t < 2) (c : ℝ) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r : ℝ,
      ENNReal.ofReal |r| ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ ((c * r) • angularDirection θ)‖ ^ 2)) =
      2 * ENNReal.ofReal (rieszFourierConstant 2 t) *
        (ENNReal.ofReal |c| ^ (-t) * rieszEnergy μ t) := by
  have heq (θ r : ℝ) : charFun μ ((c * r) • angularDirection θ) =
      charFun (μ.map (fun x ↦ c • x)) (r • angularDirection θ) := by
    rw [charFun_map_smul, smul_smul]
  simp_rw [heq]
  rw [lintegral_angular_charFun_rpow _ ht ht₂, rieszEnergy_map_smul_planar]

end FalconerPacking
