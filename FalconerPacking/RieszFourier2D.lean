/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.GaussianMellin
import FalconerPacking.ProjectionFourier

/-!
# Planar Riesz energy and angular Sobolev Fourier energy

The same positive Mellin identity used on the real line applies to the planar Gaussian
duality formula. Polar integration then identifies the averaged one-dimensional Sobolev energy.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Gaussian Fourier energy of a finite planar measure, as a positive extended integral. -/
theorem lintegral_gaussian_charFun_norm_sq_planar
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] {b : ℝ} (hb : 0 < b) :
    ∫⁻ ξ : EuclideanSpace ℝ (Fin 2), ENNReal.ofReal (Real.exp (-b * ‖ξ‖ ^ 2)) *
      ENNReal.ofReal (‖charFun μ ξ‖ ^ 2) =
        ENNReal.ofReal ((Real.pi / b) ^ ((2 : ℝ) / 2)) *
          ∫⁻ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2), ENNReal.ofReal
            (Real.exp (-(dist p.1 p.2 ^ 2 / (4 * b)))) ∂μ.prod μ := by
  have hg : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-b * ‖ξ‖ ^ 2)) volume := by
    simpa using integrable_gaussian_charFun_energy
      (Measure.dirac (0 : EuclideanSpace ℝ (Fin 2))) hb
  have hf : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2) := by
    apply (hg.mul_const (μ.real univ ^ 2)).mono' (by fun_prop)
    exact Eventually.of_forall fun ξ ↦ by
      have hs := (sq_le_sq₀ (norm_nonneg _) ENNReal.toReal_nonneg).mpr
        (norm_charFun_le (μ := μ) ξ)
      simpa only [measureReal_def, Real.norm_eq_abs, abs_of_nonneg (by positivity :
        0 ≤ Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2)] using
          mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
  have hk : Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b)))) (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hf' := ofReal_integral_eq_lintegral_ofReal hf
    (Eventually.of_forall fun ξ ↦ mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have hk' := ofReal_integral_eq_lintegral_ofReal hk
    (Eventually.of_forall fun p ↦ Real.exp_nonneg _)
  simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), dist_eq_norm]
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  rw [← hf', ← hk', ← ENNReal.ofReal_mul (by positivity),
    integral_gaussian_charFun_norm_sq μ hb]

/-- The planar Fourier energy with the Riesz weight. -/
def rieszFourierEnergy2D (μ : Measure (EuclideanSpace ℝ (Fin 2))) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : EuclideanSpace ℝ (Fin 2),
    ENNReal.ofReal ‖ξ‖ ^ (t - 2) * ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)

/-- The exact planar Fourier/Riesz identity with the positive Gamma factors displayed. -/
theorem rieszFourierEnergy2D_mul_gamma
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht₂ : t < 2) :
    ENNReal.ofReal (Real.Gamma ((2 - t) / 2)) * rieszFourierEnergy2D μ t =
      ENNReal.ofReal (Real.pi ^ ((2 : ℝ) / 2) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) *
        rieszEnergy μ t := by
  have h := riesz_fourier_identity_of_gaussian volume (μ.prod μ)
    (ρ := fun ξ : EuclideanSpace ℝ (Fin 2) ↦ ‖ξ‖)
    (σ := fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦ dist p.1 p.2)
    (by fun_prop) (by fun_prop) norm_nonneg (fun _ ↦ dist_nonneg)
    (f := fun ξ ↦ ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)) (by fun_prop)
    ht ht₂ (fun b hb ↦ lintegral_gaussian_charFun_norm_sq_planar μ hb)
  rw [lintegral_prod _ (by fun_prop)] at h
  exact h

/-- The planar Fourier/Riesz identity, including infinite energies. -/
theorem rieszFourierEnergy2D_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht₂ : t < 2) :
    rieszFourierEnergy2D μ t =
      ENNReal.ofReal (rieszFourierConstant 2 t) * rieszEnergy μ t := by
  have hg := Real.Gamma_pos_of_pos (show 0 < (2 - t) / 2 by linarith)
  have h := (ENNReal.eq_div_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hg))
    ENNReal.ofReal_ne_top).mpr (rieszFourierEnergy2D_mul_gamma μ ht ht₂)
  rw [rieszFourierConstant, ENNReal.ofReal_div_of_pos hg]
  exact h.trans (by simp only [div_eq_mul_inv]; ring)

/-- Polar integration identifies the positive radial Sobolev energy with planar Riesz energy. -/
theorem lintegral_angular_charFun_rpow_pos
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht₂ : t < 2) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal r ^ (t - 1) * ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) =
        ENNReal.ofReal (rieszFourierConstant 2 t) * rieszEnergy μ t := by
  rw [← rieszFourierEnergy2D_eq μ ht ht₂]
  have hpolar := lintegral_polar_euclidean (fun ξ ↦
    ENNReal.ofReal ‖ξ‖ ^ (t - 2) * ENNReal.ofReal (‖charFun μ ξ‖ ^ 2))
  rw [← setLIntegral_prod_symm (fun p : ℝ × ℝ ↦
    ENNReal.ofReal p.1 ^ (t - 1) *
      ENNReal.ofReal (‖charFun μ (p.1 • angularDirection p.2)‖ ^ 2)) (by fun_prop)]
  apply Eq.trans _ hpolar
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  dsimp only
  have hr : 0 < p.1 := hp.1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularDirection, mul_one,
    ← mul_assoc]
  congr 1
  have hpow := ENNReal.rpow_add (x := ENNReal.ofReal p.1) 1 (t - 2)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top
  simpa only [ENNReal.rpow_one, show 1 + (t - 2) = t - 1 by ring] using hpow

/-- Both radial orientations contribute the same Sobolev energy. -/
theorem lintegral_angular_charFun_rpow
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht₂ : t < 2) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r : ℝ,
      ENNReal.ofReal |r| ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) =
          2 * ENNReal.ofReal (rieszFourierConstant 2 t) * rieszEnergy μ t := by
  have heven (θ r : ℝ) :
      ENNReal.ofReal |(-r)| ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ ((-r) • angularDirection θ)‖ ^ 2) =
      ENNReal.ofReal |r| ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) := by
    simp only [abs_neg, neg_smul, charFun_neg, RCLike.norm_conj]
  have hhalf (θ : ℝ) :
      (∫⁻ r : ℝ, ENNReal.ofReal |r| ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2)) =
      2 * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) := by
    rw [← lintegral_add_compl _ measurableSet_Ioi, compl_Ioi,
      ← setLIntegral_congr Iio_ae_eq_Iic, lintegral_Iio_eq_Ioi_of_even (heven θ),
      ← two_mul]
    congr 1
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [abs_of_pos (show 0 < r from hr)]
  simp_rw [hhalf]
  rw [lintegral_const_mul' _ _ (by norm_num),
    lintegral_angular_charFun_rpow_pos μ ht ht₂, mul_assoc]

/-- Finite planar Riesz energy gives finite averaged linewise Sobolev energy. -/
theorem lintegral_angular_charFun_rpow_lt_top
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 < t) (ht₂ : t < 2) (hE : rieszEnergy μ t < ∞) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r : ℝ,
      ENNReal.ofReal |r| ^ (t - 1) *
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2)) < ∞ := by
  rw [lintegral_angular_charFun_rpow μ ht ht₂]
  exact ENNReal.mul_lt_top (by finiteness) hE

end FalconerPacking
