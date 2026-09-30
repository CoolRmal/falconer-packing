/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Positive Mellin formulas for Gaussian kernels

All identities are stated in extended nonnegative integrals, so that the formulas continue
to hold at the singular spatial point.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The positive constant relating characteristic-function energy to spatial Riesz energy. -/
def rieszFourierConstant (d t : ℝ) : ℝ :=
  (Real.pi ^ (d / 2) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) /
    Real.Gamma ((d - t) / 2)

/-- The Fourier/Riesz constant is strictly positive in the admissible exponent range. -/
theorem rieszFourierConstant_pos {d t : ℝ} (ht : 0 < t) (htd : t < d) :
    0 < rieszFourierConstant d t := by
  unfold rieszFourierConstant
  exact div_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.Gamma_pos_of_pos (by linarith))) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))

/-- The Laplace representation of a negative power, including its infinite value at zero. -/
theorem lintegral_mellin_exp {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(c * u))) =
      ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal c ^ (-a) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, ENNReal.ofReal_zero,
      ENNReal.zero_rpow_of_neg (neg_neg_of_pos ha),
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.Gamma_pos_of_pos ha)))]
    by_contra h
    apply not_integrableOn_Ioi_rpow (a - 1)
    refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal ?_).mpr (lt_top_iff_ne_top.mpr h)⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Real.rpow_nonneg hu.le _
  · have hi : IntegrableOn (fun u : ℝ ↦ u ^ (a - 1) * Real.exp (-(c * u))) (Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1)
          (by linarith) (by norm_num) hc
    have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun u : ℝ ↦ u ^ (a - 1) * Real.exp (-(c * u)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc]
    rw [one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le,
      ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
      ENNReal.ofReal_rpow_of_pos hc, mul_comm]

/-- Inversion on the positive half-line, with its actual Jacobian. -/
theorem lintegral_Ioi_inv_jacobian (f : ℝ → ℝ≥0∞) :
    ∫⁻ u : ℝ in Ioi 0, f u =
      ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ 2)⁻¹ * f u⁻¹ := by
  have him : (fun u : ℝ ↦ u⁻¹) '' Ioi 0 = Ioi 0 := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      change 0 < v⁻¹
      exact inv_pos.mpr (show 0 < v from hv)
    · intro hu
      exact ⟨u⁻¹, show 0 < u⁻¹ from inv_pos.mpr (show 0 < u from hu), inv_inv u⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun u (hu : u ∈ Ioi (0 : ℝ)) ↦
      (hasDerivAt_inv (ne_of_gt hu)).hasDerivWithinAt) (inv_injective.injOn) f
  rw [him] at h
  simpa only [abs_neg, abs_inv, abs_pow, sq_abs] using h

/-- The inverse-scale form of the positive Laplace representation. -/
theorem lintegral_mellin_exp_inv {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (-a - 1) * Real.exp (-(c / u))) =
      ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal c ^ (-a) := by
  rw [← lintegral_mellin_exp ha hc,
    lintegral_Ioi_inv_jacobian (fun u ↦ ENNReal.ofReal
      (u ^ (a - 1) * Real.exp (-(c * u))))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu₀ : 0 < u := hu
  dsimp only
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hp : (u ^ 2)⁻¹ * (u⁻¹) ^ (a - 1) = u ^ (-a - 1) := by
    rw [Real.inv_rpow hu₀.le, ← Real.rpow_neg hu₀.le,
      ← Real.rpow_two, ← Real.rpow_neg hu₀.le, ← Real.rpow_add hu₀]
    congr 1
    ring
  rw [← mul_assoc, hp, div_eq_mul_inv]

/-- The Mellin transform of a Gaussian radial factor. -/
theorem lintegral_mellin_gaussian {a ρ : ℝ} (ha : 0 < a) (hρ : 0 ≤ ρ) :
    ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-(u * ρ ^ 2))) =
      ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal ρ ^ (-2 * a) := by
  have h := lintegral_mellin_exp ha (sq_nonneg ρ)
  simp_rw [mul_comm (ρ ^ 2)] at h
  rw [ENNReal.ofReal_pow hρ, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
  convert h using 1
  congr 2
  ring

/-- The dimensional factor in Gaussian duality can be included in the Mellin integral.
Only the energy exponent must be positive; the dimension parameter is an arbitrary real number. -/
theorem lintegral_mellin_gaussian_spatial {t ρ d : ℝ} (ht : 0 < t) (hρ : 0 ≤ ρ) :
    ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal
      (b ^ ((d - t) / 2 - 1) * (Real.pi / b) ^ (d / 2) *
        Real.exp (-(ρ ^ 2 / (4 * b)))) =
      ENNReal.ofReal (Real.pi ^ (d / 2) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) *
        ENNReal.ofReal ρ ^ (-t) := by
  have hp (b : ℝ) (hb : 0 < b) :
      b ^ ((d - t) / 2 - 1) * (Real.pi / b) ^ (d / 2) =
        Real.pi ^ (d / 2) * b ^ (-(t / 2) - 1) := by
    rw [Real.div_rpow Real.pi_pos.le hb.le,
      div_eq_mul_inv (Real.pi ^ (d / 2)) (b ^ (d / 2)),
      ← Real.rpow_neg hb.le]
    calc
      _ = Real.pi ^ (d / 2) * (b ^ ((d - t) / 2 - 1) * b ^ (-(d / 2))) := by ring
      _ = _ := by rw [← Real.rpow_add hb]; congr 2; ring
  have hpow : ENNReal.ofReal (ρ ^ 2 / 4) ^ (-(t / 2)) =
      ENNReal.ofReal ((4 : ℝ) ^ (t / 2)) * ENNReal.ofReal ρ ^ (-t) := by
    rcases hρ.eq_or_lt with rfl | hρ
    · simp [ENNReal.zero_rpow_of_neg (by linarith : -(t / 2) < 0),
        ENNReal.zero_rpow_of_neg (by linarith : -t < 0),
        ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
          (by positivity : 0 < (4 : ℝ) ^ (t / 2))))]
    · rw [ENNReal.ofReal_rpow_of_pos (by positivity : 0 < ρ ^ 2 / 4),
        ENNReal.ofReal_rpow_of_pos hρ, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [Real.div_rpow (sq_nonneg _) (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul hρ.le]
      norm_cast
      rw [show (2 : ℝ) * -(t / 2) = -t by ring,
        Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)), div_eq_mul_inv, inv_inv, mul_comm]
  calc
    _ = ENNReal.ofReal (Real.pi ^ (d / 2)) *
        ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal
          (b ^ (-(t / 2) - 1) * Real.exp (-((ρ ^ 2 / 4) / b))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro b hb
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity), hp b hb, mul_assoc]
      congr 3
      field_simp
    _ = ENNReal.ofReal (Real.pi ^ (d / 2)) *
        (ENNReal.ofReal (Real.Gamma (t / 2)) * ENNReal.ofReal (ρ ^ 2 / 4) ^ (-(t / 2))) := by
      rw [lintegral_mellin_exp_inv (by positivity) (by positivity)]
    _ = _ := by
      rw [hpow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      ring

/-- Tonelli's theorem integrates a weighted family of frequency-side Gaussians. -/
theorem lintegral_mellin_gaussian_frequency {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {ρ : X → ℝ} (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    {f : X → ℝ≥0∞} (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal (b ^ (a - 1)) *
      ∫⁻ x, ENNReal.ofReal (Real.exp (-b * ρ x ^ 2)) * f x ∂ν =
        ENNReal.ofReal (Real.Gamma a) * ∫⁻ x, ENNReal.ofReal (ρ x) ^ (-2 * a) * f x ∂ν := by
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by fun_prop)]
  have h (x : X) :
      ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal (b ^ (a - 1)) *
        (ENNReal.ofReal (Real.exp (-b * ρ x ^ 2)) * f x) =
          ENNReal.ofReal (Real.Gamma a) * (ENNReal.ofReal (ρ x) ^ (-2 * a) * f x) := by
    have he : ∀ b ∈ Ioi (0 : ℝ), ENNReal.ofReal (b ^ (a - 1)) *
        (ENNReal.ofReal (Real.exp (-b * ρ x ^ 2)) * f x) =
          ENNReal.ofReal (b ^ (a - 1) * Real.exp (-(b * ρ x ^ 2))) * f x := by
      intro b hb
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _), neg_mul]
    rw [setLIntegral_congr_fun measurableSet_Ioi he, lintegral_mul_const _ (by fun_prop),
      lintegral_mellin_gaussian ha (hρ x), mul_assoc]
  simp_rw [h]

/-- Tonelli's theorem integrates the positive spatial kernel in any dimension parameter. -/
theorem lintegral_mellin_gaussian_space {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {ρ : X → ℝ} (hρm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    {t d : ℝ} (ht : 0 < t) :
    ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal (b ^ ((d - t) / 2 - 1)) *
      (ENNReal.ofReal ((Real.pi / b) ^ (d / 2)) *
        ∫⁻ x, ENNReal.ofReal (Real.exp (-(ρ x ^ 2 / (4 * b)))) ∂ν) =
          ENNReal.ofReal (Real.pi ^ (d / 2) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) *
            ∫⁻ x, ENNReal.ofReal (ρ x) ^ (-t) ∂ν := by
  simp_rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (by fun_prop)]
  have he (x : X) :
      ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal (b ^ ((d - t) / 2 - 1)) *
        (ENNReal.ofReal ((Real.pi / b) ^ (d / 2)) *
          ENNReal.ofReal (Real.exp (-(ρ x ^ 2 / (4 * b))))) =
            ENNReal.ofReal (Real.pi ^ (d / 2) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) *
              ENNReal.ofReal (ρ x) ^ (-t) := by
    rw [← lintegral_mellin_gaussian_spatial ht (hρ x)]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro b hb
    dsimp only
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg Real.pi_pos.le hb.le) _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hb.le _), mul_assoc]
  simp_rw [he]

/-- A Gaussian Fourier identity implies the corresponding Riesz Fourier identity. This
dimension-independent step uses no cancellation of oscillatory integrals. -/
theorem riesz_fourier_identity_of_gaussian {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X) (η : Measure Y)
    [SFinite ν] [SFinite η] {ρ : X → ℝ} {σ : Y → ℝ}
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ y, 0 ≤ σ y)
    {f : X → ℝ≥0∞} (hf : Measurable f) {t d : ℝ} (ht : 0 < t) (htd : t < d)
    (hgauss : ∀ b : ℝ, 0 < b →
      ∫⁻ x, ENNReal.ofReal (Real.exp (-b * ρ x ^ 2)) * f x ∂ν =
        ENNReal.ofReal ((Real.pi / b) ^ (d / 2)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (-(σ y ^ 2 / (4 * b)))) ∂η) :
    ENNReal.ofReal (Real.Gamma ((d - t) / 2)) *
      (∫⁻ x, ENNReal.ofReal (ρ x) ^ (t - d) * f x ∂ν) =
        ENNReal.ofReal (Real.pi ^ (d / 2) * Real.Gamma (t / 2) * (4 : ℝ) ^ (t / 2)) *
          ∫⁻ y, ENNReal.ofReal (σ y) ^ (-t) ∂η := by
  have hex : -2 * ((d - t) / 2) = t - d := by ring
  rw [← hex, ← lintegral_mellin_gaussian_frequency ν hρm hρ hf (by linarith)]
  calc
    _ = ∫⁻ b : ℝ in Ioi 0, ENNReal.ofReal (b ^ ((d - t) / 2 - 1)) *
        (ENNReal.ofReal ((Real.pi / b) ^ (d / 2)) *
          ∫⁻ y, ENNReal.ofReal (Real.exp (-(σ y ^ 2 / (4 * b)))) ∂η) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro b hb
      dsimp only
      rw [hgauss b hb]
    _ = _ := lintegral_mellin_gaussian_space η hσm hσ ht

end FalconerPacking
