/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionAngularShift

/-!
# Uniform radial moments of actual smooth sources

The constants depend on the energy bound, the pin measure, and the support-distance bound,
and are uniform in the smooth source. This is the form needed for positive approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SchwartzMap
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- An energy-bounded family of actual Schwartz projection densities has a uniform joint moment. -/
theorem exists_uniform_projection_joint_moment_bound
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν]
    {p q a b : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 < a) (ha₁ : a < 1) (hpa : p * a < 1)
    (hb : 0 ≤ b) (hbp : b < 2 * p / (p + 1))
    {M : ℝ≥0∞} (hM : M < ∞) (hν : rieszEnergy ν (p * a) < ∞) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (Φ : ℝ → SchwartzMap ℝ ℂ),
      Measurable (fun z : ℝ × ℝ ↦ (Φ z.1 z.2).re) →
      (∀ θ x, 0 ≤ (Φ θ x).re) → (∀ θ x, (Φ θ x).im = 0) →
      (∀ θ, μ.map (fun x ↦ ⟪x, angularDirection θ⟫) =
        volume.withDensity (fun t ↦ ENNReal.ofReal (Φ θ t).re)) →
      rieszEnergy μ (2 - a) ≤ M →
      (∫⁻ z, ENNReal.ofReal (Φ z.1 ⟪z.2, angularDirection z.1⟫).re ^ b
        ∂radialAngularMeasure.prod ν) ≤ C := by
  let E := ∫⁻ θ, rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) (p * a)
    ∂radialAngularMeasure
  let H := 2 * ENNReal.ofReal (rieszFourierConstant 2 (2 - a)) *
    (ENNReal.ofReal (2 * Real.pi) ^ (-(2 - a)) * M)
  let K := (ENNReal.ofReal (rieszFourierConstant 1 a) *
    ENNReal.ofReal (2 * Real.pi) ^ (-a)) ^ (p / (p + 1)) *
      E ^ (1 / (p + 1)) * H ^ (p / (p + 1))
  have hp₀ := hpq.pos
  have hp₁ : 0 < p + 1 := by linarith
  have hbase : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
  obtain ⟨C₀, hC₀, hE₀⟩ := exists_orthogonalProjection_energy_bound ν
    (mul_pos hp₀ ha) hpa
  have hE : E < ∞ := hE₀.trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC₀) hν)
  have hH : H < ∞ := by
    apply ENNReal.mul_lt_top (by finiteness)
    apply ENNReal.mul_lt_top _ hM
    finiteness
  have hK : K < ∞ := by
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg (div_nonneg hp₀.le hp₁.le)
        finiteness
      · exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp₁.le) hE.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (div_nonneg hp₀.le hp₁.le) hH.ne
  let C := radialAngularMeasure univ + (2 : ℝ≥0∞) ^ b * K *
    (1 - (2 : ℝ≥0∞) ^ (b - 2 * p / (p + 1)))⁻¹
  have hC : C < ∞ := by
    apply ENNReal.add_lt_top.mpr
    refine ⟨measure_lt_top _ _, ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hb (by norm_num)) hK) ?_⟩
    apply lt_top_iff_ne_top.mpr
    apply ENNReal.inv_ne_top.mpr
    apply ne_of_gt (tsub_pos_iff_lt.mpr ?_)
    simpa only [ENNReal.rpow_zero] using
      ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ≥0∞) < 2)
        (by norm_num) (show b - 2 * p / (p + 1) < 0 by linarith)
  refine ⟨C, hC, ?_⟩
  intro μ _ Φ hΦ hpos him hdensity hμ
  have hmap : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      (z.1, ⟪z.2, angularDirection z.1⟫)) := by fun_prop
  have hF := hΦ.comp hmap
  simp only [Function.comp_def] at hF
  have htotal : (radialAngularMeasure.prod ν) univ = radialAngularMeasure univ := by
    rw [← univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one]
  have hsource : (∫⁻ θ, (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) *
      ‖charFun μ ((2 * Real.pi * ξ) • angularDirection θ)‖ₑ ^ 2)
        ∂radialAngularMeasure) ≤ H := by
    rw [radial_trace_source_energy_eq μ ha (by linarith)]
    exact mul_le_mul_right (mul_le_mul_right hμ _) _
  have htail (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n) ^ (2 * p / (p + 1)) *
      (radialAngularMeasure.prod ν) {z | (2 : ℝ) ^ n ≤
        (Φ z.1 ⟪z.2, angularDirection z.1⟫).re} ≤ K := by
    apply (schwartz_projection_joint_tail_bound μ ν Φ hΦ hpos him hdensity hpq ha ha₁
      (by positivity : 0 ≤ (2 : ℝ) ^ n)).trans
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hsource (div_nonneg hp₀.le hp₁.le)) _
  simpa only [htotal] using
    lintegral_rpow_le_of_dyadic_tail (radialAngularMeasure.prod ν) hF hb htail

/-- A uniform moment bound for actual radial densities of smooth compact positive sources.
Only the original source energy and a common source-to-pin distance bound enter the constant. -/
theorem exists_uniform_smooth_radial_moment_bound
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν]
    {p q a b : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 < a) (ha₁ : a < 1) (hpa : p * a < 1)
    (hb : 0 ≤ b) (hbp : b < 2 * p / (p + 1))
    {M : ℝ≥0∞} (hM : M < ∞) (hν : rieszEnergy ν (p * a) < ∞) (R : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) f → HasCompactSupport f → (∀ x, 0 ≤ f x) →
      IsFiniteMeasure (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) →
      rieszEnergy (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) (2 - a) ≤ M →
      (∀ᵐ x ∂ν, ∀ y, ENNReal.ofReal (f y) ≠ 0 → dist x y ≤ R) →
      (∫⁻ x, ∫⁻ θ, radialRayDensity (fun y ↦ ENNReal.ofReal (f y)) x θ ^ b
        ∂radialAngularMeasure ∂ν) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_projection_joint_moment_bound
    ν hpq ha ha₁ hpa hb hbp hM hν
  refine ⟨ENNReal.ofReal R ^ b * C,
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hb ENNReal.ofReal_ne_top) hC, ?_⟩
  intro f hf hc hpos hfinite henergy hR
  letI := hfinite
  obtain ⟨Φ, hΦ, hΦpos, hΦim, hline, hmeasure⟩ :=
    exists_measurable_schwartz_angularProjection hf hc hpos
  have horth := hbound (volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    Φ hΦ hΦpos hΦim hmeasure henergy
  simp only [hline] at horth
  exact (lintegral_radialRayDensity_rpow_le_joint_orthogonal
    hf.continuous.measurable.ennreal_ofReal ν hb hR).trans
      (mul_le_mul_right horth (ENNReal.ofReal R ^ b))

/-- The weak exponent supplied by a nontrivial trace exponent leaves room for a strong
moment strictly above one and a second loss in the weak-limit step. -/
theorem radial_trace_strong_exponents {p : ℝ} (hp : 1 < p) :
    ∃ b c : ℝ, 1 < c ∧ c < b ∧ b < 2 * p / (p + 1) := by
  have hP : 1 < 2 * p / (p + 1) := by
    rw [lt_div_iff₀ (by linarith : 0 < p + 1)]
    linarith
  obtain ⟨b, hb₁, hb₂⟩ := exists_between hP
  obtain ⟨c, hc₁, hc₂⟩ := exists_between hb₁
  exact ⟨b, c, hc₁, hc₂, hb₂⟩

end FalconerPacking
