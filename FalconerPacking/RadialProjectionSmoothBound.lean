/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionSmoothTrace
public import FalconerPacking.RadialProjectionAngularMoment
public import FalconerPacking.RadialProjectionTransversality

/-!
# Averaged bounds for smooth orthogonal densities

Positive trace estimates are applied to actual projected pin measures. Angular integration
uses only ordinary Riesz energies of the two original planar measures.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set SchwartzMap FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Ordinary projected energies have a finite angular average below exponent one. -/
theorem exists_orthogonalProjection_energy_bound
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (∫⁻ θ, rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) t
        ∂radialAngularMeasure) ≤ C * rieszEnergy ν t := by
  obtain ⟨C, hC, hsin⟩ := lintegral_abs_sin_sub_neg_rpow ht ht₁
  refine ⟨C + 1, by finiteness, ?_⟩
  have hpoint (x y : EuclideanSpace ℝ (Fin 2)) :
      (∫⁻ θ, ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t)
        ∂radialAngularMeasure) ≤ (C + 1) * rieszKernel t x y := by
    by_cases hxy : x = y
    · subst y
      simp [rieszKernel, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr ht),
        show C + 1 ≠ 0 by simp]
    · obtain ⟨φ, hφ⟩ := abs_inner_angularDirection_eq (x - y) (sub_ne_zero.mpr hxy)
      simp_rw [hφ, ENNReal.ofReal_mul (norm_nonneg _),
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      rw [lintegral_const_mul _ (by fun_prop)]
      change ENNReal.ofReal ‖x - y‖ ^ (-t) *
        (∫⁻ θ in Ioc (-Real.pi) Real.pi, ENNReal.ofReal |Real.sin (θ - φ)| ^ (-t)) ≤ _
      rw [hsin φ]
      simpa only [rieszKernel, dist_eq_norm, mul_comm] using
        mul_le_mul_left (le_add_right le_rfl : C ≤ C + 1)
          (ENNReal.ofReal ‖x - y‖ ^ (-t))
  have heq (θ : ℝ) : rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) t =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t) ∂ν ∂ν := by
    simpa only [rieszEnergy1D, Real.dist_eq] using orthogonalProjection_rieszEnergy_eq ν t θ
  simp_rw [heq]
  calc
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ θ,
        ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t)
          ∂radialAngularMeasure ∂ν ∂ν := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      apply lintegral_congr
      intro x
      exact lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ x, ∫⁻ y, (C + 1) * rieszKernel t x y ∂ν ∂ν :=
      lintegral_mono fun x ↦ lintegral_mono (hpoint x)
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ (show C + 1 ≠ ∞ by finiteness)]
      rfl

/-- Projected energy depends measurably on the direction. -/
theorem measurable_orthogonalProjection_rieszEnergy
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] (t : ℝ) :
    Measurable (fun θ ↦ rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) t) := by
  have heq (θ : ℝ) : rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) t =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t) ∂ν ∂ν := by
    simpa only [rieszEnergy1D, Real.dist_eq] using orthogonalProjection_rieszEnergy_eq ν t θ
  simp_rw [heq]
  fun_prop

/-- Positive Schwartz representatives give a genuine joint weak trace bound against the
original pin probability, with no directional regularity of that probability assumed. -/
theorem schwartz_projection_joint_tail_bound
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (Φ : ℝ → SchwartzMap ℝ ℂ)
    (hΦ : Measurable (fun z : ℝ × ℝ ↦ (Φ z.1 z.2).re))
    (hpos : ∀ θ x, 0 ≤ (Φ θ x).re) (him : ∀ θ x, (Φ θ x).im = 0)
    (hdensity : ∀ θ, μ.map (fun x ↦ ⟪x, angularDirection θ⟫) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (Φ θ t).re))
    {p q a T : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 < a) (ha₁ : a < 1) (hT : 0 ≤ T) :
    ENNReal.ofReal T ^ (2 * p / (p + 1)) *
      (radialAngularMeasure.prod ν) {z |
        T ≤ (Φ z.1 ⟪z.2, angularDirection z.1⟫).re} ≤
      (ENNReal.ofReal (rieszFourierConstant 1 a) *
        ENNReal.ofReal (2 * Real.pi) ^ (-a)) ^ (p / (p + 1)) *
      (∫⁻ θ, rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) (p * a)
        ∂radialAngularMeasure) ^ (1 / (p + 1)) *
      (∫⁻ θ, (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) *
        ‖charFun μ ((2 * Real.pi * ξ) • angularDirection θ)‖ₑ ^ 2)
          ∂radialAngularMeasure) ^ (p / (p + 1)) := by
  have hF : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      (Φ z.1 ⟪z.2, angularDirection z.1⟫).re) := hΦ.comp
        (show Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) ↦
          (z.1, ⟪z.2, angularDirection z.1⟫)) from by fun_prop)
  let m (θ : ℝ) := ν {x | T ≤ (Φ θ ⟪x, angularDirection θ⟫).re}
  have hm : Measurable m := measurable_measure_prodMk_left
    (measurableSet_le measurable_const hF)
  have hm₁ (θ : ℝ) : m θ ≤ 1 := prob_le_one
  have hproj (θ : ℝ) : (ν.map (fun x ↦ ⟪x, angularDirection θ⟫))
      {x | T ≤ (Φ θ x).re} = m θ :=
    Measure.map_apply (by fun_prop) (measurableSet_le measurable_const (by fun_prop))
  rw [Measure.prod_apply (measurableSet_le measurable_const hF)]
  apply lintegral_trace_tail_interpolate radialAngularMeasure hm
    (measurable_orthogonalProjection_rieszEnergy ν (p * a))
    (by fun_prop) hpq.lt hm₁
  intro θ
  have hh := schwartz_level_weak_trace_bound
    (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) (Φ θ) hpq ha ha₁ hT
  rw [hproj] at hh
  simpa only [fourierInv_positive_schwartz_projection μ (Φ θ)
    (angularDirection θ) (hpos θ) (him θ) (hdensity θ)] using hh

/-- The source Sobolev term in the weak trace bound is exactly a planar Riesz energy. -/
theorem radial_trace_source_energy_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {a : ℝ} (ha : 0 < a) (ha₂ : a < 2) :
    (∫⁻ θ, (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) *
      ‖charFun μ ((2 * Real.pi * ξ) • angularDirection θ)‖ₑ ^ 2)
        ∂radialAngularMeasure) =
      2 * ENNReal.ofReal (rieszFourierConstant 2 (2 - a)) *
        (ENNReal.ofReal (2 * Real.pi) ^ (-(2 - a)) * rieszEnergy μ (2 - a)) := by
  change (∫⁻ θ in Ioc (-Real.pi) Real.pi, ∫⁻ ξ : ℝ,
    ENNReal.ofReal |ξ| ^ (1 - a) *
      ‖charFun μ ((2 * Real.pi * ξ) • angularDirection θ)‖ₑ ^ 2) = _
  rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
  simpa only [show (2 - a) - 1 = 1 - a by ring,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)] using
      lintegral_angular_charFun_scaled_rpow μ (by linarith : 0 < 2 - a)
        (by linarith : 2 - a < 2) (2 * Real.pi)

/-- Joint integrability with an exponent above one follows from the two actual finite energies. -/
theorem schwartz_projection_joint_moment_lt_top
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (Φ : ℝ → SchwartzMap ℝ ℂ)
    (hΦ : Measurable (fun z : ℝ × ℝ ↦ (Φ z.1 z.2).re))
    (hpos : ∀ θ x, 0 ≤ (Φ θ x).re) (him : ∀ θ x, (Φ θ x).im = 0)
    (hdensity : ∀ θ, μ.map (fun x ↦ ⟪x, angularDirection θ⟫) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (Φ θ t).re))
    {p q a b : ℝ} (hpq : p.HolderConjugate q)
    (ha : 0 < a) (ha₁ : a < 1) (hpa : p * a < 1)
    (hb : 0 ≤ b) (hbp : b < 2 * p / (p + 1))
    (hμ : rieszEnergy μ (2 - a) < ∞) (hν : rieszEnergy ν (p * a) < ∞) :
    (∫⁻ z, ENNReal.ofReal (Φ z.1 ⟪z.2, angularDirection z.1⟫).re ^ b
      ∂radialAngularMeasure.prod ν) < ∞ := by
  have hF : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      (Φ z.1 ⟪z.2, angularDirection z.1⟫).re) := hΦ.comp
        (show Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) ↦
          (z.1, ⟪z.2, angularDirection z.1⟫)) from by fun_prop)
  obtain ⟨C, hC, hE⟩ := exists_orthogonalProjection_energy_bound ν
    (mul_pos hpq.pos ha) hpa
  have hEfin := hE.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hν)
  have hHfin : (∫⁻ θ, (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) *
      ‖charFun μ ((2 * Real.pi * ξ) • angularDirection θ)‖ₑ ^ 2)
        ∂radialAngularMeasure) < ∞ := by
    rw [radial_trace_source_energy_eq μ ha (by linarith)]
    apply ENNReal.mul_lt_top (by finiteness)
    apply ENNReal.mul_lt_top _ hμ
    have hbase : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
    finiteness
  apply lintegral_rpow_lt_top_of_dyadic_tail (radialAngularMeasure.prod ν) hF hb hbp
    (K := (ENNReal.ofReal (rieszFourierConstant 1 a) *
        ENNReal.ofReal (2 * Real.pi) ^ (-a)) ^ (p / (p + 1)) *
      (∫⁻ θ, rieszEnergy1D (ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) (p * a)
        ∂radialAngularMeasure) ^ (1 / (p + 1)) *
      (∫⁻ θ, (∫⁻ ξ : ℝ, ENNReal.ofReal |ξ| ^ (1 - a) *
        ‖charFun μ ((2 * Real.pi * ξ) • angularDirection θ)‖ₑ ^ 2)
          ∂radialAngularMeasure) ^ (p / (p + 1)))
  · have hp₀ := hpq.pos
    have hp₁ : 0 < p + 1 := by linarith
    have hbase : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by positivity
    apply ENNReal.mul_lt_top
    · apply ENNReal.mul_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg (div_nonneg hp₀.le hp₁.le)
        finiteness
      · exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp₁.le) hEfin.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (div_nonneg hp₀.le hp₁.le) hHfin.ne
  · intro n
    exact schwartz_projection_joint_tail_bound μ ν Φ hΦ hpos him hdensity hpq ha ha₁
      (by positivity)

/-- Smooth compact positive sources provide all the jointly measurable Schwartz data required
by the preceding trace estimates. -/
theorem exists_measurable_schwartz_angularProjection
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hc : HasCompactSupport f) (hpos : ∀ x, 0 ≤ f x) :
    ∃ Φ : ℝ → SchwartzMap ℝ ℂ,
      Measurable (fun z : ℝ × ℝ ↦ (Φ z.1 z.2).re) ∧
      (∀ θ t, 0 ≤ (Φ θ t).re) ∧ (∀ θ t, (Φ θ t).im = 0) ∧
      (∀ θ t, ENNReal.ofReal (Φ θ t).re =
        orthogonalLineDensity (angularCartesianFrame θ) (fun x ↦ ENNReal.ofReal (f x)) t) ∧
      (∀ θ, (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).map
        (fun x ↦ ⟪x, angularDirection θ⟫) =
          volume.withDensity (fun t ↦ ENNReal.ofReal (Φ θ t).re)) := by
  choose Φ hvalue hpositive hline hmeasure using
    fun θ ↦ exists_positive_schwartz_orthogonalLineDensity (angularCartesianFrame θ) hf hc hpos
  have hre (θ t : ℝ) : (Φ θ t).re =
      (orthogonalLineDensity (angularCartesianFrame θ) (fun x ↦ ENNReal.ofReal (f x)) t).toReal := by
    rw [← hline, ENNReal.toReal_ofReal (hpositive θ t).1]
  refine ⟨Φ, ?_, fun θ t ↦ (hpositive θ t).1,
    fun θ t ↦ (hpositive θ t).2, hline, ?_⟩
  · simp_rw [hre]
    exact (measurable_angularLineDensity hf.continuous.measurable.ennreal_ofReal).ennreal_toReal
  · intro θ
    simpa only [angularCartesianFrame_one] using hmeasure θ

end FalconerPacking
