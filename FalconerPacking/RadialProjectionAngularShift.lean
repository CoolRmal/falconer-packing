/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionSmoothBound

/-!
# Rotating the angular moment

Positive integration over a full period is invariant under angular translation, including
infinite integrals. This identifies the radial-to-orthogonal moment with its canonical frame.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Positive integration over a full period is independent of its initial point. -/
theorem lintegral_periodic_Ioc_eq {f : ℝ → ℝ≥0∞} {T : ℝ}
    (hT : 0 < T) (hf : Function.Periodic f T) (u v : ℝ) :
    (∫⁻ x in Ioc u (u + T), f x) = ∫⁻ x in Ioc v (v + T), f x := by
  haveI : VAddInvariantMeasure (AddSubgroup.zmultiples T) ℝ volume :=
    ⟨fun c s _ ↦ measure_preimage_add _ _ _⟩
  exact (isAddFundamentalDomain_Ioc hT u).setLIntegral_eq
    (isAddFundamentalDomain_Ioc hT v) f hf.map_vadd_zmultiples

/-- Angular shifts preserve a full-period positive integral without an integrability hypothesis. -/
theorem lintegral_periodic_comp_sub {f : ℝ → ℝ≥0∞} {T : ℝ}
    (hT : 0 < T) (hf : Function.Periodic f T) (u c : ℝ) :
    (∫⁻ x in Ioc u (u + T), f (x - c)) = ∫⁻ x in Ioc u (u + T), f x := by
  have hset : (fun x : ℝ ↦ x - c) ⁻¹' Ioc (u - c) (u + T - c) = Ioc u (u + T) := by
    ext x
    simp only [mem_preimage, mem_Ioc, sub_lt_sub_iff_right, sub_le_sub_iff_right]
  have h := lintegral_sub_right_eq_self (μ := volume)
    ((Ioc (u - c) (u + T - c)).indicator f) c
  simp_rw [← Set.indicator_comp_right (fun x : ℝ ↦ x - c)] at h
  rw [hset, lintegral_indicator measurableSet_Ioc,
    lintegral_indicator measurableSet_Ioc] at h
  change (∫⁻ x in Ioc u (u + T), f (x - c)) = _ at h
  rw [show u + T - c = (u - c) + T by ring] at h
  exact h.trans (lintegral_periodic_Ioc_eq hT hf (u - c) u)

/-- The canonical Cartesian frame is periodic in its angular coordinate. -/
theorem angularCartesianFrame_add_two_pi (θ : ℝ) :
    angularCartesianFrame (θ + 2 * Real.pi) = angularCartesianFrame θ := by
  ext z
  simp only [angularCartesianFrame_apply, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The canonical unit direction has period `2π`. -/
theorem angularDirection_add_two_pi (θ : ℝ) :
    angularDirection (θ + 2 * Real.pi) = angularDirection θ := by
  simpa only [angularCartesianFrame_one] using
    congrArg (fun e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) ↦ e 1)
      (angularCartesianFrame_add_two_pi θ)

/-- The perpendicular shift in the radial-ray formula leaves the averaged line moment unchanged. -/
theorem lintegral_shifted_orthogonalLineDensity_rpow
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (p c : ℝ) :
    (∫⁻ θ, (∫⁻ t : ℝ, orthogonalLineDensity (angularCartesianFrame (θ - c)) f t ^ p
      ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - c)⟫)) ∂radialAngularMeasure) =
    ∫⁻ θ, (∫⁻ t : ℝ, orthogonalLineDensity (angularCartesianFrame θ) f t ^ p
      ∂ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) ∂radialAngularMeasure := by
  let g (θ : ℝ) := ∫⁻ t : ℝ, orthogonalLineDensity (angularCartesianFrame θ) f t ^ p
    ∂ν.map (fun x ↦ ⟪x, angularDirection θ⟫)
  have hg : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [g, angularCartesianFrame_add_two_pi, angularDirection_add_two_pi]
  have h := lintegral_periodic_comp_sub (by positivity : 0 < 2 * Real.pi) hg (-Real.pi) c
  simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring, radialAngularMeasure] using h

/-- The radial moment is controlled by the canonical joint orthogonal moment. -/
theorem lintegral_radialRayDensity_rpow_le_joint_orthogonal
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] {R p : ℝ} (hp : 0 ≤ p)
    (hR : ∀ᵐ x ∂ν, ∀ y, f y ≠ 0 → dist x y ≤ R) :
    (∫⁻ x, ∫⁻ θ, radialRayDensity f x θ ^ p ∂radialAngularMeasure ∂ν) ≤
      ENNReal.ofReal R ^ p * ∫⁻ z,
        orthogonalLineDensity (angularCartesianFrame z.1) f
          ⟪z.2, angularDirection z.1⟫ ^ p ∂radialAngularMeasure.prod ν := by
  apply (lintegral_radialRayDensity_rpow_le_orthogonal hf ν hp hR).trans_eq
  congr 1
  rw [lintegral_shifted_orthogonalLineDensity_rpow]
  have hmap : Measurable (fun z : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      (z.1, ⟪z.2, angularDirection z.1⟫)) := by fun_prop
  have hm := (measurable_angularLineDensity hf).comp hmap
  simp only [Function.comp_def] at hm
  rw [lintegral_prod _ (hm.pow_const p).aemeasurable]
  apply lintegral_congr
  intro θ
  have ht := (measurable_angularLineDensity hf).comp
    (show Measurable (fun t : ℝ ↦ (θ, t)) from measurable_const.prodMk measurable_id)
  simp only [Function.comp_def] at ht
  exact lintegral_map (ht.pow_const p) (by fun_prop)

end FalconerPacking
