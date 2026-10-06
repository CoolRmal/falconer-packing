/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionKernel
public import FalconerPacking.RadialProjectionEnergy

/-!
# Weighted angular energies of orthogonal projections

The explicit planar angle formula turns the integrable angular sine singularity into a
uniform weighted bound for projected Riesz kernels. Tonelli then gives the corresponding
energy estimate for an actual source measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The inner product of unit angular directions is the cosine of their difference. -/
theorem inner_angularDirection (θ φ : ℝ) :
    ⟪angularDirection θ, angularDirection φ⟫ = Real.cos (θ - φ) := by
  unfold angularDirection
  rw [LinearIsometryEquiv.inner_map_map]
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply, RCLike.re_eq_complex_re]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
    Real.cos_sub]
  ring

/-- Every nonzero displacement has the same angular projection profile up to phase. -/
theorem abs_inner_angularDirection_eq (v : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) :
    ∃ φ : ℝ, ∀ θ : ℝ,
      |⟪v, angularDirection θ⟫| = ‖v‖ * |Real.sin (θ - φ)| := by
  let ψ := radialAngle v 0
  refine ⟨ψ + Real.pi / 2, fun θ ↦ ?_⟩
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have he : v = ‖v‖ • angularDirection ψ := by
    rw [angularDirection_radialAngle hv, sub_zero, smul_smul, mul_inv_cancel₀ hvnorm,
      one_smul]
  nth_rw 1 [he]
  rw [real_inner_smul_left, inner_angularDirection, abs_mul, abs_of_nonneg (norm_nonneg v)]
  congr 1
  rw [show θ - (ψ + Real.pi / 2) = (θ - ψ) - Real.pi / 2 by ring,
    Real.sin_sub_pi_div_two, abs_neg, show ψ - θ = -(θ - ψ) by ring, Real.cos_neg]

/-- Weighted angular transversality for a nonzero planar displacement. -/
theorem exists_weighted_angular_projection_kernel_bound {p t : ℝ}
    (hp₁ : 1 < p) (hp₂ : p < 2) (ht₀ : 0 < t) (ht : t < 2 - p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : ℝ → ℝ≥0∞, Measurable w →
      (∫⁻ θ, w θ ^ (1 / (p - 1)) ∂radialAngularMeasure) ≤ 1 →
      ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 →
        (∫⁻ θ, w θ * ENNReal.ofReal |⟪v, angularDirection θ⟫| ^ (-t)
          ∂radialAngularMeasure) ≤
            C * ENNReal.ofReal ‖v‖ ^ (-t) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_weighted_sin_riesz_bound hp₁ hp₂ ht₀ ht
  refine ⟨C, hC, fun w hw hnorm v hv ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := abs_inner_angularDirection_eq v hv
  have heq (θ : ℝ) : w θ * ENNReal.ofReal |⟪v, angularDirection θ⟫| ^ (-t) =
      (w θ * ENNReal.ofReal |Real.sin (θ - φ)| ^ (-t)) *
        ENNReal.ofReal ‖v‖ ^ (-t) := by
    rw [hφ, ENNReal.ofReal_mul (norm_nonneg v),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
    ac_rfl
  simp_rw [heq]
  rw [lintegral_mul_const _ (by fun_prop)]
  exact mul_le_mul' (hbound w hw hnorm φ) le_rfl

/-- The uniform angular kernel estimate integrates to the energy of the actual measure.
No regularity of the measure is assumed in this inequality; infinite energies are allowed. -/
theorem exists_weighted_angular_projection_energy_bound
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] {p t : ℝ}
    (hp₁ : 1 < p) (hp₂ : p < 2) (ht₀ : 0 < t) (ht : t < 2 - p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : ℝ → ℝ≥0∞, Measurable w →
      (∫⁻ θ, w θ ^ (1 / (p - 1)) ∂radialAngularMeasure) ≤ 1 →
      (∫⁻ θ, w θ * (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t) ∂ν ∂ν)
          ∂radialAngularMeasure) ≤ C * rieszEnergy ν t := by
  obtain ⟨C, hC, hbound⟩ := exists_weighted_angular_projection_kernel_bound hp₁ hp₂ ht₀ ht
  refine ⟨C + 1, by finiteness, fun w hw hnorm ↦ ?_⟩
  have hpoint (x y : EuclideanSpace ℝ (Fin 2)) :
      (∫⁻ θ, w θ * ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t)
        ∂radialAngularMeasure) ≤ (C + 1) * rieszKernel t x y := by
    by_cases hxy : x = y
    · subst y
      have hc : C + 1 ≠ 0 := by simp
      simp [rieszKernel, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr ht₀), hc]
    · apply (hbound w hw hnorm (x - y) (sub_ne_zero.mpr hxy)).trans
      simpa only [rieszKernel, dist_eq_norm] using
        (mul_le_mul' (le_add_right le_rfl : C ≤ C + 1)
          (le_rfl : ENNReal.ofReal ‖x - y‖ ^ (-t) ≤ _))
  calc
    (∫⁻ θ, w θ * (∫⁻ x, ∫⁻ y,
        ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t) ∂ν ∂ν)
          ∂radialAngularMeasure) =
        ∫⁻ θ, ∫⁻ x, ∫⁻ y,
          w θ * ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t)
            ∂ν ∂ν ∂radialAngularMeasure := by
      apply lintegral_congr
      intro θ
      rw [← lintegral_const_mul (w θ) (by fun_prop)]
      apply lintegral_congr
      intro x
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = ∫⁻ x, ∫⁻ y, ∫⁻ θ,
          w θ * ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t)
            ∂radialAngularMeasure ∂ν ∂ν := by
      rw [lintegral_lintegral_swap (by fun_prop)]
      apply lintegral_congr
      intro x
      exact lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ x, ∫⁻ y, (C + 1) * rieszKernel t x y ∂ν ∂ν :=
      lintegral_mono fun x ↦ lintegral_mono (hpoint x)
    _ = (C + 1) * rieszEnergy ν t := by
      simp_rw [lintegral_const_mul' _ _ (show C + 1 ≠ ⊤ by finiteness)]
      rfl

/-- The energy of the actual orthogonal pushforward equals the pulled-back kernel integral. -/
theorem orthogonalProjection_rieszEnergy_eq
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] (t θ : ℝ) :
    (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal |a - b| ^ (-t)
      ∂ν.map (fun y ↦ ⟪y, angularDirection θ⟫)
      ∂ν.map (fun x ↦ ⟪x, angularDirection θ⟫)) =
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal |⟪x - y, angularDirection θ⟫| ^ (-t) ∂ν ∂ν := by
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro x
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  simp only [inner_sub_left]

/-- Orponen's weighted projected-energy estimate, with actual pushforward measures. -/
theorem exists_weighted_orthogonalProjection_energy_bound
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] {p t : ℝ}
    (hp₁ : 1 < p) (hp₂ : p < 2) (ht₀ : 0 < t) (ht : t < 2 - p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : ℝ → ℝ≥0∞, Measurable w →
      (∫⁻ θ, w θ ^ (1 / (p - 1)) ∂radialAngularMeasure) ≤ 1 →
      (∫⁻ θ, w θ * (∫⁻ a : ℝ, ∫⁻ b : ℝ, ENNReal.ofReal |a - b| ^ (-t)
        ∂ν.map (fun y ↦ ⟪y, angularDirection θ⟫)
        ∂ν.map (fun x ↦ ⟪x, angularDirection θ⟫))
          ∂radialAngularMeasure) ≤ C * rieszEnergy ν t := by
  simpa only [orthogonalProjection_rieszEnergy_eq] using
    exists_weighted_angular_projection_energy_bound ν hp₁ hp₂ ht₀ ht

end FalconerPacking
