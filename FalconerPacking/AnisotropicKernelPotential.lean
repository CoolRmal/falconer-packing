/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AnisotropicSchwartzKernel
import FalconerPacking.GridMassGrowth

/-!
# Kernel potentials from anisotropic cell masses

Transporting a measure to unit-grid coordinates makes the potential estimate uniform
over all aspect ratios and rotations. A support margin gives an independent tail bound.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Mass bounds on actual inverse-image grid rectangles give a uniform kernel potential. -/
theorem shiftedAnisotropicReproducingKernel_potential_le
    (τ : Measure (EuclideanSpace ℝ (Fin 2)))
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (ξ₀ : EuclideanSpace ℝ (Fin 2)) (M : ℝ≥0∞)
    (hM : ∀ q, τ (A ⁻¹' dyadicCube 0 q) ≤ M)
    (y : EuclideanSpace ℝ (Fin 2)) :
    ∫⁻ x, ‖shiftedAnisotropicReproducingKernel A ξ₀ (x - y)‖ₑ ∂τ ≤
      ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det| * 81 *
        ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
          SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * M := by
  have hmap (q) : τ.map A (dyadicCube 0 q) ≤ M := by
    rw [Measure.map_apply A.continuous.measurable (measurableSet_dyadicCube 0 q)]
    exact hM q
  have h := schwartz_potential_sub_right_le_of_unit_cube_mass (τ.map A)
    unitReproducingKernel M hmap (A y)
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin 2) ↦
      ‖unitReproducingKernel (z - A y)‖ₑ) :=
    (unitReproducingKernel.continuous.measurable.comp
      (measurable_id.sub (measurable_const (a := A y)))).enorm
  rw [lintegral_map hm A.continuous.measurable] at h
  have hnorm (x : EuclideanSpace ℝ (Fin 2)) :
      ‖shiftedAnisotropicReproducingKernel A ξ₀ (x - y)‖ₑ =
        ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det| *
          ‖unitReproducingKernel (A x - A y)‖ₑ := by
    rw [← ofReal_norm, norm_shiftedAnisotropicReproducingKernel,
      anisotropicReproducingKernel_apply, norm_smul, Real.norm_eq_abs, abs_abs,
      ENNReal.ofReal_mul (abs_nonneg _), ofReal_norm, map_sub]
  simp_rw [hnorm]
  rw [lintegral_const_mul (μ := τ)
    (f := fun x ↦ ‖unitReproducingKernel (A x - A y)‖ₑ)
    _ (hm.comp A.continuous.measurable)]
  exact (mul_le_mul_right h _).trans_eq (by ring)

/-- Rapid decay and an actual support margin give a uniform tail potential. -/
theorem shiftedAnisotropicReproducingKernel_tail (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (τ : Measure (EuclideanSpace ℝ (Fin 2)))
        (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
        (ξ₀ y : EuclideanSpace ℝ (Fin 2)) (R : ℝ), 0 ≤ R →
        (∀ᵐ x ∂τ, R ≤ ‖A (x - y)‖) →
        ∫⁻ x, ‖shiftedAnisotropicReproducingKernel A ξ₀ (x - y)‖ₑ ∂τ ≤
          ENNReal.ofReal (|A.toLinearEquiv.toLinearMap.det| * C / (1 + R) ^ m) *
            τ univ := by
  obtain ⟨C, hC, hdecay⟩ := shiftedAnisotropicReproducingKernel_decay m
  refine ⟨C, hC, ?_⟩
  intro τ A ξ₀ y R hR hdist
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal
        (|A.toLinearEquiv.toLinearMap.det| * C / (1 + R) ^ m) ∂τ := by
      apply lintegral_mono_ae
      filter_upwards [hdist] with x hx
      rw [← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      exact (hdecay A ξ₀ (x - y)).trans (div_le_div_of_nonneg_left
        (by positivity) (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) m))
    _ = _ := lintegral_const _

/-- The actual Fourier support, rectangle masses, and support margin imply weighted embedding. -/
theorem anisotropic_weighted_embedding (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (τ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite τ]
        (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
        (ξ₀ : EuclideanSpace ℝ (Fin 2))
        (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (M : ℝ≥0∞) (P : Set (EuclideanSpace ℝ (Fin 2))) (R : ℝ),
        MeasurableSet P → 0 ≤ R →
        (∀ ξ ∈ Function.support (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          ∀ i, |(A.symm.toContinuousLinearMap.adjoint (ξ - ξ₀)) i| ≤ 1) →
        (∀ q, τ (A ⁻¹' dyadicCube 0 q) ≤ M) →
        (∀ y ∉ P, ∀ᵐ x ∂τ, R ≤ ‖A (x - y)‖) →
        (∫⁻ x, ‖f x‖ₑ ^ 2 ∂τ) ≤ (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
          ((ENNReal.ofReal |A.toLinearEquiv.toLinearMap.det| * 81 *
              ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
                SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * M) *
            (∫⁻ x in P, ‖f x‖ₑ ^ 2) +
          (ENNReal.ofReal (|A.toLinearEquiv.toLinearMap.det| * C / (1 + R) ^ m) *
            τ univ) * ∫⁻ x in Pᶜ, ‖f x‖ₑ ^ 2) := by
  obtain ⟨C, hC, htail⟩ := shiftedAnisotropicReproducingKernel_tail m
  refine ⟨C, hC, ?_⟩
  intro τ hτ A ξ₀ f M P R hP hR hf hM hmargin
  have h := schwartz_weighted_embedding_of_reproducing f
    (shiftedAnisotropicReproducingKernel A ξ₀) τ
    (shiftedAnisotropicReproducingKernel_reproduces A ξ₀ f hf) hP
    (fun y _ ↦ shiftedAnisotropicReproducingKernel_potential_le τ A ξ₀ M hM y)
    (fun y hy ↦ htail τ A ξ₀ y R hR (hmargin y hy))
  rwa [shiftedAnisotropicReproducingKernel_lintegral_enorm] at h

end FalconerPacking
