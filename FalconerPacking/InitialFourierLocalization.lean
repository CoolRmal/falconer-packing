/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AnisotropicKernelPotential
public import FalconerPacking.OrientedReproducingKernel

/-!
# Initial localization against an arbitrary pin measure

A function supported in a frequency ball has its energy against any finite measure in
a spatial ball controlled by ordinary Lebesgue energy on an enlarged ball, with a rapid
tail. Only the total pin mass enters; no conditional Frostman hypothesis is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Equal coordinate dilations in the identity frame are ordinary scalar dilations. -/
theorem orientedRectangleDilation_id_inv_apply {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin 2)) :
    orientedRectangleDilation (LinearIsometryEquiv.refl ℝ _) r⁻¹ r⁻¹
      (inv_pos.mpr hr) (inv_pos.mpr hr) x = r • x := by
  ext i
  fin_cases i <;>
    simp [orientedRectangleDilation_apply_zero, orientedRectangleDilation_apply_one,
      div_eq_mul_inv, mul_comm]

/-- The initial bandlimited estimate uses only the actual mass and spatial support of the pins. -/
theorem initial_fourier_localization (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (τ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure τ]
        (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (ξ c : EuclideanSpace ℝ (Fin 2)) (r s t : ℝ),
        0 < r → s ≤ t →
        (∀ᵐ x ∂τ, dist x c ≤ s) →
        (Function.support (fun z ↦ 𝓕 f z) ⊆ ball ξ r) →
        (∫⁻ x, ‖f x‖ₑ ^ 2 ∂τ) ≤ (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
          ((ENNReal.ofReal (r ^ 2) * 81 *
              ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
                SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * τ univ) *
            (∫⁻ x in ball c t, ‖f x‖ₑ ^ 2) +
            (ENNReal.ofReal (r ^ 2 * C / (1 + r * (t - s)) ^ m) * τ univ) *
              ∫⁻ x in (ball c t)ᶜ, ‖f x‖ₑ ^ 2) := by
  obtain ⟨C, hC, he⟩ := anisotropic_weighted_embedding m
  refine ⟨C, hC, ?_⟩
  intro τ hτ f ξ c r s t hr hst hs hf
  let A := orientedRectangleDilation (LinearIsometryEquiv.refl ℝ _) r⁻¹ r⁻¹
    (inv_pos.mpr hr) (inv_pos.mpr hr)
  have hA (x : EuclideanSpace ℝ (Fin 2)) : A x = r • x :=
    orientedRectangleDilation_id_inv_apply hr x
  have hdet : |A.toLinearEquiv.toLinearMap.det| = r ^ 2 := by
    dsimp only [A]
    rw [orientedRectangleDilation_abs_det, mul_inv_rev, inv_inv]
    ring
  have hfreq : ∀ z ∈ Function.support (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
      ∀ i, |(A.symm.toContinuousLinearMap.adjoint (z - ξ)) i| ≤ 1 := by
    intro z hz
    rw [orientedRectangleDilation_dual_mem_square_iff]
    have hnorm : ‖z - ξ‖ < r := by simpa only [mem_ball, dist_eq_norm] using hf hz
    have hi (i : Fin 2) : |(z - ξ) i| ≤ r := by
      exact (PiLp.norm_apply_le (z - ξ) i).trans hnorm.le
    change |(z - ξ) 0| ≤ r⁻¹⁻¹ ∧ |(z - ξ) 1| ≤ r⁻¹⁻¹
    simpa only [inv_inv] using And.intro (hi 0) (hi 1)
  have hmargin : ∀ y ∉ ball c t, ∀ᵐ x ∂τ, r * (t - s) ≤ ‖A (x - y)‖ := by
    intro y hy
    filter_upwards [hs] with x hx
    have ht : t ≤ dist y c := by simpa only [mem_ball, not_lt] using hy
    have hd : t - s ≤ ‖x - y‖ := by
      have := dist_triangle y x c
      rw [dist_comm y x, dist_eq_norm x y] at this
      linarith
    rw [hA, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hd hr.le
  have h := he τ A ξ f (τ univ) (ball c t) (r * (t - s)) measurableSet_ball
    (mul_nonneg hr.le (sub_nonneg.mpr hst)) hfreq
    (fun _ ↦ measure_mono (subset_univ _)) hmargin
  simpa only [hdet] using h

end FalconerPacking
