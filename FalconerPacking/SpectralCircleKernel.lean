/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.FullCirclePacketDecay
import FalconerPacking.CircleCapScaledGeometry
import FalconerPacking.SourcePacketMicrolocal

/-!
# Nonstationary angular kernels for remote spectral circle extensions

The amplitude here is an angular selector. A spectral extension is subsequently written
as its oscillatory kernel integrated against the physical source packet. This is distinct
from integration of a packet over a physical distance circle.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- Chordal localization alone transfers the central transverse margin to the actual phase
derivative; there is no angular branch-cut assumption. -/
theorem le_abs_deriv_circularPhase_of_chord
    (z : EuclideanSpace ℝ (Fin 2)) {α θ ε γ L : ℝ}
    (hz : ‖z‖ ≤ L) (hnear : ‖angularDirection θ - angularDirection α‖ ≤ ε)
    (hmargin : γ + L * ε ≤ |⟪z, angularDirection (α + Real.pi / 2)⟫|) :
    γ ≤ |deriv (circularPhase z) θ| := by
  have he : ‖angularDirection (α + Real.pi / 2) - angularDirection (θ + Real.pi / 2)‖ =
      ‖angularDirection θ - angularDirection α‖ := by
    rw [norm_sub_rev (angularDirection θ), norm_angularDirection_sub,
      norm_angularDirection_sub]
    congr 3
    ring
  have hε : 0 ≤ ε := (norm_nonneg _).trans hnear
  have hi := abs_real_inner_le_norm z
    (angularDirection (α + Real.pi / 2) - angularDirection (θ + Real.pi / 2))
  rw [he, inner_sub_right] at hi
  have hb := abs_add_le ⟪z, angularDirection (θ + Real.pi / 2)⟫
    (⟪z, angularDirection (α + Real.pi / 2)⟫ - ⟪z, angularDirection (θ + Real.pi / 2)⟫)
  rw [add_sub_cancel] at hb
  have hm := mul_le_mul hz hnear (norm_nonneg _) (by linarith [norm_nonneg z] : 0 ≤ L)
  rw [deriv_circularPhase, circularPhase]
  linarith

/-- Multiplication by the fixed unfolding cutoff preserves the angular derivative scale. -/
theorem exists_unfolded_selector_derivative_bound (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℝ → ℂ}, ContDiff ℝ ∞ a →
      ∀ (δ A : ℝ), 0 < δ → δ ≤ 1 → 0 ≤ A →
      (∀ k ≤ N, ∀ θ, ‖iteratedDeriv k a θ‖ ≤ A * δ⁻¹ ^ k) →
      ∀ k ≤ N, ∀ θ,
        ‖iteratedDeriv k (fun t ↦ (smoothPeriodCutoff (2 * Real.pi) t : ℂ) * a t) θ‖ ≤
          C * A * δ⁻¹ ^ k := by
  obtain ⟨B, hB, hb⟩ := exists_smoothPeriodCutoff_derivative_bound
    (show 0 < 2 * Real.pi by positivity) N
  refine ⟨2 ^ N * B, by positivity, ?_⟩
  intro a ha δ A hδ hδ₁ hA hder k hk θ
  have hbase : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ₁
  have hcut : ∀ i ≤ k, ‖iteratedDeriv i
      (fun t ↦ (smoothPeriodCutoff (2 * Real.pi) t : ℂ)) θ‖ ≤ B * δ⁻¹ ^ i := by
    intro i hi
    rw [iteratedDeriv_ofReal (contDiff_smoothPeriodCutoff _) i, Complex.norm_real]
    exact (hb i (hi.trans hk) θ).trans
      (le_mul_of_one_le_right hB.le (one_le_pow₀ hbase))
  have hmul := norm_iteratedDeriv_mul_le
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothPeriodCutoff _)) ha hB.le
    (inv_nonneg.mpr hδ.le) k θ hcut (fun i hi ↦ hder i (hi.trans hk) θ)
  exact hmul.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hB.le) hA)
    (by positivity))

/-- Full-circle remote decay for a genuinely periodic smooth angular selector. -/
theorem exists_remote_spectral_circle_kernel_bound (N : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℝ → ℂ}, ContDiff ℝ ∞ a → Periodic a (2 * Real.pi) →
      ∀ (δ γ A ε α : ℝ), 0 < δ → δ ≤ γ → γ ≤ 1 → 0 ≤ A →
      (∀ k ≤ N, ∀ θ, ‖iteratedDeriv k a θ‖ ≤ A * δ⁻¹ ^ k) →
      (∀ θ ∈ tsupport a, ‖angularDirection θ - angularDirection α‖ ≤ ε) →
      ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ ≤ L →
        γ + L * ε ≤ |⟪z, angularDirection (α + Real.pi / 2)⟫| →
        ∀ t : ℝ, t ≠ 0 →
          ‖∫ θ, oscillatoryPhase (circularPhase z) t θ * a θ ∂radialAngularMeasure‖ ≤
            C * A * (|t| * δ * γ)⁻¹ ^ N := by
  obtain ⟨B, hB, hb⟩ := exists_unfolded_selector_derivative_bound N
  let Q := circularReciprocalDerivativeBound N L
  have hQ : 0 < Q := circularReciprocalDerivativeBound_pos N L
  refine ⟨(4 * Real.pi) * (2 ^ N * Q) ^ N * B, by positivity, ?_⟩
  intro a ha haper δ γ A ε α hδ hδγ hγ₁ hA hder hs z hz hmargin t ht
  let b (θ : ℝ) := (smoothPeriodCutoff (2 * Real.pi) θ : ℂ) * a θ
  have hbc : ContDiff ℝ ∞ b :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothPeriodCutoff _)).mul ha
  have hbs : HasCompactSupport b :=
    ((hasCompactSupport_smoothPeriodCutoff (show 0 < 2 * Real.pi by positivity)).comp_left
      Complex.ofReal_zero).mul_right
  have hbint : tsupport b ⊆ Icc (-(2 * Real.pi)) (2 * Real.pi) := by
    apply tsupport_mul_subset_left.trans
    apply (tsupport_comp_subset Complex.ofReal_zero _).trans
    exact tsupport_smoothPeriodCutoff_subset (by positivity)
  have hba : tsupport b ⊆ tsupport a := tsupport_mul_subset_right
  have hqφ : ∀ θ ∈ tsupport b, circularReciprocal γ z θ * deriv (circularPhase z) θ = 1 := by
    intro θ hθ
    exact circularReciprocal_mul_deriv_eq_one z (hδ.trans_le hδγ)
      (le_abs_deriv_circularPhase_of_chord z hz (hs θ (hba hθ)) hmargin)
  have hc : Continuous (fun θ ↦ oscillatoryPhase (circularPhase z) t θ * a θ) :=
    (contDiff_oscillatoryPhase (contDiff_circularPhase z) t).continuous.mul ha.continuous
  have hp : Periodic (fun θ ↦ oscillatoryPhase (circularPhase z) t θ * a θ)
      (2 * Real.pi) := by
    intro θ
    dsimp only
    rw [haper θ]
    simp only [oscillatoryPhase, circularPhase, angularDirection,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [integral_radialAngularMeasure_eq_smoothPeriodCutoff hc hp]
  have he : (fun θ ↦ smoothPeriodCutoff (2 * Real.pi) θ •
      (oscillatoryPhase (circularPhase z) t θ * a θ)) =
      fun θ ↦ oscillatoryPhase (circularPhase z) t θ * b θ := by
    funext θ
    simp only [b, Complex.real_smul]
    ring
  rw [he]
  have h := norm_integral_oscillatoryPhase_mul_scale_le
    (contDiff_circularPhase z) (contDiff_circularReciprocal γ z) hbc hbs hqφ hQ.le
    (mul_nonneg hB.le hA) hδ (hδ.trans_le hδγ) hbint N
    (fun k hk θ ↦ norm_iteratedDeriv_circularReciprocal_scale_le z hδ hδγ hγ₁ hz hk θ)
    (hb ha δ A hδ (hδγ.trans hγ₁) hA hder) ht
  simp only [sub_neg_eq_add, show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring,
    max_eq_left (show 0 ≤ 4 * Real.pi by positivity)] at h
  exact h.trans_eq (by ring)

end FalconerPacking
