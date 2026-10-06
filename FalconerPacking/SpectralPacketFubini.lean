/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleFourierConvolution
public import FalconerPacking.SpectralCircleKernel

/-!
# Selected spectral circle averages as physical kernel integrals

The angular selector is inside the frequency-circle integral. Absolute Fubini follows
from source integrability and the selector's angular first norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The actual spectral circle average with an angular multiplier. -/
def selectedSpectralCircleAverage (a : ℝ → ℂ)
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) : ℂ :=
  ∫ θ, a θ * (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) *
    𝓕 f (r • angularDirection θ) ∂radialAngularProbability

/-- Absolute integrability for exchanging the physical source and selected circle integrals. -/
theorem integrable_selectedSpectralCircle_prod
    {a : ℝ → ℂ} (ha : Integrable a radialAngularProbability)
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      a p.1 * (𝐞 (⟪y - p.2, r • angularDirection p.1⟫) : ℂ) * f p.2)
        (radialAngularProbability.prod volume) := by
  have hp := ha.mul_prod hf
  have hc : Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      (𝐞 (⟪y - p.2, r • angularDirection p.1⟫) : ℂ)) := by fun_prop
  have hm := hp.aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hi : Integrable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦
      (a p.1 * f p.2) * (𝐞 (⟪y - p.2, r • angularDirection p.1⟫) : ℂ))
        (radialAngularProbability.prod volume) := by
    apply (integrable_norm_iff hm).mp
    simpa only [Pi.mul_apply, norm_mul, Circle.norm_coe, mul_one] using hp.norm
  convert hi using 1
  funext p
  ring

/-- Exact reconstruction of the selected spectral average from its oscillatory physical kernel. -/
theorem selectedSpectralCircleAverage_eq_kernel
    {a : ℝ → ℂ} (ha : Integrable a radialAngularProbability)
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    selectedSpectralCircleAverage a f y r = ∫ x, f x *
      ∫ θ, (𝐞 (⟪y - x, r • angularDirection θ⟫) : ℂ) * a θ
        ∂radialAngularProbability := by
  rw [selectedSpectralCircleAverage]
  calc
    _ = ∫ θ, ∫ x, a θ * (𝐞 (⟪y - x, r • angularDirection θ⟫) : ℂ) * f x
        ∂volume ∂radialAngularProbability := by
      apply integral_congr_ae
      refine ae_of_all _ fun θ ↦ ?_
      dsimp only
      rw [Real.fourier_eq, ← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      dsimp only
      rw [inner_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul]
      simp only [Circle.smul_def, Circle.coe_mul, smul_eq_mul]
      ring
    _ = ∫ x, ∫ θ, a θ * (𝐞 (⟪y - x, r • angularDirection θ⟫) : ℂ) * f x
        ∂radialAngularProbability ∂volume :=
      integral_integral_swap (integrable_selectedSpectralCircle_prod ha hf y r)
    _ = _ := by
      apply integral_congr_ae
      refine ae_of_all _ fun x ↦ ?_
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine ae_of_all _ fun θ ↦ ?_
      ring

/-- A uniform kernel bound on the actual source support gives a first-norm bound. -/
theorem norm_selectedSpectralCircleAverage_le
    {a : ℝ → ℂ} (ha : Integrable a radialAngularProbability)
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) {B : ℝ}
    (hkernel : ∀ x ∈ support f,
      ‖∫ θ, (𝐞 (⟪y - x, r • angularDirection θ⟫) : ℂ) * a θ
        ∂radialAngularProbability‖ ≤ B) :
    ‖selectedSpectralCircleAverage a f y r‖ ≤ B * ∫ x, ‖f x‖ := by
  rw [selectedSpectralCircleAverage_eq_kernel ha hf]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x, B * ‖f x‖ := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
        (hf.norm.const_mul B)
      refine ae_of_all _ fun x ↦ ?_
      dsimp only
      by_cases hx : f x = 0
      · simp [hx]
      · rw [norm_mul, mul_comm B]
        exact mul_le_mul_of_nonneg_left (hkernel x hx) (norm_nonneg _)
    _ = _ := integral_const_mul B _

/-- The normalized angular Fourier kernel has the same remote decay as its unfolded integral. -/
theorem exists_remote_probability_circle_kernel_bound (N : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a : ℝ → ℂ}, ContDiff ℝ ∞ a → Periodic a (2 * Real.pi) →
      ∀ (δ γ A ε α : ℝ), 0 < δ → δ ≤ γ → γ ≤ 1 → 0 ≤ A →
      (∀ k ≤ N, ∀ θ, ‖iteratedDeriv k a θ‖ ≤ A * δ⁻¹ ^ k) →
      (∀ θ ∈ tsupport a, ‖angularDirection θ - angularDirection α‖ ≤ ε) →
      ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ ≤ L →
        γ + L * ε ≤ |⟪z, angularDirection (α + Real.pi / 2)⟫| →
        ∀ r : ℝ, 0 < r →
          ‖∫ θ, (𝐞 (⟪z, r • angularDirection θ⟫) : ℂ) * a θ
            ∂radialAngularProbability‖ ≤ C * A * (r * δ * γ)⁻¹ ^ N := by
  obtain ⟨C, hC, hc⟩ := exists_remote_spectral_circle_kernel_bound N L
  refine ⟨C, hC, ?_⟩
  intro a ha hp δ γ A ε α hδ hδγ hγ₁ hA hd hs z hz hm r hr
  have hγ : 0 < γ := hδ.trans_le hδγ
  have hphase (θ : ℝ) : (𝐞 (⟪z, r • angularDirection θ⟫) : ℂ) =
      oscillatoryPhase (circularPhase z) (2 * Real.pi * r) θ := by
    rw [Real.fourierChar_apply]
    simp only [oscillatoryPhase, circularPhase, real_inner_smul_right]
    congr 1
    push_cast
    ring
  simp_rw [hphase]
  rw [radialAngularProbability, integral_smul_measure, norm_smul, Real.norm_eq_abs,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal (show 0 ≤ 2 * Real.pi by positivity),
    abs_of_pos (show 0 < (2 * Real.pi)⁻¹ by positivity)]
  have h := hc ha hp δ γ A ε α hδ hδγ hγ₁ hA hd hs z hz hm
    (2 * Real.pi * r) (by positivity)
  rw [abs_of_pos (show 0 < 2 * Real.pi * r by positivity)] at h
  have hπ : 1 ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have hscale : (2 * Real.pi * r * δ * γ)⁻¹ ≤ (r * δ * γ)⁻¹ := by
    apply inv_le_inv₀ (by positivity) (by positivity) |>.mpr
    nlinarith [mul_pos (mul_pos hr hδ) (hδ.trans_le hδγ)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (C * A * (2 * Real.pi * r * δ * γ)⁻¹ ^ N) := by
      gcongr
    _ ≤ 1 * (C * A * (r * δ * γ)⁻¹ ^ N) := by
      apply mul_le_mul ((inv_le_one₀ (by positivity)).mpr hπ) _ (by positivity) zero_le_one
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hscale N)
        (mul_nonneg hC.le hA)
    _ = _ := one_mul _

end FalconerPacking
