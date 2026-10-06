/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CorrelatedFourierShift
public import FalconerPacking.AngularDerivativeEnergy

/-!
# Correlated angular Fourier band estimates

The actual characteristic function satisfies both the derivative and trivial comparison
bounds. Their combination is the small-scale gain used in the coherent density argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The two-marginal estimate integrates over an arbitrary frequency band. -/
theorem lintegral_correlated_angular_band_le_norm
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    {θ φ : α → ℝ} (hθ : Measurable θ) (hφ : Measurable φ) {A : ℝ≥0∞}
    (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    {F : ℝ → ℝ → ℂ} (hF : Continuous (Function.uncurry F)) (S : Set ℝ) {a b : ℝ}
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc a b ∧ φ z ∈ Icc a b) :
    ∫⁻ z, ∫⁻ τ in S, ‖F τ (φ z) - F τ (θ z)‖ₑ ^ 2 ∂volume ∂κ ≤
      (4 * A) * ∫⁻ τ in S, ∫⁻ t in Icc a b, ‖F τ t‖ₑ ^ 2 := by
  have hm : Measurable (fun p : α × ℝ ↦ ‖F p.2 (φ p.1) - F p.2 (θ p.1)‖ₑ ^ 2) := by
    exact ((hF.measurable.comp (measurable_snd.prodMk (hφ.comp measurable_fst))).sub
      (hF.measurable.comp (measurable_snd.prodMk (hθ.comp measurable_fst)))).enorm.pow_const 2
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ ≤ ∫⁻ τ in S, (4 * A) * ∫⁻ t in Icc a b, ‖F τ t‖ₑ ^ 2 := by
      apply lintegral_mono
      intro τ
      exact lintegral_correlated_angular_difference_le_norm κ hθ hφ hθdom hφdom
        (hF.comp (continuous_const.prodMk continuous_id)) hrange
    _ = _ := lintegral_const_mul _ (hF.measurable.enorm.pow_const 2).lintegral_prod_right

private theorem angular_band_order_aux {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (S : Set ℝ) :
    ∫⁻ τ in S, ∫⁻ θ in Icc (-Real.pi) Real.pi, ‖F τ θ‖ₑ ^ 2 =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in S, ENNReal.ofReal (‖F τ θ‖ ^ 2) := by
  have hf : Measurable (fun p : ℝ × ℝ ↦ ‖F p.1 p.2‖ₑ ^ 2) :=
    hF.measurable.enorm.pow_const 2
  rw [lintegral_lintegral_swap hf.aemeasurable, ← setLIntegral_congr Ioo_ae_eq_Icc]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The actual characteristic function satisfies the trivial two-marginal band estimate. -/
theorem exists_correlated_charFun_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
      (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
      κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
      (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
      ∀ R : ℝ, 0 < R →
        ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
          ‖charFun μ (τ • angularDirection (φ z)) -
            charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
          A * ENNReal.ofReal (B * R ^ (1 - s)) := by
  obtain ⟨B, hB, hbound⟩ := exists_angular_fourier_band_bound μ hs hs₂ hfr
  refine ⟨4 * B, by positivity, ?_⟩
  intro α _ κ _ θ φ A hθ hφ hθdom hφdom hrange R hR
  have hc : Continuous (fun p : ℝ × ℝ ↦ charFun μ (p.1 • angularDirection p.2)) := by fun_prop
  have h := lintegral_correlated_angular_band_le_norm κ hθ hφ hθdom hφdom
    (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc (Ioo (R / 2) (2 * R)) hrange
  rw [angular_band_order_aux (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc] at h
  refine (h.trans (mul_le_mul' le_rfl (hbound R hR))).trans_eq ?_
  rw [show (4 * B) * R ^ (1 - s) = 4 * (B * R ^ (1 - s)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  ring

/-- The actual angular derivative gives the sharper comparison at low frequencies. -/
theorem exists_correlated_charFun_derivative_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
        κ.map θ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        ∀ h : ℝ, 0 ≤ h → (∀ᵐ z ∂κ, |φ z - θ z| ≤ h) →
        ∀ R : ℝ, 0 < R →
          ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
            ‖charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * h ^ 2 * r ^ 2 * R ^ (3 - s)) := by
  obtain ⟨B, hB, hbound⟩ := exists_angular_derivative_fourier_band_bound μ hs hs₂ hfr
  refine ⟨2 * B, by positivity, ?_⟩
  intro r hr hsource α _ κ _ θ φ A hθ hφ hdom hrange h hh hclose R hR
  have hm := memLp_id_of_ae_norm_le μ hsource (1 : ℝ≥0∞)
  have hc : Continuous (fun p : ℝ × ℝ ↦ charFun μ (p.1 • angularDirection p.2)) := by fun_prop
  have hd₀ := (continuous_deriv_angular_charFun μ hm).comp
    (continuous_swap : Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ))
  have hd : Continuous (fun p : ℝ × ℝ ↦
      deriv (fun t ↦ charFun μ (p.1 • angularDirection t)) p.2) := hd₀
  have hderiv (τ θ : ℝ) : HasDerivAt (fun t ↦ charFun μ (τ • angularDirection t))
      (deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ) θ := by
    rw [(hasDerivAt_angular_charFun μ hm τ θ).deriv]
    exact hasDerivAt_angular_charFun μ hm τ θ
  have hest := lintegral_correlated_angular_band_le κ hθ hφ hdom
    (F := fun τ θ ↦ charFun μ (τ • angularDirection θ))
    (F' := fun τ θ ↦ deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ) hc hd hderiv
    (Ioo (R / 2) (2 * R)) hh hrange hclose
  rw [angular_band_order_aux
    (F := fun τ θ ↦ deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ) hd] at hest
  refine (hest.trans (mul_le_mul' le_rfl (hbound r hr hsource R hR))).trans_eq ?_
  rw [mul_assoc A, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring

/-- The derivative and trivial bounds combine into the small-scale gain, without assuming
independence between the two angle maps. -/
theorem exists_correlated_charFun_band_gain
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) → ∀ R : ℝ, 0 < R →
          ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
            ‖charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * min 1 ((r ^ 2 * R) ^ 2) * R ^ (1 - s)) := by
  obtain ⟨B₀, hB₀, hnorm⟩ := exists_correlated_charFun_band_bound μ hs hs₂ hfr
  obtain ⟨B₁, hB₁, hderiv⟩ := exists_correlated_charFun_derivative_band_bound μ hs hs₂ hfr
  refine ⟨B₀ + B₁, by positivity, ?_⟩
  intro r hr hsource α _ κ _ θ φ A hθ hφ hθdom hφdom hrange hclose R hR
  by_cases hsmall : (r ^ 2 * R) ^ 2 ≤ 1
  · rw [min_eq_right hsmall]
    refine (hderiv r hr hsource κ θ φ A hθ hφ hθdom hrange r hr hclose R hR).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    have he : B₁ * r ^ 2 * r ^ 2 * R ^ (3 - s) =
        B₁ * (r ^ 2 * R) ^ 2 * R ^ (1 - s) := by
      rw [show 3 - s = 2 + (1 - s) by ring, Real.rpow_add hR, Real.rpow_two]
      ring
    rw [he]
    gcongr
    linarith
  · rw [min_eq_left (le_of_not_ge hsmall), mul_one]
    refine (hnorm κ θ φ A hθ hφ hθdom hφdom hrange R hR).trans
      (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
    gcongr
    linarith

/-- A shift of order r² has the same small-scale band gain, even when correlated with angle. -/
theorem exists_correlated_charFun_translation_band_gain
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ,
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) → ∀ R : ℝ, 0 < R →
          ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (θ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * min 1 ((r ^ 2 * R) ^ 2) * R ^ (1 - s)) := by
  obtain ⟨B, hB, hbound⟩ := exists_angular_fourier_band_bound μ hs hs₂ hfr
  refine ⟨4 * B, by positivity, ?_⟩
  intro r α _ κ _ θ v A hθ hv hdom hrange hshift R hR
  have hc : Continuous (fun p : ℝ × ℝ ↦ charFun μ (p.1 • angularDirection p.2)) := by fun_prop
  have hband : ∀ τ ∈ Ioo (R / 2) (2 * R), |τ| ≤ 2 * R := by
    intro τ hτ
    rw [abs_of_pos (lt_trans (by positivity) hτ.1)]
    exact hτ.2.le
  have hest := lintegral_correlated_translation_band_le κ hθ hv hdom
    (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc measurableSet_Ioo
    (show 0 ≤ 2 * R by positivity) hband hrange hshift
  rw [angular_band_order_aux (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc] at hest
  refine (hest.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl (hbound R hR)))).trans_eq ?_
  have he : min (4 : ℝ≥0∞) (ENNReal.ofReal ((2 * R) ^ 2 * (r ^ 2) ^ 2)) =
      4 * ENNReal.ofReal (min 1 ((r ^ 2 * R) ^ 2)) := by
    rw [ENNReal.ofReal_min, ENNReal.ofReal_one, mul_min, mul_one,
      show (2 * R) ^ 2 * (r ^ 2) ^ 2 = 4 * ((r ^ 2 * R) ^ 2) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  rw [he, ENNReal.ofReal_mul (by positivity : 0 ≤ (4 * B) * min 1 ((r ^ 2 * R) ^ 2)),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * B),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_mul hB.le]
  ring

end FalconerPacking
