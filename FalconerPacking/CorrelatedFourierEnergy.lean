/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CorrelatedBandEnergy
public import FalconerPacking.DyadicBandIntegral

/-!
# Full Fourier energy of correlated changes of projection

The frequency band gains sum to a power of the spatial displacement. The angle maps and
translations may all depend on the same parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate

namespace FalconerPacking

theorem enorm_angular_charFun_sub_neg
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (θ φ τ : ℝ) :
    ‖charFun μ ((-τ) • angularDirection φ) -
      charFun μ ((-τ) • angularDirection θ)‖ₑ =
    ‖charFun μ (τ • angularDirection φ) - charFun μ (τ • angularDirection θ)‖ₑ := by
  simp only [neg_smul, charFun_neg, ← map_sub, RCLike.enorm_conj]

theorem shifted_charFun_neg (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (θ v τ : ℝ) :
    Complex.exp (Complex.I * ((-τ) * v)) * charFun μ ((-τ) • angularDirection θ) =
      conj (Complex.exp (Complex.I * (τ * v)) * charFun μ (τ • angularDirection θ)) := by
  rw [map_mul, ← Complex.exp_conj, neg_smul, charFun_neg]
  congr 2
  simp

/-- Integrating the angular band gain gives the full Fourier comparison estimate. -/
theorem exists_correlated_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hband⟩ := exists_correlated_charFun_band_gain μ (by linarith) hs₂ hfr
  have hs₃ : s < 3 := by linarith
  refine ⟨2 * B * dyadicBandSumConstant s,
    mul_pos (by positivity) (dyadicBandSumConstant_pos hs hs₃), ?_⟩
  intro r hr hsource α _ κ _ θ φ A hθ hφ hθdom hφdom hrange hclose
  have hc : Continuous (fun p : ℝ × ℝ ↦ charFun μ (p.1 • angularDirection p.2)) := by
    fun_prop
  have hm : Measurable (fun p : α × ℝ ↦
      ‖charFun μ (p.2 • angularDirection (φ p.1)) -
        charFun μ (p.2 • angularDirection (θ p.1))‖ₑ ^ 2) := by
    exact ((hc.measurable.comp (measurable_snd.prodMk (hφ.comp measurable_fst))).sub
      (hc.measurable.comp (measurable_snd.prodMk (hθ.comp measurable_fst)))).enorm.pow_const 2
  have heven (z : α) (τ : ℝ) := congrArg (fun x : ℝ≥0∞ ↦ x ^ 2)
    (enorm_angular_charFun_sub_neg μ (θ z) (φ z) τ)
  have h := lintegral_joint_le_of_even_of_dyadicBandTerm κ
    (f := fun z τ ↦ ‖charFun μ (τ • angularDirection (φ z)) -
      charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2) hm hs hs₃
    (show 0 < r ^ 2 by positivity) hB.le heven (fun n ↦ by
      simpa only [dyadicBandTerm, mul_assoc] using
        hband r hr.le hsource κ θ φ A hθ hφ hθdom hφdom hrange hclose
          ((2 : ℝ) ^ n) (by positivity))
  have he : (r ^ 2) ^ (s - 1) = r ^ (2 * s - 2) := by
    rw [← Real.rpow_natCast_mul hr.le]
    congr 1
    norm_num
    ring
  simpa only [he] using h

/-- A correlated translation of size r² has the same full Fourier energy bound. -/
theorem exists_correlated_charFun_translation_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (θ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hband⟩ :=
    exists_correlated_charFun_translation_band_gain μ (by linarith) hs₂ hfr
  have hs₃ : s < 3 := by linarith
  refine ⟨2 * B * dyadicBandSumConstant s,
    mul_pos (by positivity) (dyadicBandSumConstant_pos hs hs₃), ?_⟩
  intro r hr α _ κ _ θ v A hθ hv hdom hrange hshift
  have hm : Measurable (fun p : α × ℝ ↦
      ‖Complex.exp (Complex.I * (p.2 * v p.1)) *
        charFun μ (p.2 • angularDirection (θ p.1)) -
          charFun μ (p.2 • angularDirection (θ p.1))‖ₑ ^ 2) := by
    fun_prop
  have heven (z : α) (τ : ℝ) :
      ‖Complex.exp (Complex.I * ((-τ) * v z)) *
        charFun μ ((-τ) • angularDirection (θ z)) -
          charFun μ ((-τ) • angularDirection (θ z))‖ₑ ^ 2 =
      ‖Complex.exp (Complex.I * (τ * v z)) *
        charFun μ (τ • angularDirection (θ z)) -
          charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 := by
    rw [shifted_charFun_neg, neg_smul, charFun_neg, ← map_sub, RCLike.enorm_conj]
  have h := lintegral_joint_le_of_even_of_dyadicBandTerm κ
    (f := fun z τ ↦ ‖Complex.exp (Complex.I * (τ * v z)) *
      charFun μ (τ • angularDirection (θ z)) -
      charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2) hm hs hs₃
    (show 0 < r ^ 2 by positivity) hB.le (by simpa only [Complex.ofReal_neg] using heven) (fun n ↦ by
      simpa only [dyadicBandTerm, mul_assoc] using
        hband r κ θ v A hθ hv hdom hrange hshift ((2 : ℝ) ^ n) (by positivity))
  have he : (r ^ 2) ^ (s - 1) = r ^ (2 * s - 2) := by
    rw [← Real.rpow_natCast_mul hr.le]
    congr 1
    norm_num
    ring
  simpa only [he] using h

/-- The squared triangle inequality compares two functions through a common middle function. -/
theorem lintegral_enorm_sub_sq_le_middle
    {α : Type*} [MeasurableSpace α] (κ : Measure α) {f g h : α → ℂ}
    (hf : Measurable f) (_hg : Measurable g) (hh : Measurable h) :
    ∫⁻ z, ‖f z - g z‖ₑ ^ 2 ∂κ ≤
      2 * ((∫⁻ z, ‖f z - h z‖ₑ ^ 2 ∂κ) + ∫⁻ z, ‖g z - h z‖ₑ ^ 2 ∂κ) := by
  calc
    _ ≤ ∫⁻ z, 2 * (‖f z - h z‖ₑ ^ 2 + ‖g z - h z‖ₑ ^ 2) ∂κ := by
      apply lintegral_mono
      intro z
      simpa only [sub_sub_sub_cancel_right] using
        enorm_sub_sq_le_two_mul (f z - h z) (g z - h z)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        lintegral_add_left (show Measurable (fun z ↦ ‖f z - h z‖ₑ ^ 2) from
          (hf.sub hh).enorm.pow_const 2)]

/-- Simultaneously changing direction and translating obeys the same displacement power. -/
theorem exists_correlated_shifted_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ r : ℝ, 0 < r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) → (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B₀, hB₀, hangle⟩ := exists_correlated_charFun_energy_bound μ hs hs₂ hfr
  obtain ⟨B₁, hB₁, hshift⟩ := exists_correlated_charFun_translation_energy_bound μ hs hs₂ hfr
  refine ⟨2 * (B₀ + B₁), by positivity, ?_⟩
  intro r hr hsource α _ κ _ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound
  let f (p : α × ℝ) := Complex.exp (Complex.I * (p.2 * v p.1)) *
    charFun μ (p.2 • angularDirection (φ p.1))
  let g (p : α × ℝ) := charFun μ (p.2 • angularDirection (θ p.1))
  let h (p : α × ℝ) := charFun μ (p.2 • angularDirection (φ p.1))
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hh : Measurable h := by dsimp [h]; fun_prop
  have ht := lintegral_enorm_sub_sq_le_middle (κ.prod volume) hf hg hh
  rw [lintegral_prod (fun p ↦ ‖f p - g p‖ₑ ^ 2)
      (show AEMeasurable (fun p ↦ ‖f p - g p‖ₑ ^ 2) (κ.prod volume) from
        ((hf.sub hg).enorm.pow_const 2).aemeasurable),
    lintegral_prod (fun p ↦ ‖f p - h p‖ₑ ^ 2)
      (show AEMeasurable (fun p ↦ ‖f p - h p‖ₑ ^ 2) (κ.prod volume) from
        ((hf.sub hh).enorm.pow_const 2).aemeasurable),
    lintegral_prod (fun p ↦ ‖g p - h p‖ₑ ^ 2)
      (show AEMeasurable (fun p ↦ ‖g p - h p‖ₑ ^ 2) (κ.prod volume) from
        ((hg.sub hh).enorm.pow_const 2).aemeasurable)] at ht
  have hang := hangle r hr hsource κ θ φ A hθ hφ hθdom hφdom hrange hclose
  have htr := hshift r hr κ φ v A hφ hv hφdom (hrange.mono fun _ h ↦ h.2) hvbound
  have hang' : (∫⁻ z, ∫⁻ τ : ℝ, ‖g (z, τ) - h (z, τ)‖ₑ ^ 2 ∂volume ∂κ) ≤
      A * ENNReal.ofReal (B₀ * r ^ (2 * s - 2)) := by
    simpa only [g, h, enorm_sub_rev] using hang
  refine (ht.trans (mul_le_mul' le_rfl (add_le_add htr hang'))).trans_eq ?_
  rw [← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 2 * (B₀ + B₁) * r ^ (2 * s - 2) =
    2 * (B₁ * r ^ (2 * s - 2) + B₀ * r ^ (2 * s - 2)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  ring

end FalconerPacking
