/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.UniformFourierBands
import FalconerPacking.ProjectionDensityComparison

/-!
# Uniform correlated projection comparison

Every scalar coefficient is bounded explicitly in terms of the exponent and `max C 1`.
Consequently the final constant works simultaneously for all Frostman source probabilities,
which is essential when summing over conditional measures.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate

namespace FalconerPacking

private theorem uniform_angular_band_order {F : ℝ → ℝ → ℂ}
    (hF : Continuous (Function.uncurry F)) (S : Set ℝ) :
    ∫⁻ τ in S, ∫⁻ θ in Icc (-Real.pi) Real.pi, ‖F τ θ‖ₑ ^ 2 =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ τ in S, ENNReal.ofReal (‖F τ θ‖ ^ 2) := by
  have hf : Measurable (fun p : ℝ × ℝ ↦ ‖F p.1 p.2‖ₑ ^ 2) :=
    hF.measurable.enorm.pow_const 2
  rw [lintegral_lintegral_swap hf.aemeasurable, ← setLIntegral_congr Ioo_ae_eq_Icc]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]


/-- A correlated band coefficient with an explicit uniform upper bound. -/
theorem exists_uniform_correlated_charFun_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 4 * (uniformFourierBandCoefficient s * max C 1) ∧
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
      (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
      κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
      (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
      ∀ R : ℝ, 0 < R →
        ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
          ‖charFun μ (τ • angularDirection (φ z)) -
            charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
          A * ENNReal.ofReal (B * R ^ (1 - s)) := by
  let B := uniformFourierBandCoefficient s * max C 1
  have hB : 0 < B := by dsimp [B]; positivity [uniformFourierBandCoefficient_pos s]
  have hbound := uniform_angular_fourier_band_bound μ hs hs₂ hfr
  refine ⟨4 * B, by positivity, le_rfl, ?_⟩
  intro α _ κ _ θ φ A hθ hφ hθdom hφdom hrange R hR
  have hc : Continuous (fun p : ℝ × ℝ ↦ charFun μ (p.1 • angularDirection p.2)) := by fun_prop
  have h := lintegral_correlated_angular_band_le_norm κ hθ hφ hθdom hφdom
    (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc (Ioo (R / 2) (2 * R)) hrange
  rw [uniform_angular_band_order (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc] at h
  refine (h.trans (mul_le_mul' le_rfl (hbound R hR))).trans_eq ?_
  rw [show (4 * B) * R ^ (1 - s) = 4 * (B * R ^ (1 - s)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  ring


/-- A correlated band coefficient with an explicit uniform upper bound. -/
theorem exists_uniform_correlated_charFun_derivative_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 32 * (uniformFourierBandCoefficient s * max C 1) ∧
      ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
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
  let B := 16 * (uniformFourierBandCoefficient s * max C 1)
  have hB : 0 < B := by dsimp [B]; positivity [uniformFourierBandCoefficient_pos s]
  have hbound := uniform_angular_derivative_fourier_band_bound μ hs hs₂ hfr
  refine ⟨2 * B, by positivity, by dsimp [B]; nlinarith, ?_⟩
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
  rw [uniform_angular_band_order
    (F := fun τ θ ↦ deriv (fun t ↦ charFun μ (τ • angularDirection t)) θ) hd] at hest
  refine (hest.trans (mul_le_mul' le_rfl (hbound r hr hsource R hR))).trans_eq ?_
  rw [mul_assoc A, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  ring


/-- A correlated band coefficient with an explicit uniform upper bound. -/
theorem exists_uniform_correlated_charFun_band_gain
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 36 * (uniformFourierBandCoefficient s * max C 1) ∧
      ∀ r : ℝ, 0 ≤ r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) → ∀ R : ℝ, 0 < R →
          ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
            ‖charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * min 1 ((r ^ 2 * R) ^ 2) * R ^ (1 - s)) := by
  obtain ⟨B₀, hB₀, hB₀bound, hnorm⟩ := exists_uniform_correlated_charFun_band_bound μ hs hs₂ hfr
  obtain ⟨B₁, hB₁, hB₁bound, hderiv⟩ :=
    exists_uniform_correlated_charFun_derivative_band_bound μ hs hs₂ hfr
  refine ⟨B₀ + B₁, by positivity, by linarith, ?_⟩
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


/-- A correlated band coefficient with an explicit uniform upper bound. -/
theorem exists_uniform_correlated_charFun_translation_band_gain
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 4 * (uniformFourierBandCoefficient s * max C 1) ∧
      ∀ r : ℝ,
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) → ∀ R : ℝ, 0 < R →
          ∫⁻ z, ∫⁻ τ in Ioo (R / 2) (2 * R),
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (θ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * min 1 ((r ^ 2 * R) ^ 2) * R ^ (1 - s)) := by
  let B := uniformFourierBandCoefficient s * max C 1
  have hB : 0 < B := by dsimp [B]; positivity [uniformFourierBandCoefficient_pos s]
  have hbound := uniform_angular_fourier_band_bound μ hs hs₂ hfr
  refine ⟨4 * B, by positivity, le_rfl, ?_⟩
  intro r α _ κ _ θ v A hθ hv hdom hrange hshift R hR
  have hc : Continuous (fun p : ℝ × ℝ ↦ charFun μ (p.1 • angularDirection p.2)) := by fun_prop
  have hband : ∀ τ ∈ Ioo (R / 2) (2 * R), |τ| ≤ 2 * R := by
    intro τ hτ
    rw [abs_of_pos (lt_trans (by positivity) hτ.1)]
    exact hτ.2.le
  have hest := lintegral_correlated_translation_band_le κ hθ hv hdom
    (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc measurableSet_Ioo
    (show 0 ≤ 2 * R by positivity) hband hrange hshift
  rw [uniform_angular_band_order (F := fun τ θ ↦ charFun μ (τ • angularDirection θ)) hc] at hest
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


/-- Dyadic summation preserves the explicit source-uniform coefficient. -/
theorem exists_uniform_correlated_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧
      B ≤ 72 * (uniformFourierBandCoefficient s * max C 1) * dyadicBandSumConstant s ∧
      ∀ r : ℝ, 0 < r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hBbound, hband⟩ :=
    exists_uniform_correlated_charFun_band_gain μ (by linarith) hs₂ hfr
  have hs₃ : s < 3 := by linarith
  refine ⟨2 * B * dyadicBandSumConstant s,
    mul_pos (by positivity) (dyadicBandSumConstant_pos hs hs₃), by
      nlinarith [mul_le_mul_of_nonneg_right hBbound
        (dyadicBandSumConstant_pos hs hs₃).le], ?_⟩
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


/-- Dyadic summation preserves the explicit source-uniform coefficient. -/
theorem exists_uniform_correlated_charFun_translation_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ B ≤ 8 * (uniformFourierBandCoefficient s * max C 1) * dyadicBandSumConstant s ∧
      ∀ r : ℝ, 0 < r →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (θ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hBbound, hband⟩ :=
    exists_uniform_correlated_charFun_translation_band_gain μ (by linarith) hs₂ hfr
  have hs₃ : s < 3 := by linarith
  refine ⟨2 * B * dyadicBandSumConstant s,
    mul_pos (by positivity) (dyadicBandSumConstant_pos hs hs₃), by
      nlinarith [mul_le_mul_of_nonneg_right hBbound
        (dyadicBandSumConstant_pos hs hs₃).le], ?_⟩
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
    (show 0 < r ^ 2 by positivity) hB.le (by simpa only [Complex.ofReal_neg] using heven)
    (fun n ↦ by
      simpa only [dyadicBandTerm, mul_assoc] using
        hband r κ θ v A hθ hv hdom hrange hshift ((2 : ℝ) ^ n) (by positivity))
  have he : (r ^ 2) ^ (s - 1) = r ^ (2 * s - 2) := by
    rw [← Real.rpow_natCast_mul hr.le]
    congr 1
    norm_num
    ring
  simpa only [he] using h


/-- Direction and translation comparison with a uniform quantified coefficient. -/
theorem exists_uniform_correlated_shifted_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧
      B ≤ 160 * (uniformFourierBandCoefficient s * max C 1) * dyadicBandSumConstant s ∧
      ∀ r : ℝ, 0 < r → (∀ᵐ x ∂μ, ‖x‖ ≤ r) →
      ∀ {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
        (θ φ v : α → ℝ) (A : ℝ≥0∞), Measurable θ → Measurable φ → Measurable v →
        κ.map θ ≤ A • (volume : Measure ℝ) → κ.map φ ≤ A • (volume : Measure ℝ) →
        (∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi) →
        (∀ᵐ z ∂κ, |φ z - θ z| ≤ r) → (∀ᵐ z ∂κ, |v z| ≤ r ^ 2) →
          ∫⁻ z, ∫⁻ τ : ℝ,
            ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
              charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ ≤
            A * ENNReal.ofReal (B * r ^ (2 * s - 2)) := by
  obtain ⟨B₀, hB₀, hB₀bound, hangle⟩ := exists_uniform_correlated_charFun_energy_bound μ hs hs₂ hfr
  obtain ⟨B₁, hB₁, hB₁bound, hshift⟩ :=
    exists_uniform_correlated_charFun_translation_energy_bound μ hs hs₂ hfr
  refine ⟨2 * (B₀ + B₁), by positivity, by nlinarith, ?_⟩
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

/-- The Fourier comparison itself with a coefficient depending only on the exponent. -/
theorem uniform_correlated_shifted_charFun_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 < r) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hv : Measurable v) (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ, |φ z - θ z| ≤ r) (hvbound : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    (∫⁻ z, ∫⁻ τ : ℝ,
      ‖Complex.exp (Complex.I * (τ * v z)) * charFun μ (τ • angularDirection (φ z)) -
        charFun μ (τ • angularDirection (θ z))‖ₑ ^ 2 ∂volume ∂κ) ≤
          A * ENNReal.ofReal ((160 * uniformFourierBandCoefficient s *
            dyadicBandSumConstant s) * max C 1 * r ^ (2 * s - 2)) := by
  obtain ⟨B, _, hBbound, hbound⟩ :=
    exists_uniform_correlated_shifted_charFun_energy_bound μ hs hs₂ hfr
  refine (hbound r hr hsource κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound).trans
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
  nlinarith [hBbound]

/-- A coefficient depending only on the Frostman exponent, in the density normalization. -/
def uniformProjectionCoefficient (s : ℝ) : ℝ :=
  160 * uniformFourierBandCoefficient s * dyadicBandSumConstant s / (2 * Real.pi)

theorem uniformProjectionCoefficient_pos {s : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2) :
    0 < uniformProjectionCoefficient s := by
  unfold uniformProjectionCoefficient
  positivity [uniformFourierBandCoefficient_pos s,
    dyadicBandSumConstant_pos hs (show s < 3 by linarith)]

/-- The actual correlated density estimate with a source-independent explicit coefficient. -/
theorem uniform_correlated_projectionDensity_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 < r) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hv : Measurable v) (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ, |φ z - θ z| ≤ r) (hvbound : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    (∫⁻ z, ∫⁻ t : ℝ, ENNReal.ofReal ((orthogonalProjectionDensity μ (φ z) (t - v z) -
      orthogonalProjectionDensity μ (θ z) t) ^ 2) ∂volume ∂κ) ≤
        A * ENNReal.ofReal (uniformProjectionCoefficient s * max C 1 * r ^ (2 * s - 2)) := by
  obtain ⟨B, hB, hBbound, hbound⟩ :=
    exists_uniform_correlated_shifted_charFun_energy_bound μ hs hs₂ hfr
  rw [lintegral_correlated_projectionDensity_sub_sq μ hs hs₂ hfr κ θ φ v A hθ hφ
    hθdom hφdom hrange]
  have h := (hbound r hr hsource κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound).trans
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hBbound (Real.rpow_nonneg hr.le _))))
  refine (mul_le_mul' le_rfl h).trans_eq ?_
  have hconst :
      ENNReal.ofReal (uniformProjectionCoefficient s * max C 1 * r ^ (2 * s - 2)) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * ENNReal.ofReal
        ((160 * (uniformFourierBandCoefficient s * max C 1) * dyadicBandSumConstant s) *
          r ^ (2 * s - 2)) := by
    calc
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          ((160 * (uniformFourierBandCoefficient s * max C 1) * dyadicBandSumConstant s) *
            r ^ (2 * s - 2))) := by
        congr 1
        unfold uniformProjectionCoefficient
        ring
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
          ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [hconst]
  ac_rfl

/-- If the Frostman constant is at least one, the dependence is exactly linear in it. -/
theorem uniform_correlated_projectionDensity_energy_bound_of_one_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hC : 1 ≤ C) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 < r) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hv : Measurable v) (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ, |φ z - θ z| ≤ r) (hvbound : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    (∫⁻ z, ∫⁻ t : ℝ, ENNReal.ofReal ((orthogonalProjectionDensity μ (φ z) (t - v z) -
      orthogonalProjectionDensity μ (θ z) t) ^ 2) ∂volume ∂κ) ≤
        A * ENNReal.ofReal (uniformProjectionCoefficient s * C * r ^ (2 * s - 2)) := by
  simpa only [max_eq_left hC] using uniform_correlated_projectionDensity_energy_bound
    μ hs hs₂ hfr r hr hsource κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound

end FalconerPacking
