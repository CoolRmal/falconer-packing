/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularTruncation
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Averaging short angular intervals with correlated parameters

A bounded angular marginal controls the average of a sliding interval integral. The other
angular map can depend on the same parameter; no independence assumption is used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The square of an integral is bounded by the squared integrand times total mass. -/
theorem sq_lintegral_le_lintegral_sq_mul_mass
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * μ univ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
      Real.HolderConjugate 2 2) hf (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two, one_pow, lintegral_const,
    one_mul] at h
  have hsqrt (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simpa only [mul_pow, hsqrt] using pow_le_pow_left' h 2

/-- The fundamental theorem of calculus and Cauchy--Schwarz give a squared increment bound. -/
theorem enorm_sub_sq_le_interval_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → V} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    {a b : ℝ} (hab : a ≤ b) :
    ‖F b - F a‖ₑ ^ 2 ≤ ENNReal.ofReal (b - a) * ∫⁻ t in Icc a b, ‖F' t‖ₑ ^ 2 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hF t) (hF'.intervalIntegrable a b)
  rw [← hFTC, intervalIntegral.integral_of_le hab]
  calc
    ‖∫ t in Ioc a b, F' t‖ₑ ^ 2 ≤ (∫⁻ t in Ioc a b, ‖F' t‖ₑ) ^ 2 :=
      pow_le_pow_left' (enorm_integral_le_lintegral_enorm _) 2
    _ ≤ (∫⁻ t in Ioc a b, ‖F' t‖ₑ ^ 2) * (volume.restrict (Ioc a b)) univ :=
      sq_lintegral_le_lintegral_sq_mul_mass _ hF'.aestronglyMeasurable.enorm
    _ = _ := by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc,
        setLIntegral_congr Ioc_ae_eq_Icc, mul_comm]

/-- The squared increment estimate is independent of the order of the two endpoints. -/
theorem enorm_sub_sq_le_uIcc_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → V} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    (a b : ℝ) :
    ‖F b - F a‖ₑ ^ 2 ≤ ENNReal.ofReal |b - a| * ∫⁻ t in uIcc a b, ‖F' t‖ₑ ^ 2 := by
  rcases le_total a b with hab | hba
  · simpa only [uIcc_of_le hab, abs_of_nonneg (sub_nonneg.mpr hab)] using
      enorm_sub_sq_le_interval_derivative hF hF' hab
  · rw [enorm_sub_rev, abs_sub_comm, uIcc_comm]
    simpa only [uIcc_of_le hba, abs_of_nonneg (sub_nonneg.mpr hba)] using
      enorm_sub_sq_le_interval_derivative hF hF' hba

/-- A short increment is controlled by the derivative in a sliding interval, localized to
the range of its endpoints. -/
theorem enorm_sub_sq_le_sliding_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → V} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    {a b x y h : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : |y - x| ≤ h) :
    ‖F y - F x‖ₑ ^ 2 ≤ ENNReal.ofReal h *
      ∫⁻ t in Icc (x - h) (x + h), (Icc a b).indicator (fun t ↦ ‖F' t‖ₑ ^ 2) t := by
  have hrange : uIcc x y ⊆ Icc a b := by
    intro t ht
    exact ⟨(le_min hx.1 hy.1).trans ht.1, ht.2.trans (max_le hx.2 hy.2)⟩
  have hwindow : uIcc x y ⊆ Icc (x - h) (x + h) := by
    have hh : 0 ≤ h := (abs_nonneg _).trans hxy
    obtain ⟨h₁, h₂⟩ := abs_le.mp hxy
    intro t ht
    exact ⟨(le_min (by linarith) (by linarith)).trans ht.1,
      ht.2.trans (max_le (by linarith) (by linarith))⟩
  refine (enorm_sub_sq_le_uIcc_derivative hF hF' x y).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hxy) ?_)
  calc
    ∫⁻ t in uIcc x y, ‖F' t‖ₑ ^ 2 =
        ∫⁻ t in uIcc x y, (Icc a b).indicator (fun t ↦ ‖F' t‖ₑ ^ 2) t := by
      apply setLIntegral_congr_fun measurableSet_uIcc
      intro t ht
      exact (indicator_of_mem (hrange ht) (fun t ↦ ‖F' t‖ₑ ^ 2)).symm
    _ ≤ _ := lintegral_mono_set hwindow

/-- A bounded angular marginal controls every sliding interval integral. -/
theorem lintegral_sliding_interval_le
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    {θ : α → ℝ} (hθ : Measurable θ) {A : ℝ≥0∞}
    (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (h : ℝ) :
    ∫⁻ z, ∫⁻ t in Icc (θ z - h) (θ z + h), G t ∂volume ∂κ ≤
      (A * ENNReal.ofReal (2 * h)) * ∫⁻ t, G t := by
  let W : α × ℝ → ℝ≥0∞ := fun p ↦
    {p : α × ℝ | θ p.1 - h ≤ p.2 ∧ p.2 ≤ θ p.1 + h}.indicator (fun p ↦ G p.2) p
  have hW : Measurable W := by
    apply (hG.comp measurable_snd).indicator
    exact (measurableSet_le ((hθ.comp measurable_fst).sub_const h) measurable_snd).inter
      (measurableSet_le measurable_snd ((hθ.comp measurable_fst).add_const h))
  have heq (z : α) : (∫⁻ t in Icc (θ z - h) (θ z + h), G t) = ∫⁻ t, W (z, t) := by
    rw [← lintegral_indicator measurableSet_Icc]
    rfl
  simp_rw [heq]
  rw [lintegral_lintegral_swap hW.aemeasurable]
  calc
    ∫⁻ t, ∫⁻ z, W (z, t) ∂κ ≤ ∫⁻ t, (A * ENNReal.ofReal (2 * h)) * G t := by
      apply lintegral_mono
      intro t
      have hset : MeasurableSet (θ ⁻¹' Icc (t - h) (t + h)) := hθ measurableSet_Icc
      have hpoint (z : α) : W (z, t) =
          (θ ⁻¹' Icc (t - h) (t + h)).indicator (fun _ ↦ G t) z := by
        have hi : (θ z - h ≤ t ∧ t ≤ θ z + h) ↔ (t - h ≤ θ z ∧ θ z ≤ t + h) := by
          constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
        classical
        simp only [W, indicator_apply, mem_setOf_eq, mem_preimage, mem_Icc, hi]
      simp_rw [hpoint]
      rw [lintegral_indicator hset, lintegral_const, Measure.restrict_apply_univ]
      have hmass := (Measure.le_iff.mp hdom) (Icc (t - h) (t + h)) measurableSet_Icc
      rw [Measure.map_apply hθ measurableSet_Icc, Measure.smul_apply,
        smul_eq_mul, Real.volume_Icc, show t + h - (t - h) = 2 * h by ring] at hmass
      exact (mul_le_mul' le_rfl hmass).trans_eq (mul_comm _ _)
    _ = _ := lintegral_const_mul _ hG

/-- Two angular maps on the same parameter space satisfy the averaged derivative estimate.
Only the first marginal needs domination for this estimate. -/
theorem lintegral_correlated_angular_difference_le
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] (κ : Measure α) [SFinite κ]
    {θ φ : α → ℝ} (hθ : Measurable θ) {A : ℝ≥0∞}
    (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    {F F' : ℝ → V} (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : Continuous F')
    {a b h : ℝ} (hh : 0 ≤ h)
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc a b ∧ φ z ∈ Icc a b)
    (hclose : ∀ᵐ z ∂κ, |φ z - θ z| ≤ h) :
    ∫⁻ z, ‖F (φ z) - F (θ z)‖ₑ ^ 2 ∂κ ≤
      A * ENNReal.ofReal (2 * h ^ 2) * ∫⁻ t in Icc a b, ‖F' t‖ₑ ^ 2 := by
  let G := (Icc a b).indicator (fun t ↦ ‖F' t‖ₑ ^ 2)
  have hG : Measurable G := (hF'.enorm.measurable.pow_const 2).indicator measurableSet_Icc
  calc
    ∫⁻ z, ‖F (φ z) - F (θ z)‖ₑ ^ 2 ∂κ ≤
        ∫⁻ z, ENNReal.ofReal h * ∫⁻ t in Icc (θ z - h) (θ z + h), G t ∂volume ∂κ := by
      apply lintegral_mono_ae
      filter_upwards [hrange, hclose] with z hz hc
      exact enorm_sub_sq_le_sliding_derivative hF hF' hz.1 hz.2 hc
    _ = ENNReal.ofReal h * ∫⁻ z, ∫⁻ t in Icc (θ z - h) (θ z + h), G t ∂volume ∂κ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal h * ((A * ENNReal.ofReal (2 * h)) * ∫⁻ t, G t) :=
      mul_le_mul' le_rfl (lintegral_sliding_interval_le κ hθ hdom G hG h)
    _ = _ := by
      rw [show ∫⁻ t, G t = ∫⁻ t in Icc a b, ‖F' t‖ₑ ^ 2 from
        lintegral_indicator measurableSet_Icc _]
      rw [show ENNReal.ofReal (2 * h ^ 2) = ENNReal.ofReal h * ENNReal.ofReal (2 * h) by
        rw [← ENNReal.ofReal_mul hh]; congr 1; ring]
      ring

/-- A dominated marginal controls every nonnegative measurable test. -/
theorem lintegral_comp_le_of_map_le_smul
    {α : Type*} [MeasurableSpace α] (κ : Measure α) {θ : α → ℝ}
    (hθ : Measurable θ) {A : ℝ≥0∞} (hdom : κ.map θ ≤ A • (volume : Measure ℝ))
    {G : ℝ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G (θ z) ∂κ ≤ A * ∫⁻ t, G t := by
  rw [← lintegral_map hG hθ, ← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' hdom le_rfl

/-- The elementary squared difference bound in extended nonnegative norm. -/
theorem enorm_sub_sq_le_two_mul
    {V : Type*} [SeminormedAddCommGroup V] (x y : V) :
    ‖x - y‖ₑ ^ 2 ≤ 2 * (‖x‖ₑ ^ 2 + ‖y‖ₑ ^ 2) := by
  have h : ‖x - y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have hnorm := norm_sub_le x y
    nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using ENNReal.ofReal_le_ofReal h

/-- Both dominated marginals give the complementary estimate without an angular-distance loss. -/
theorem lintegral_correlated_angular_difference_le_norm
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    (κ : Measure α) {θ φ : α → ℝ} (hθ : Measurable θ) (hφ : Measurable φ) {A : ℝ≥0∞}
    (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    {F : ℝ → V} (hF : Continuous F) {a b : ℝ}
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc a b ∧ φ z ∈ Icc a b) :
    ∫⁻ z, ‖F (φ z) - F (θ z)‖ₑ ^ 2 ∂κ ≤
      4 * A * ∫⁻ t in Icc a b, ‖F t‖ₑ ^ 2 := by
  let G := (Icc a b).indicator (fun t ↦ ‖F t‖ₑ ^ 2)
  have hG : Measurable G := (hF.enorm.measurable.pow_const 2).indicator measurableSet_Icc
  calc
    ∫⁻ z, ‖F (φ z) - F (θ z)‖ₑ ^ 2 ∂κ ≤ ∫⁻ z, 2 * (G (φ z) + G (θ z)) ∂κ := by
      apply lintegral_mono_ae
      filter_upwards [hrange] with z hz
      simpa only [G, indicator_of_mem hz.1, indicator_of_mem hz.2] using
        enorm_sub_sq_le_two_mul (F (φ z)) (F (θ z))
    _ = 2 * ((∫⁻ z, G (φ z) ∂κ) + ∫⁻ z, G (θ z) ∂κ) := by
      rw [lintegral_const_mul' _ _ (by norm_num)]
      congr 1
      exact lintegral_add_left (show Measurable (fun z ↦ G (φ z)) from hG.comp hφ) _
    _ ≤ 2 * ((A * ∫⁻ t, G t) + A * ∫⁻ t, G t) :=
      mul_le_mul' le_rfl (add_le_add (lintegral_comp_le_of_map_le_smul κ hφ hφdom hG)
        (lintegral_comp_le_of_map_le_smul κ hθ hθdom hG))
    _ = _ := by
      rw [show ∫⁻ t, G t = ∫⁻ t in Icc a b, ‖F t‖ₑ ^ 2 from
        lintegral_indicator measurableSet_Icc _]
      ring

end FalconerPacking
