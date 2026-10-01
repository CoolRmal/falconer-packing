/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Weighted convolution embedding

Cauchy--Schwarz with the kernel as a weight and positive Tonelli give the weighted
embedding estimate. The convolution is an actual Bochner integral, whose integrability
follows from the Schwartz hypotheses.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Convolution

namespace FalconerPacking

/-- Weighted Cauchy--Schwarz, including infinite positive integrals. -/
theorem lintegral_weighted_sq_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {f w : α → ℝ≥0∞}
    (hf : Measurable f) (hw : Measurable w) :
    (∫⁻ x, f x * w x ∂μ) ^ 2 ≤
      (∫⁻ x, w x ∂μ) * ∫⁻ x, f x ^ 2 * w x ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.withDensity w)
    Real.HolderConjugate.two_two hf.aemeasurable
    (measurable_const (a := (1 : ℝ≥0∞))).aemeasurable
  simp only [Pi.mul_apply, mul_one, ENNReal.rpow_two, one_pow, lintegral_one,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [lintegral_withDensity_eq_lintegral_mul μ hw hf,
    lintegral_withDensity_eq_lintegral_mul μ hw (hf.pow_const 2)] at h
  have hs := pow_le_pow_left' h 2
  have hroot (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simpa only [Pi.mul_apply, mul_pow, hroot, mul_comm] using hs

/-- The complex convolution of two Schwartz functions exists at every point. -/
theorem schwartz_convolutionExistsAt
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ConvolutionExistsAt f k x (ContinuousLinearMap.mul ℂ ℂ) volume := by
  have hk : Integrable (fun y ↦ k (x - y)) volume :=
    (integrable_comp_sub_left k x).mpr k.integrable
  exact hk.bdd_mul f.continuous.aestronglyMeasurable
    (Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ f))

/-- The actual Schwartz convolution is continuous, hence measurable for every Borel weight. -/
theorem continuous_schwartz_convolution
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Continuous (f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) := by
  have hk : BddAbove (range fun y ↦ ‖k y‖) := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 k, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact SchwartzMap.norm_le_seminorm ℝ k y
  exact hk.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) f.integrable k.continuous

/-- Pointwise weighted Cauchy--Schwarz for the actual Schwartz convolution. -/
theorem schwartz_convolution_enorm_sq_le
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖ₑ ^ 2 ≤
      (∫⁻ y, ‖k y‖ₑ) * ∫⁻ y, ‖f y‖ₑ ^ 2 * ‖k (x - y)‖ₑ := by
  have hn : ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖ₑ ≤
      ∫⁻ y, ‖f y‖ₑ * ‖k (x - y)‖ₑ := by
    simpa only [convolution_def, ContinuousLinearMap.mul_apply', enorm_mul] using
      enorm_integral_le_lintegral_enorm (fun y ↦ f y * k (x - y))
  have hcs := lintegral_weighted_sq_le volume
    f.continuous.measurable.enorm (k.continuous.measurable.comp
      ((measurable_const (a := x)).sub measurable_id)).enorm
  have hk : (∫⁻ y, ‖k (x - y)‖ₑ) = ∫⁻ y, ‖k y‖ₑ := by
    exact lintegral_sub_left_eq_self (μ := volume) (fun y ↦ ‖k y‖ₑ) x
  exact (pow_le_pow_left' hn 2).trans (hk ▸ hcs)

/-- Positive Tonelli expresses the weighted convolution energy through the kernel potential. -/
theorem schwartz_convolution_energy_le_potential
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (τ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite τ] :
    (∫⁻ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖ₑ ^ 2 ∂τ) ≤
      (∫⁻ y, ‖k y‖ₑ) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ∫⁻ x, ‖k (x - y)‖ₑ ∂τ := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, ‖k y‖ₑ) *
        (∫⁻ y, ‖f y‖ₑ ^ 2 * ‖k (x - y)‖ₑ) ∂τ :=
      lintegral_mono (schwartz_convolution_enorm_sq_le f k)
    _ = (∫⁻ y, ‖k y‖ₑ) *
        ∫⁻ x, ∫⁻ y, ‖f y‖ₑ ^ 2 * ‖k (x - y)‖ₑ ∂volume ∂τ := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = (∫⁻ y, ‖k y‖ₑ) * ∫⁻ y, ∫⁻ x, ‖f y‖ₑ ^ 2 * ‖k (x - y)‖ₑ ∂τ := by
      rw [lintegral_lintegral_swap (by fun_prop)]
    _ = _ := by
      congr 1
      apply lintegral_congr
      intro y
      exact lintegral_const_mul _
        (k.continuous.measurable.comp
          (measurable_id.sub (measurable_const (a := y)))).enorm

/-- Kernel potential bounds on a measurable region and its complement yield the embedding. -/
theorem schwartz_convolution_weighted_embedding
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (τ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite τ]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : MeasurableSet P) {A B : ℝ≥0∞}
    (hA : ∀ y ∈ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ A)
    (hB : ∀ y ∉ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ B) :
    (∫⁻ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖ₑ ^ 2 ∂τ) ≤
      (∫⁻ y, ‖k y‖ₑ) *
        (A * (∫⁻ y in P, ‖f y‖ₑ ^ 2) + B * ∫⁻ y in Pᶜ, ‖f y‖ₑ ^ 2) := by
  apply (schwartz_convolution_energy_le_potential f k τ).trans
  apply mul_le_mul' le_rfl
  rw [← lintegral_add_compl (fun y ↦ ‖f y‖ₑ ^ 2 * ∫⁻ x, ‖k (x - y)‖ₑ ∂τ) hP]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ y in P, A * ‖f y‖ₑ ^ 2 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hP] with y hy
        simpa only [mul_comm] using mul_le_mul' le_rfl (hA y hy)
      _ = _ := lintegral_const_mul _ (by fun_prop)
  · calc
      _ ≤ ∫⁻ y in Pᶜ, B * ‖f y‖ₑ ^ 2 := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hP.compl] with y hy
        simpa only [mul_comm] using mul_le_mul' le_rfl (hB y hy)
      _ = _ := lintegral_const_mul _ (by fun_prop)

/-- The embedding applies to a function reproduced by its convolution kernel. -/
theorem schwartz_weighted_embedding_of_reproducing
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (τ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite τ]
    (hreproduce : ∀ x, (f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x = f x)
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : MeasurableSet P) {A B : ℝ≥0∞}
    (hA : ∀ y ∈ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ A)
    (hB : ∀ y ∉ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ B) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂τ) ≤ (∫⁻ y, ‖k y‖ₑ) *
      (A * (∫⁻ y in P, ‖f y‖ₑ ^ 2) + B * ∫⁻ y in Pᶜ, ‖f y‖ₑ ^ 2) := by
  simpa only [hreproduce] using schwartz_convolution_weighted_embedding f k τ hP hA hB

/-- Finite potential bounds give finite weighted convolution energy, not merely a formal
inequality with an infinite right-hand side. -/
theorem schwartz_convolution_energy_ne_top_of_potential_bounds
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (τ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite τ]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : MeasurableSet P) {A B : ℝ≥0∞}
    (hAfinite : A ≠ ∞) (hBfinite : B ≠ ∞)
    (hA : ∀ y ∈ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ A)
    (hB : ∀ y ∉ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ B) :
    (∫⁻ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖ₑ ^ 2 ∂τ) ≠ ∞ := by
  have hk : (∫⁻ y, ‖k y‖ₑ) ≠ ∞ := k.integrable.hasFiniteIntegral.ne
  have hf : (∫⁻ y, ‖f y‖ₑ ^ 2) ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (f.memLp 2 volume).2
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using h.ne
  have hfP : (∫⁻ y in P, ‖f y‖ₑ ^ 2) ≠ ∞ :=
    ne_top_of_le_ne_top hf (setLIntegral_le_lintegral P _)
  have hfPc : (∫⁻ y in Pᶜ, ‖f y‖ₑ ^ 2) ≠ ∞ :=
    ne_top_of_le_ne_top hf (setLIntegral_le_lintegral Pᶜ _)
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hk (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top hAfinite hfP, ENNReal.mul_ne_top hBfinite hfPc⟩))
    (schwartz_convolution_weighted_embedding f k τ hP hA hB)

/-- Finite potential bounds put the actual convolution in the weighted L² space. -/
theorem schwartz_convolution_memLp_of_potential_bounds
    (f k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (τ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite τ]
    {P : Set (EuclideanSpace ℝ (Fin 2))} (hP : MeasurableSet P) {A B : ℝ≥0∞}
    (hAfinite : A ≠ ∞) (hBfinite : B ≠ ∞)
    (hA : ∀ y ∈ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ A)
    (hB : ∀ y ∉ P, ∫⁻ x, ‖k (x - y)‖ₑ ∂τ ≤ B) :
    MemLp (f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) 2 τ := by
  refine ⟨(continuous_schwartz_convolution f k).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
    (schwartz_convolution_energy_ne_top_of_potential_bounds f k τ hP
      hAfinite hBfinite hA hB).lt_top

end FalconerPacking
