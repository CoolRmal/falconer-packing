/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleBallMass
import FalconerPacking.WeightedConvolutionEmbedding

/-!
# Convolution of complex circle data with a compact spectral bump

The actual local mass of normalized circle measure supplies the factor `a/r` in
Cauchy--Schwarz. Positive Tonelli then gives the global squared-norm bound.
-/

noncomputable section

open MeasureTheory Set Filter SchwartzMap
open scoped ENNReal

namespace FalconerPacking

/-- Convolution of complex spectral data on the circle with a Schwartz frequency bump. -/
def circleSpectralConvolution (r : ℝ)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∫ ξ, g ξ * k (x - ξ) ∂normalizedCircleMeasure r

/-- Integrable circle data give an actual integrable convolution integrand at every point. -/
theorem integrable_circleSpectralConvolution_integrand
    (r : ℝ) {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun ξ ↦ g ξ * k (x - ξ)) (normalizedCircleMeasure r) := by
  exact hg.mul_bdd (k.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ SchwartzMap.norm_le_seminorm ℝ k (x - ξ))

/-- Integrable circle data convolve to an actual continuous function. -/
theorem continuous_circleSpectralConvolution
    (r : ℝ) {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Continuous (circleSpectralConvolution r g k) := by
  have hk : BddAbove (range fun x ↦ ‖k x‖) := by
    refine ⟨SchwartzMap.seminorm ℝ 0 0 k, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact SchwartzMap.norm_le_seminorm ℝ k x
  exact hk.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hg k.continuous

/-- Pointwise Cauchy--Schwarz uses the proved circle-ball mass, not a label count. -/
theorem circleSpectralConvolution_enorm_sq_le
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Measurable g)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ‖circleSpectralConvolution r g k x‖ₑ ^ 2 ≤ ENNReal.ofReal (a / r) *
      ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 * ‖k (x - ξ)‖ₑ ^ 2 ∂normalizedCircleMeasure r := by
  let f := fun ξ ↦ ‖g ξ * k (x - ξ)‖ₑ
  let w := (Metric.closedBall x a).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hf : Measurable f := (hg.mul (k.continuous.measurable.comp
    (measurable_const.sub measurable_id))).enorm
  have hw : Measurable w := measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  have hz (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ξ ∉ Metric.closedBall x a) :
      k (x - ξ) = 0 := by
    by_contra h
    have hs := hk h
    apply hξ
    simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using hs
  have he (ξ : EuclideanSpace ℝ (Fin 2)) : f ξ * w ξ = f ξ := by
    by_cases hξ : ξ ∈ Metric.closedBall x a
    · simp [w, hξ]
    · simp [f, hz ξ hξ]
  have he₂ (ξ : EuclideanSpace ℝ (Fin 2)) : f ξ ^ 2 * w ξ = f ξ ^ 2 := by
    by_cases hξ : ξ ∈ Metric.closedBall x a
    · simp [w, hξ]
    · simp [f, hz ξ hξ]
  have hcs := lintegral_weighted_sq_le (normalizedCircleMeasure r) hf hw
  simp_rw [he, he₂] at hcs
  have hmass : (∫⁻ ξ, w ξ ∂normalizedCircleMeasure r) ≤ ENNReal.ofReal (a / r) := by
    rw [show w = (Metric.closedBall x a).indicator (fun _ ↦ (1 : ℝ≥0∞)) from rfl,
      lintegral_indicator Metric.isClosed_closedBall.measurableSet, setLIntegral_const, one_mul]
    exact normalizedCircleMeasure_closedBall_le hr ha x
  have hnorm : ‖circleSpectralConvolution r g k x‖ₑ ≤
      ∫⁻ ξ, f ξ ∂normalizedCircleMeasure r :=
    enorm_integral_le_lintegral_enorm _
  have hf₂ (ξ : EuclideanSpace ℝ (Fin 2)) :
      f ξ ^ 2 = ‖g ξ‖ₑ ^ 2 * ‖k (x - ξ)‖ₑ ^ 2 := by
    dsimp only [f]
    rw [enorm_mul, mul_pow]
  simp_rw [hf₂] at hcs
  refine (pow_le_pow_left' hnorm 2).trans (hcs.trans ?_)
  exact mul_le_mul_left hmass _

/-- The global quadratic convolution bound for actual circle data. -/
theorem lintegral_circleSpectralConvolution_sq_le
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Measurable g)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a) :
    (∫⁻ x, ‖circleSpectralConvolution r g k x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 ∂normalizedCircleMeasure r := by
  have hkm := k.continuous.measurable
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a / r) *
        ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 * ‖k (x - ξ)‖ₑ ^ 2 ∂normalizedCircleMeasure r :=
      lintegral_mono (circleSpectralConvolution_enorm_sq_le hr ha hg k hk)
    _ = ENNReal.ofReal (a / r) *
        ∫⁻ ξ, ∫⁻ x, ‖g ξ‖ₑ ^ 2 * ‖k (x - ξ)‖ₑ ^ 2 ∂volume
          ∂normalizedCircleMeasure r := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_lintegral_swap (by fun_prop)]
    _ = ENNReal.ofReal (a / r) *
        ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 * (∫⁻ x, ‖k x‖ₑ ^ 2) ∂normalizedCircleMeasure r := by
      congr 1
      apply lintegral_congr
      intro ξ
      rw [lintegral_const_mul _ (by fun_prop),
        lintegral_sub_right_eq_self (fun x ↦ ‖k x‖ₑ ^ 2) ξ]
    _ = _ := by
      rw [lintegral_mul_const _ (hg.enorm.pow_const 2)]
      ring

/-- A finite multiplier family costs its square-sum bound, not its cardinality. -/
theorem sum_lintegral_circleSpectralConvolution_sq_le {ι : Type*}
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (I : Finset ι) (m : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hm : ∀ i ∈ I, Measurable (m i))
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Measurable g)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a)
    {B : ℝ≥0∞} (hB : ∀ ξ, ∑ i ∈ I, ‖m i ξ‖ₑ ^ 2 ≤ B) :
    (∑ i ∈ I, ∫⁻ x, ‖circleSpectralConvolution r (fun ξ ↦ m i ξ * g ξ) k x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) * B *
        ∫⁻ ξ, ‖g ξ‖ₑ ^ 2 ∂normalizedCircleMeasure r := by
  calc
    _ ≤ ∑ i ∈ I, ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ∫⁻ ξ, ‖m i ξ * g ξ‖ₑ ^ 2 ∂normalizedCircleMeasure r :=
      Finset.sum_le_sum fun i hi ↦ lintegral_circleSpectralConvolution_sq_le
        hr ha ((hm i hi).mul hg) k hk
    _ = ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ∫⁻ ξ, ∑ i ∈ I, ‖m i ξ * g ξ‖ₑ ^ 2 ∂normalizedCircleMeasure r := by
      rw [lintegral_finsetSum I (f := fun i ξ ↦ ‖m i ξ * g ξ‖ₑ ^ (2 : ℕ))
        (fun i hi ↦ ((hm i hi).mul hg).enorm.pow_const 2), Finset.mul_sum]
    _ ≤ ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ∫⁻ ξ, B * ‖g ξ‖ₑ ^ 2 ∂normalizedCircleMeasure r := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro ξ
      simp only [enorm_mul, mul_pow, ← Finset.sum_mul]
      exact mul_le_mul_left (hB ξ) _
    _ = _ := by
      rw [lintegral_const_mul _ (hg.enorm.pow_const 2)]
      simp only [mul_assoc]

/-- Finite circle energy gives actual square integrability of the continuous convolution. -/
theorem memLp_circleSpectralConvolution
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Measurable g)
    (hg₂ : MemLp g 2 (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hk : Function.support k ⊆ Metric.closedBall 0 a) :
    MemLp (circleSpectralConvolution r g k) 2 volume := by
  have hi := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) hg₂
  refine ⟨(continuous_circleSpectralConvolution r hi k).aestronglyMeasurable, ?_⟩
  have hgf : (∫⁻ ξ, ‖g ξ‖ₑ ^ (2 : ℕ) ∂normalizedCircleMeasure r) < ∞ := by
    simpa using (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp hg₂.eLpNorm_lt_top
  have hkf : (∫⁻ x, ‖k x‖ₑ ^ (2 : ℕ)) < ∞ := by
    simpa using (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp (k.memLp 2 volume).eLpNorm_lt_top
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact (lintegral_circleSpectralConvolution_sq_le hr ha hg k hk).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hkf) hgf)

end FalconerPacking
