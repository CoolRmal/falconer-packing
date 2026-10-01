/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SmoothMeasureApproximation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz source functions from compactly supported measures

Multiplying the convolution of a Schwartz kernel with a bounded source measure by a
smooth compact cutoff gives an actual Schwartz function. The proof replaces the kernel
on the relevant difference set by a smooth compact kernel before differentiating.
-/

noncomputable section

open MeasureTheory Set Function Metric
open scoped ContDiff Convolution

namespace FalconerPacking

/-- A smooth compact complex kernel can be differentiated after convolution with a finite measure. -/
theorem contDiff_compactKernel_measureConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {k : EuclideanSpace ℝ (Fin 2) → ℂ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, k (x - y) ∂μ) := by
  have hz : ∀ p x : EuclideanSpace ℝ (Fin 2), p ∈ univ → x ∉ tsupport k → k x = 0 :=
    fun _ _ _ hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hg : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 2) ×
      EuclideanSpace ℝ (Fin 2) ↦ k p.2) := hk.comp contDiff_snd
  have h := contDiffOn_convolution_right_with_param_comp
    (n := ⊤) (μ := μ) (ContinuousLinearMap.mul ℝ ℂ)
    (v := id) (s := univ) contDiffOn_id isOpen_univ hkc.isCompact hz
    (show LocallyIntegrable (fun _ : EuclideanSpace ℝ (Fin 2) ↦ (1 : ℂ)) μ from
      (integrable_const 1).locallyIntegrable) hg.contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  funext x
  simp only [convolution, ContinuousLinearMap.mul_apply', one_mul, id]

/-- A fixed source cutoff makes Schwartz convolution smooth, with no regularity of the source. -/
theorem contDiff_cutoff_schwartz_measureConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {χ : EuclideanSpace ℝ (Fin 2) → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ContDiff ℝ ∞ (fun x ↦ χ x * ∫ y, K (x - y) ∂μ) := by
  obtain ⟨A, hA, hAbound⟩ := hχc.isCompact.isBounded.exists_pos_norm_le
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
    ⟨A + max M 0 + 1, A + max M 0 + 2, by positivity, by linarith⟩
  let k (x : EuclideanSpace ℝ (Fin 2)) : ℂ := φ x • K x
  have hk : ContDiff ℝ ∞ k := φ.contDiff.smul (K.smooth ⊤)
  have hkc : HasCompactSupport k := φ.hasCompactSupport.smul_right
  have he : (fun x ↦ χ x * ∫ y, K (x - y) ∂μ) =
      (fun x ↦ χ x * ∫ y, k (x - y) ∂μ) := by
    funext x
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul]
    · congr 1
      apply integral_congr_ae
      filter_upwards [hμ] with y hy
      have hxA : ‖x‖ ≤ A := hAbound x (subset_tsupport _ (mem_support.mpr hx))
      have hxy : x - y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) φ.rIn := by
        rw [mem_closedBall, dist_zero_right]
        dsimp only [φ]
        have hn := norm_sub_le x y
        have hM := le_max_left M 0
        linarith
      simp only [k, φ.one_of_mem_closedBall hxy, one_smul]
  rw [he]
  exact hχ.mul (contDiff_compactKernel_measureConvolution μ hk hkc)

/-- The source cutoff gives compact support independently of the kernel tails. -/
theorem hasCompactSupport_cutoff_schwartz_measureConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {χ : EuclideanSpace ℝ (Fin 2) → ℂ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (fun x ↦ χ x * ∫ y, K (x - y) ∂μ) := hχc.mul_right

/-- The actual compactly cut off convolution, bundled as a Schwartz function. -/
def cutoffSchwartzMeasureConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {χ : EuclideanSpace ℝ (Fin 2) → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (hasCompactSupport_cutoff_schwartz_measureConvolution μ K hχc).toSchwartzMap
    (contDiff_cutoff_schwartz_measureConvolution μ hμ K hχ hχc)

@[simp]
theorem cutoffSchwartzMeasureConvolution_apply
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {χ : EuclideanSpace ℝ (Fin 2) → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (x : EuclideanSpace ℝ (Fin 2)) :
    cutoffSchwartzMeasureConvolution μ hμ K hχ hχc x =
      χ x * ∫ y, K (x - y) ∂μ := rfl

/-- Integrable complex source weights also permit differentiation under convolution. -/
theorem contDiff_compactKernel_weightedMeasureConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g μ)
    {k : EuclideanSpace ℝ (Fin 2) → ℂ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) :
    ContDiff ℝ ∞ (fun x ↦ ∫ y, g y * k (x - y) ∂μ) := by
  have hz : ∀ p x : EuclideanSpace ℝ (Fin 2), p ∈ univ → x ∉ tsupport k → k x = 0 :=
    fun _ _ _ hx ↦ image_eq_zero_of_notMem_tsupport hx
  have h := contDiffOn_convolution_right_with_param_comp
    (n := ⊤) (μ := μ) (ContinuousLinearMap.mul ℝ ℂ)
    (v := id) (s := univ) contDiffOn_id isOpen_univ hkc.isCompact hz
    hg.locallyIntegrable (hk.comp contDiff_snd).contDiffOn
  rw [contDiffOn_univ] at h
  exact h

/-- A bounded source and compact kernel give compact support even for complex source weights. -/
theorem hasCompactSupport_compactKernel_weightedMeasureConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    {k : EuclideanSpace ℝ (Fin 2) → ℂ} (hkc : HasCompactSupport k)
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M) :
    HasCompactSupport (fun x ↦ ∫ y, g y * k (x - y) ∂μ) := by
  obtain ⟨R, _, hR⟩ := hkc.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) (M + R))
  intro x hx
  by_contra hout
  have hnorm : M + R < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hout
  apply mem_support.mp hx
  apply integral_eq_zero_of_ae
  filter_upwards [hμ] with y hy
  have hnot : x - y ∉ tsupport k := by
    intro hxy
    have hr := hR (x - y) hxy
    have htriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - y) y
    linarith
  simp only [image_eq_zero_of_notMem_tsupport hnot, mul_zero, Pi.zero_apply]

/-- The actual weighted convolution of a compact kernel with a bounded source. -/
def compactKernelWeightedConvolution
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g μ)
    {k : EuclideanSpace ℝ (Fin 2) → ℂ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (hasCompactSupport_compactKernel_weightedMeasureConvolution μ g hkc hμ).toSchwartzMap
    (contDiff_compactKernel_weightedMeasureConvolution μ hg hk hkc)

@[simp]
theorem compactKernelWeightedConvolution_apply
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g μ)
    {k : EuclideanSpace ℝ (Fin 2) → ℂ} (hk : ContDiff ℝ ∞ k)
    (hkc : HasCompactSupport k) (x : EuclideanSpace ℝ (Fin 2)) :
    compactKernelWeightedConvolution μ hμ hg hk hkc x =
      ∫ y, g y * k (x - y) ∂μ := rfl

end FalconerPacking
