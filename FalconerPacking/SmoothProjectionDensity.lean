/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjectionLine
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Smooth densities of orthogonal projections

Integrating a smooth compactly supported source along a line gives a smooth compactly
supported function of the perpendicular coordinate. The formula is pointwise, so the same
representative may be tested against singular measures.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal ContDiff Convolution

namespace FalconerPacking

/-- The ordinary real-valued line density in an orthonormal frame. -/
def smoothLineDensity (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (t : ℝ) : ℝ :=
  ∫ r : ℝ, f (e (t + r * Complex.I))

private theorem frame_im_le_norm_aux
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (t r : ℝ) :
    |r| ≤ ‖e (t + r * Complex.I)‖ := by
  rw [e.norm_map]
  simpa using Complex.abs_im_le_norm ((t : ℂ) + r * Complex.I)

private theorem frame_re_le_norm_aux
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) (t r : ℝ) :
    |t| ≤ ‖e (t + r * Complex.I)‖ := by
  rw [e.norm_map]
  simpa using Complex.abs_re_le_norm ((t : ℂ) + r * Complex.I)

private theorem line_integrand_zero_aux
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {R t r : ℝ}
    (hR : ∀ x ∈ tsupport f, ‖x‖ ≤ R) (hr : R < |r|) :
    f (e (t + r * Complex.I)) = 0 := by
  by_contra h
  exact (not_lt_of_ge ((frame_im_le_norm_aux e t r).trans
    (hR _ (subset_tsupport _ (mem_support.mpr h))))) hr

/-- A compactly supported source gives a compactly supported integrand on every line. -/
theorem hasCompactSupport_line_integrand
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun r : ℝ ↦ f (e (t + r * Complex.I))) := by
  obtain ⟨R, _, hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.of_support_subset_isCompact
    (show IsCompact (Icc (-R) R) from isCompact_Icc)
  intro r hr
  by_contra h
  have hb : R < |r| := by simpa only [mem_Icc, ← abs_le, not_le] using h
  exact (mem_support.mp hr) (line_integrand_zero_aux e hR hb)

/-- Smoothness passes through the line integral by compactly supported parameter integration. -/
theorem contDiff_smoothLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : ContDiff ℝ ∞ (smoothLineDensity e f) := by
  obtain ⟨R, _, hR⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  let g (t r : ℝ) := f (e (t - r * Complex.I))
  have hg : ContDiff ℝ ∞ (Function.uncurry g) := by
    dsimp [g, Function.uncurry]
    apply hf.comp
    apply e.toContinuousLinearEquiv.contDiff.comp
    exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).sub
      ((Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  have hz : ∀ t r : ℝ, t ∈ (univ : Set ℝ) → r ∉ Icc (-R) R → g t r = 0 := by
    intro t r _ hr
    have hb : R < |-r| := by simpa only [abs_neg, mem_Icc, ← abs_le, not_le] using hr
    simpa only [g, Complex.ofReal_neg, neg_mul, add_neg_cancel_right, sub_eq_add_neg] using
      line_integrand_zero_aux e hR hb (t := t)
  have h := contDiffOn_convolution_right_with_param_comp
    (n := ⊤) (μ := volume) (ContinuousLinearMap.mul ℝ ℝ)
    (v := fun _ : ℝ ↦ (0 : ℝ)) contDiffOn_const
    isOpen_univ isCompact_Icc hz
    (show LocallyIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume from
      continuous_const.locallyIntegrable) hg.contDiffOn
  rw [contDiffOn_univ] at h
  convert h using 1
  funext t
  simp only [smoothLineDensity, convolution, ContinuousLinearMap.mul_apply', g,
    zero_sub, Complex.ofReal_neg, neg_mul, sub_neg_eq_add, one_mul]

/-- The perpendicular support is contained in the projection of a fixed source ball. -/
theorem hasCompactSupport_smoothLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (smoothLineDensity e f) := by
  obtain ⟨R, _, hR⟩ := hf.isCompact.isBounded.exists_pos_norm_le
  apply HasCompactSupport.of_support_subset_isCompact
    (show IsCompact (Icc (-R) R) from isCompact_Icc)
  intro t ht
  by_contra h
  have hb : R < |t| := by simpa only [mem_Icc, ← abs_le, not_le] using h
  apply (mem_support.mp ht)
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun r ↦ by
    by_contra hfr
    exact (not_lt_of_ge ((frame_re_le_norm_aux e t r).trans
      (hR _ (subset_tsupport _ (mem_support.mpr hfr))))) hb

/-- The smooth line density agrees pointwise with the extended nonnegative line integral. -/
theorem ofReal_smoothLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hpos : ∀ x, 0 ≤ f x) (t : ℝ) :
    ENNReal.ofReal (smoothLineDensity e f t) =
      orthogonalLineDensity e (fun x ↦ ENNReal.ofReal (f x)) t := by
  apply ofReal_integral_eq_lintegral_ofReal
    ((hf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_line_integrand e hc t))
  exact Filter.Eventually.of_forall fun _ ↦ hpos _

/-- A smooth compact source supplies a genuine complex Schwartz representative on every line. -/
theorem exists_schwartz_smoothLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ∃ g : SchwartzMap ℝ ℂ, ∀ t, g t = (smoothLineDensity e f t : ℂ) := by
  have hcont : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ smoothLineDensity e f) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_smoothLineDensity e hf hc)
  have hsupp : HasCompactSupport (Complex.ofRealCLM ∘ smoothLineDensity e f) :=
    (hasCompactSupport_smoothLineDensity e hc).comp_left rfl
  exact ⟨hsupp.toSchwartzMap hcont, fun _ ↦ rfl⟩

theorem smoothLineDensity_nonneg
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hpos : ∀ x, 0 ≤ f x) (t : ℝ) :
    0 ≤ smoothLineDensity e f t := integral_nonneg fun _ ↦ hpos _

/-- Positive smooth compact sources yield actual positive Schwartz projection densities. -/
theorem exists_positive_schwartz_orthogonalLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hpos : ∀ x, 0 ≤ f x) :
    ∃ g : SchwartzMap ℝ ℂ, (∀ t, g t = (smoothLineDensity e f t : ℂ)) ∧
      (∀ t, 0 ≤ (g t).re ∧ (g t).im = 0) ∧
      (∀ t, ENNReal.ofReal (g t).re =
        orthogonalLineDensity e (fun x ↦ ENNReal.ofReal (f x)) t) ∧
      (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).map (fun x ↦ inner ℝ x (e 1)) =
        volume.withDensity (fun t ↦ ENNReal.ofReal (g t).re) := by
  obtain ⟨g, hg⟩ := exists_schwartz_smoothLineDensity e hf hc
  have he (t : ℝ) : ENNReal.ofReal (g t).re =
      orthogonalLineDensity e (fun x ↦ ENNReal.ofReal (f x)) t := by
    rw [hg t, Complex.ofReal_re]
    exact ofReal_smoothLineDensity e hf.continuous hc hpos t
  refine ⟨g, hg, ?_, he, ?_⟩
  · intro t
    rw [hg t]
    exact ⟨smoothLineDensity_nonneg e hpos t, Complex.ofReal_im _⟩
  · simpa only [he] using map_orthogonal_withDensity_eq e hf.continuous.measurable.ennreal_ofReal

end FalconerPacking
