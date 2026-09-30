/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.WeakDensityLimit
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Absolute continuity from a bounded Schwartz pairing

A finite positive measure whose action on complex Schwartz functions is bounded in the
Lebesgue `L²` norm satisfies the corresponding square-root open-set mass bound. Smooth
compactly supported cutoffs and measure regularity establish the implication directly.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace FalconerPacking

/-- A compact subset of an open subset of the line has a smooth compactly supported cutoff. -/
theorem exists_smooth_compact_cutoff_real {K U : Set ℝ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      EqOn f 1 K ∧ EqOn f 0 Uᶜ ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨R, _, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℝ)
  let V : Set ℝ := U ∩ Metric.ball 0 R
  have hV : IsOpen V := hU.inter Metric.isOpen_ball
  have hKV : K ⊆ V := fun x hx ↦ ⟨hKU hx, hKR hx⟩
  obtain ⟨f, hfzero, hfone, hfrange⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (modelWithCornersSelf ℝ ℝ) hV.isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.mpr hKV) (n := ⊤)
  have hsupp : Function.support f ⊆ Metric.closedBall (0 : ℝ) R := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Metric.ball_subset_closedBall hxV.2
    · exact False.elim (hx (hfzero hxV))
  have hfcompact : HasCompactSupport (f : ℝ → ℝ) :=
    (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset isClosed_closure
      (closure_minimal hsupp Metric.isClosed_closedBall)
  refine ⟨f, f.contMDiff.contDiff, hfcompact, hfone, ?_, hfrange⟩
  intro x hx
  exact hfzero (fun hxV ↦ hx hxV.1)

private theorem schwartz_cutoff_eLpNorm_le_aux {φ : SchwartzMap ℝ ℂ} {U : Set ℝ}
    (hU : MeasurableSet U) (hzero : ∀ x ∉ U, φ x = 0) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    eLpNorm (φ : ℝ → ℂ) 2 volume ≤ volume U ^ (1 / 2 : ℝ) := by
  have hmono : eLpNorm (φ : ℝ → ℂ) 2 volume ≤
      eLpNorm (U.indicator (fun _ : ℝ ↦ (1 : ℝ))) 2 volume := by
    apply eLpNorm_mono_ae
    filter_upwards [] with x
    by_cases hx : x ∈ U
    · simpa only [indicator_of_mem hx, norm_one] using hbound x
    · simp only [hzero x hx, norm_zero, indicator_of_notMem hx, norm_zero, le_refl]
  have heq := eLpNorm_indicator_const (μ := (volume : Measure ℝ))
    (c := (1 : ℝ)) hU (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  norm_num at heq
  rwa [heq] at hmono

/-- A bounded Schwartz pairing controls the mass of a compact subset of an open set. -/
theorem compact_mass_le_of_schwartz_L2_bound {μ : Measure ℝ} [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : SchwartzMap ℝ ℂ,
      ‖∫ x, φ x ∂μ‖ ≤ C * ‖φ.toLp 2 volume‖)
    {K U : Set ℝ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    μ K ≤ ENNReal.ofReal C * volume U ^ (1 / 2 : ℝ) := by
  obtain ⟨f, hfsmooth, hfcompact, hfone, hfzero, hfrange⟩ :=
    exists_smooth_compact_cutoff_real hK hU hKU
  have hfc : HasCompactSupport (fun x ↦ (f x : ℂ)) :=
    hfcompact.comp_left Complex.ofReal_zero
  let φ : SchwartzMap ℝ ℂ :=
    hfc.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hfsmooth)
  have hφ : ∀ x, φ x = (f x : ℂ) := fun _ ↦ rfl
  have hnorm : eLpNorm (φ : ℝ → ℂ) 2 volume ≤ volume U ^ (1 / 2 : ℝ) := by
    apply schwartz_cutoff_eLpNorm_le_aux hU.measurableSet
    · intro x hx
      simp only [hφ, hfzero hx, Pi.zero_apply, Complex.ofReal_zero]
    · intro x
      simpa only [hφ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hfrange x).1] using (hfrange x).2
  have hpair := hbound φ
  have hint : (∫ x, φ x ∂μ) = (∫ x, f x ∂μ : ℝ) := integral_complex_ofReal
  rw [hint, Complex.norm_real, Real.norm_eq_abs] at hpair
  calc
    μ K ≤ ENNReal.ofReal (∫ x, f x ∂μ) :=
      (hfsmooth.continuous.integrable_of_hasCompactSupport hfcompact).measure_le_integral
        (Eventually.of_forall fun x ↦ (hfrange x).1) (fun x hx ↦ (hfone hx).ge)
    _ ≤ ENNReal.ofReal (C * ‖φ.toLp 2 volume‖) :=
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hpair)
    _ = ENNReal.ofReal C * eLpNorm (φ : ℝ → ℂ) 2 volume := by
      rw [ENNReal.ofReal_mul hC, SchwartzMap.norm_toLp,
        ENNReal.ofReal_toReal (φ.eLpNorm_lt_top 2 volume).ne]
    _ ≤ ENNReal.ofReal C * volume U ^ (1 / 2 : ℝ) := mul_le_mul' le_rfl hnorm

/-- The Schwartz pairing bound gives the exact square-root bound on every open set. -/
theorem open_mass_le_of_schwartz_L2_bound {μ : Measure ℝ} [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : SchwartzMap ℝ ℂ,
      ‖∫ x, φ x ∂μ‖ ≤ C * ‖φ.toLp 2 volume‖)
    {U : Set ℝ} (hU : IsOpen U) :
    μ U ≤ ENNReal.ofReal C * volume U ^ (1 / 2 : ℝ) := by
  rw [hU.measure_eq_iSup_isCompact μ]
  exact iSup_le fun K ↦ iSup_le fun hKU ↦ iSup_le fun hK ↦
    compact_mass_le_of_schwartz_L2_bound hC hbound hK hU hKU

/-- A finite positive measure bounded on Schwartz tests in the Lebesgue `L²` norm is
absolutely continuous with respect to Lebesgue measure. -/
theorem absolutelyContinuous_of_schwartz_L2_bound {μ : Measure ℝ} [IsFiniteMeasure μ]
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : SchwartzMap ℝ ℂ,
      ‖∫ x, φ x ∂μ‖ ≤ C * ‖φ.toLp 2 volume‖) : μ ≪ volume := by
  apply absolutelyContinuous_of_open_power_bound ENNReal.ofReal_ne_top
    (by norm_num : (0 : ℝ) < 1 / 2)
  intro U hU
  exact open_mass_le_of_schwartz_L2_bound hC hbound hU

end FalconerPacking
