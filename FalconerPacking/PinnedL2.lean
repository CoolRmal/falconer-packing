/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Density
import FalconerPacking.PinnedMeasure

/-!
# The `L²` criterion for pinned distance sets

The overlap identity of `Density.lean` applies verbatim to the pinned distance law: the `L²`
norm of its `ε`-average is the exact double integral

  `∫∫ (2ε - | |x - y| - |x' - y| |)⁺ dμ(x) dμ(x')`,

which is at most `2ε` times the `μ × μ`-mass of the *hyperbolic tube* around the pin — the pairs
whose distances to `y` differ by less than `2ε`.

The result is a self-contained sufficient condition for the conclusion of Theorem 1.1
(`volume_pinnedDistances_pos_of_hyperbolic_bound`): if that mass is `O(δ)` along a sequence of
scales tending to zero, every source set of positive mass has a pinned distance set of positive
length.  No Fourier transform, no smoothing, and no regularity of the source is used.

This is the sharpest elementary form of the `L²` method, and it is the interface the analytic
branches have to meet.  The hyperbolic tube is exactly where `RadialProjection.lean` enters: the
gradient of `z ↦ |z - y|` is the radial projection `Θ_y`, so the tube around a pair `(x, x')` is
thin precisely when `Θ_y x` and `Θ_y x'` are far apart, which the separation estimate bounds
below by `|det (x - y, x' - y)| / (‖x - y‖ ‖x' - y‖)`.  Controlling that mass for a positive
proportion of pins is the content of Orponen's theorem, which remains open here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- Change of variables for a kernel of the difference under an arbitrary scalar pushforward. -/
theorem lintegral_prod_map_sub (μ : Measure Plane) [SFinite μ] {φ : Plane → ℝ}
    (hφ : Measurable φ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : ℝ × ℝ, f (p.1 - p.2) ∂((μ.map φ).prod (μ.map φ))
      = ∫⁻ q : Plane × Plane, f (φ q.1 - φ q.2) ∂(μ.prod μ) := by
  have hfd : Measurable fun p : ℝ × ℝ => f (p.1 - p.2) :=
    hf.comp (measurable_fst.sub measurable_snd)
  have : SFinite (μ.map φ) := by infer_instance
  calc ∫⁻ p : ℝ × ℝ, f (p.1 - p.2) ∂((μ.map φ).prod (μ.map φ))
      = ∫⁻ u, ∫⁻ v, f (u - v) ∂(μ.map φ) ∂(μ.map φ) := lintegral_prod _ hfd.aemeasurable
    _ = ∫⁻ x, ∫⁻ y, f (φ x - φ y) ∂μ ∂μ := by
        have hOuter : Measurable fun u : ℝ => ∫⁻ v, f (u - v) ∂(μ.map φ) :=
          hfd.lintegral_prod_right'
        rw [lintegral_map hOuter hφ]
        exact lintegral_congr fun x =>
          lintegral_map (hf.comp (measurable_const.sub measurable_id)) hφ
    _ = ∫⁻ q : Plane × Plane, f (φ q.1 - φ q.2) ∂(μ.prod μ) := by
        rw [lintegral_prod]
        exact (hf.comp ((hφ.comp measurable_fst).sub (hφ.comp measurable_snd))).aemeasurable

instance instSFinitePinnedDistanceMeasure (μ : Measure Plane) [SFinite μ] (y : Plane) :
    SFinite (pinnedDistanceMeasure μ y) := by
  rw [pinnedDistanceMeasure]; infer_instance

/-- **The pinned overlap identity.**  The `L²` norm of the `ε`-average of the pinned distance
measure is an explicit double integral over the source: the "hyperbolic annulus" overlap. -/
theorem lintegral_sq_pinnedDistanceMeasure (μ : Measure Plane) [SFinite μ] (y : Plane)
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ t : ℝ, ((pinnedDistanceMeasure μ y) {s : ℝ | |t - s| ≤ ε}) ^ 2)
      = ∫⁻ q : Plane × Plane,
          ENNReal.ofReal (2 * ε - |dist q.1 y - dist q.2 y|) ∂(μ.prod μ) := by
  rw [lintegral_sq_measure_interval_eq _ hε, pinnedDistanceMeasure,
    lintegral_prod_map_sub μ (measurable_dist_right y) measurable_ofReal_overlap]

/-- **An elementary criterion for a positive-length pinned distance set.**  If the hyperbolic
annulus overlap is `O(ε²)` frequently along a sequence of scales tending to zero, then the
pinned distance measure is absolutely continuous, and every source set of positive mass has a
pinned distance set of positive length.

The overlap integral is the exact `L²` norm of the `ε`-averaged pinned distance law, so this is
the sharpest form of the `L²` method, with no Fourier transform and no smoothing. -/
theorem absolutelyContinuous_pinnedDistanceMeasure_of_frequently
    (μ : Measure Plane) [IsFiniteMeasure μ] (y : Plane) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {ε : ℕ → ℝ} (hpos : ∀ n, 0 < ε n) (hto : Tendsto ε atTop (𝓝 0))
    (hfreq : ∃ᶠ n in atTop, (∫⁻ q : Plane × Plane,
        ENNReal.ofReal (2 * ε n - |dist q.1 y - dist q.2 y|) ∂(μ.prod μ))
      ≤ ENNReal.ofReal (4 * (ε n) ^ 2) * C) :
    pinnedDistanceMeasure μ y ≪ volume := by
  have hfin : IsFiniteMeasure (pinnedDistanceMeasure μ y) := by
    rw [pinnedDistanceMeasure]
    exact μ.isFiniteMeasure_map _
  refine absolutelyContinuous_of_frequently _ hC hpos hto (hfreq.mono fun n hn => ?_)
  rw [lintegral_sq_pinnedDistanceMeasure μ y (hpos n)]
  exact hn

/-- The endpoint: a positive-mass source set has a positive-length pinned distance set. -/
theorem volume_pinnedDistances_pos_of_frequently
    (μ : Measure Plane) [IsFiniteMeasure μ] {E : Set Plane} (y : Plane)
    (hμE : 0 < μ E) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {ε : ℕ → ℝ} (hpos : ∀ n, 0 < ε n) (hto : Tendsto ε atTop (𝓝 0))
    (hfreq : ∃ᶠ n in atTop, (∫⁻ q : Plane × Plane,
        ENNReal.ofReal (2 * ε n - |dist q.1 y - dist q.2 y|) ∂(μ.prod μ))
      ≤ ENNReal.ofReal (4 * (ε n) ^ 2) * C) :
    0 < volume (pinnedDistances E y) :=
  volume_pinnedDistances_pos_of_absolutelyContinuous hμE
    (absolutelyContinuous_pinnedDistanceMeasure_of_frequently μ y hC hpos hto hfreq)



/-- The overlap integral is at most `2ε` times the mass of the pairs whose distances to the pin
differ by less than `2ε` — the "hyperbolic tube" around the pin. -/
theorem lintegral_overlap_le (μ : Measure Plane) [SFinite μ] (y : Plane) {ε : ℝ} :
    (∫⁻ q : Plane × Plane, ENNReal.ofReal (2 * ε - |dist q.1 y - dist q.2 y|) ∂(μ.prod μ))
      ≤ ENNReal.ofReal (2 * ε)
        * (μ.prod μ) {q : Plane × Plane | |dist q.1 y - dist q.2 y| < 2 * ε} := by
  set B : Set (Plane × Plane) := {q | |dist q.1 y - dist q.2 y| < 2 * ε} with hB
  have hBmeas : MeasurableSet B := by
    refine measurableSet_lt (continuous_abs.measurable.comp ?_) measurable_const
    exact ((measurable_dist_right y).comp measurable_fst).sub
      ((measurable_dist_right y).comp measurable_snd)
  have hpt : ∀ q : Plane × Plane, ENNReal.ofReal (2 * ε - |dist q.1 y - dist q.2 y|)
      ≤ B.indicator (fun _ => ENNReal.ofReal (2 * ε)) q := by
    intro q
    by_cases h : q ∈ B
    · rw [Set.indicator_of_mem h]
      exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg (dist q.1 y - dist q.2 y)])
    · rw [Set.indicator_of_notMem h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
      simp only [hB, Set.mem_setOf_eq, not_lt] at h
      linarith
  calc (∫⁻ q : Plane × Plane, ENNReal.ofReal (2 * ε - |dist q.1 y - dist q.2 y|) ∂(μ.prod μ))
      ≤ ∫⁻ q, B.indicator (fun _ => ENNReal.ofReal (2 * ε)) q ∂(μ.prod μ) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * ε) * (μ.prod μ) B := by
        rw [lintegral_indicator hBmeas, setLIntegral_const]

/-- **The `L²` criterion for the pinned distance set, in its sharpest elementary form.**  If the
`μ × μ`-mass of the pairs whose distances to `y` differ by less than `δ` is `O(δ)` along a
sequence of scales tending to zero, then every source set of positive mass has a pinned distance
set of positive length.

This is what the analytic branches have to supply.  The hyperbolic tube is where the radial
separation estimate of `RadialProjection.lean` enters: the gradient of `z ↦ |z - y|` is the
radial projection `Θ_y`, so the tube around a pair `(x, x')` is thin exactly when
`Θ_y x` and `Θ_y x'` are far apart, and `|det (x - y, x' - y)|` bounds that below. -/
theorem volume_pinnedDistances_pos_of_hyperbolic_bound
    (μ : Measure Plane) [IsFiniteMeasure μ] {E : Set Plane} (y : Plane) (hμE : 0 < μ E)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {ε : ℕ → ℝ} (hpos : ∀ n, 0 < ε n)
    (hto : Tendsto ε atTop (𝓝 0))
    (hfreq : ∃ᶠ n in atTop,
      (μ.prod μ) {q : Plane × Plane | |dist q.1 y - dist q.2 y| < 2 * ε n}
        ≤ ENNReal.ofReal (2 * ε n) * C) :
    0 < volume (pinnedDistances E y) := by
  refine volume_pinnedDistances_pos_of_frequently μ y hμE hC hpos hto (hfreq.mono fun n hn => ?_)
  refine le_trans (lintegral_overlap_le μ y) ?_
  calc ENNReal.ofReal (2 * ε n)
        * (μ.prod μ) {q : Plane × Plane | |dist q.1 y - dist q.2 y| < 2 * ε n}
      ≤ ENNReal.ofReal (2 * ε n) * (ENNReal.ofReal (2 * ε n) * C) := by gcongr
    _ = ENNReal.ofReal (4 * (ε n) ^ 2) * C := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith [hpos n] : (0:ℝ) ≤ 2 * ε n)]
        congr 2
        ring

end FalconerPacking
