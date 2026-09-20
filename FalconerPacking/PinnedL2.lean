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

/-! ### Averaging over the pin

The criterion above is stated at a fixed pin, and the analytic branches supply information about
the hyperbolic tubes only on average over a pin measure.  Fatou bridges the two: an average
bound at every scale gives a finite lower limit at almost every pin, hence the frequent bound
the criterion needs.

The conclusion, `exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube`, has exactly the
shape of both analytic branches of Theorem 1.1.  Everything after the averaged tube bound is
therefore supplied here, unconditionally.
-/

/-- The hyperbolic tube around a pin, as a set of pairs. -/
def hypTube (y : Plane) (δ : ℝ) : Set (Plane × Plane) :=
  {q | |dist q.1 y - dist q.2 y| < δ}

theorem measurableSet_hypTube_prod (δ : ℝ) :
    MeasurableSet {z : Plane × (Plane × Plane) | |dist z.2.1 z.1 - dist z.2.2 z.1| < δ} := by
  refine measurableSet_lt (continuous_abs.measurable.comp ?_) measurable_const
  have h1 : Measurable fun z : Plane × (Plane × Plane) => dist z.2.1 z.1 :=
    (continuous_dist.comp ((continuous_fst.comp continuous_snd).prodMk continuous_fst)).measurable
  have h2 : Measurable fun z : Plane × (Plane × Plane) => dist z.2.2 z.1 :=
    (continuous_dist.comp ((continuous_snd.comp continuous_snd).prodMk continuous_fst)).measurable
  exact h1.sub h2

theorem measurable_measure_hypTube (μ : Measure Plane) [SFinite μ] (δ : ℝ) :
    Measurable fun y : Plane => (μ.prod μ) (hypTube y δ) :=
  measurable_measure_prodMk_left (measurableSet_hypTube_prod δ)



/-- **A pin from an averaged hyperbolic-tube bound.**  Suppose the mass of the hyperbolic tube
around the pin, averaged over a pin measure `ν`, is `O(δ)` at a sequence of scales tending to
zero.  Then `ν`-almost every pin has a positive-length pinned distance set, so a pin can be
chosen in any full-measure set for `ν`.

This is the shape of both analytic branches of Theorem 1.1: everything after the averaged tube
bound — Fatou to pass from an average at every scale to a frequent bound at almost every pin,
then the `L²` criterion at that pin — is supplied here, unconditionally. -/
theorem exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube
    (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {E F : Set Plane} (hμE : 0 < μ E) (hνF : ν Fᶜ = 0) (hν : 0 < ν univ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) {δ : ℕ → ℝ} (hpos : ∀ n, 0 < δ n)
    (hto : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n, (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ n)) ∂ν)
      ≤ ENNReal.ofReal (2 * δ n) * C) :
    ∃ y ∈ F, 0 < volume (pinnedDistances E y) := by
  set G : ℕ → Plane → ℝ≥0∞ := fun n y =>
    (μ.prod μ) (hypTube y (2 * δ n)) / ENNReal.ofReal (2 * δ n) with hG
  have hcne : ∀ n, ENNReal.ofReal (2 * δ n) ≠ 0 := by
    intro n
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith [hpos n]
  have hGmeas : ∀ n, Measurable (G n) := fun n =>
    (measurable_measure_hypTube μ (2 * δ n)).div_const _
  have hGbound : ∀ n, (∫⁻ y, G n y ∂ν) ≤ C := by
    intro n
    calc (∫⁻ y, G n y ∂ν)
        = (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ n)) ∂ν) / ENNReal.ofReal (2 * δ n) := by
          simp only [hG, div_eq_mul_inv]
          exact lintegral_mul_const _ (measurable_measure_hypTube μ (2 * δ n))
      _ ≤ (ENNReal.ofReal (2 * δ n) * C) / ENNReal.ofReal (2 * δ n) := by gcongr; exact hbound n
      _ = C := by
          rw [mul_comm, ENNReal.mul_div_cancel_right (hcne n) ENNReal.ofReal_ne_top]
  have hfatou : (∫⁻ y, liminf (fun n => G n y) atTop ∂ν) ≤ C :=
    le_trans (lintegral_liminf_le hGmeas)
      (liminf_le_of_frequently_le (Filter.Frequently.of_forall hGbound))
  have hae := ae_lt_top (Measurable.liminf hGmeas) (ne_top_of_le_ne_top hC hfatou)
  have hgood : ∀ᵐ y ∂ν, 0 < volume (pinnedDistances E y) := by
    filter_upwards [hae] with y hy
    obtain ⟨M, hM1, hM2⟩ : ∃ M : ℝ≥0∞, liminf (fun n => G n y) atTop < M ∧ M ≠ ⊤ :=
      ⟨liminf (fun n => G n y) atTop + 1, ENNReal.lt_add_right hy.ne one_ne_zero,
        ENNReal.add_ne_top.2 ⟨hy.ne, ENNReal.one_ne_top⟩⟩
    have hfreq : ∃ᶠ n in atTop, G n y < M := frequently_lt_of_liminf_lt (by isBoundedDefault) hM1
    refine volume_pinnedDistances_pos_of_hyperbolic_bound μ y hμE hM2 hpos hto
      (hfreq.mono fun n hn => ?_)
    have hlt : (μ.prod μ) (hypTube y (2 * δ n)) < M * ENNReal.ofReal (2 * δ n) :=
      (ENNReal.div_lt_iff (Or.inl (hcne n)) (Or.inl ENNReal.ofReal_ne_top)).1 hn
    rw [mul_comm M] at hlt
    exact le_of_lt hlt
  -- a full-measure set for `ν` meets `F`
  by_contra hcon
  push_neg at hcon
  have hsub : F ⊆ {y | ¬ (0 < volume (pinnedDistances E y))} := by
    intro y hy
    simpa using (hcon y hy)
  have hnull : ν {y | ¬ (0 < volume (pinnedDistances E y))} = 0 := hgood
  have hF0 : ν F = 0 := measure_mono_null hsub hnull
  have hFpos : 0 < ν F := by
    have h1 : ν univ ≤ ν F + ν Fᶜ := by
      rw [← Set.union_compl_self F]
      exact measure_union_le _ _
    rw [hνF, add_zero] at h1
    exact lt_of_lt_of_le hν h1
  exact absurd hF0 hFpos.ne'

/-! ### The dictionary with radial projections

Seen from a pin, the separation of two source points splits exactly into a radial part and an
angular part, and the split is an identity rather than an estimate:

  `‖x - x'‖² = (‖x - y‖ - ‖x' - y‖)² + ‖x - y‖ ‖x' - y‖ · |Θ_y x - Θ_y x'|²`.

The hyperbolic tube constrains the radial part, so membership in a thin tube forces the radial
projections apart.  That is the precise sense in which the tube bound is a statement about
radial projections, and hence the point at which Orponen's theorem is what is needed.
-/

/-- **The pinned-distance identity.**  Seen from a pin `y`, the separation of two source points
splits exactly into a radial part and an angular part:

`‖x - x'‖² = (‖x - y‖ - ‖x' - y‖)² + ‖x - y‖ ‖x' - y‖ · |Θ_y x - Θ_y x'|²`.

The radial part is the quantity the hyperbolic tube constrains, and the angular part is the
radial-projection separation.  The identity is exact, and it is the dictionary between the two:
a thin hyperbolic tube forces the radial projections apart, and conversely. -/
theorem norm_sub_sq_eq_radial_add_angular {x x' y : Plane} (hx : x ≠ y) (hx' : x' ≠ y) :
    ‖x - x'‖ ^ 2
      = (‖x - y‖ - ‖x' - y‖) ^ 2
        + ‖x - y‖ * ‖x' - y‖ * dist (radialProj y x) (radialProj y x') ^ 2 := by
  have hu : (0 : ℝ) < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hx)
  have hu' : (0 : ℝ) < ‖x' - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hx')
  have hsub : x - x' = (x - y) - (x' - y) := by abel
  have hnorm : ‖x - x'‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * ⟪x - y, x' - y⟫ + ‖x' - y‖ ^ 2 := by
    rw [hsub, ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    simp only [real_inner_self_eq_norm_sq, real_inner_comm (x - y) (x' - y)]
    ring
  have hdist : dist (radialProj y x) (radialProj y x') ^ 2
      = 2 - 2 * (⟪x - y, x' - y⟫ / (‖x - y‖ * ‖x' - y‖)) := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
    have h1 : ⟪radialProj y x, radialProj y x⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_radialProj y hx]; norm_num
    have h2 : ⟪radialProj y x', radialProj y x'⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_radialProj y hx']; norm_num
    have h3 : ⟪radialProj y x, radialProj y x'⟫
        = ⟪x - y, x' - y⟫ / (‖x - y‖ * ‖x' - y‖) := by
      rw [radialProj, radialProj, real_inner_smul_left, real_inner_smul_right]
      field_simp
    have h3' : ⟪radialProj y x', radialProj y x⟫
        = ⟪x - y, x' - y⟫ / (‖x - y‖ * ‖x' - y‖) := by
      rw [real_inner_comm]; exact h3
    rw [h1, h2, h3, h3']
    ring
  rw [hnorm, hdist]
  field_simp
  ring



/-- **A thin hyperbolic tube forces the radial projections apart.**  If the distances from `y`
to `x` and to `x'` differ by less than `δ`, and both source points lie within `R` of the pin,
then the radial projections are separated by at least `(‖x - x'‖² - δ²)^{1/2} / R`.

This is the exact sense in which the hyperbolic tube of `PinnedL2.lean` is a statement about
radial projections, and hence the point at which Orponen's theorem is what is needed. -/
theorem dist_radialProj_sq_ge_of_mem_hypTube {x x' y : Plane} (hx : x ≠ y) (hx' : x' ≠ y)
    {δ R : ℝ} (hxR : ‖x - y‖ ≤ R) (hx'R : ‖x' - y‖ ≤ R)
    (hmem : |dist x y - dist x' y| < δ) :
    ‖x - x'‖ ^ 2 - δ ^ 2 ≤ R ^ 2 * dist (radialProj y x) (radialProj y x') ^ 2 := by
  have hid := norm_sub_sq_eq_radial_add_angular hx hx'
  rw [dist_eq_norm, dist_eq_norm] at hmem
  have hrad : (‖x - y‖ - ‖x' - y‖) ^ 2 < δ ^ 2 := by
    have h0 : (0 : ℝ) ≤ |‖x - y‖ - ‖x' - y‖| := abs_nonneg _
    nlinarith [sq_abs (‖x - y‖ - ‖x' - y‖)]
  have hprod : ‖x - y‖ * ‖x' - y‖ ≤ R ^ 2 := by
    nlinarith [norm_nonneg (x - y), norm_nonneg (x' - y)]
  nlinarith [dist_nonneg (x := radialProj y x) (y := radialProj y x'),
    sq_nonneg (dist (radialProj y x) (radialProj y x'))]

end FalconerPacking
