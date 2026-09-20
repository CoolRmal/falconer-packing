/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Projection

/-!
# Square integrability of the projected densities

Section 2 of the manuscript works with the densities `F(θ) ∈ L²(ℝ)` of the projections
`(π_θ)_* λ`, and needs their joint second integrability in the angle.  Classically that comes
from the Fourier computation

  `∫ ‖π_θ μ‖₂² dθ ≍ ∫ |μ̂(ζ)|² |ζ|⁻¹ dζ ≍ I₁(μ)`,

which needs the Fourier transform of the Riesz kernel as a tempered distribution — theory that
Mathlib does not have.  This file gets the same conclusion by an elementary route.

The observation is that the `L²` norm of the `ε`-average of a measure on the line is an exact
overlap integral:

  `∫ σ(B(u, ε))² du = ∫∫ |B(x, ε) ∩ B(y, ε)| dσ dσ = ∫∫ (2ε - |x - y|)⁺ dσ dσ`,

and `(2ε - d)⁺ ≤ 4 ε² / d`, so the averages are bounded in `L²` by the Riesz `1`-energy,
uniformly in `ε` (`lintegral_sq_measure_interval_le`).

Applying this to a projection and integrating over the slope charts of `Tubes.lean` replaces the
`1`-energy of the *projected* measure — which is infinite, since the projection-energy
comparison of `Projection.lean` only converges for `s < 1` — by the `1`-energy of `μ` itself:
the inner integral `∫ (2ε - |⟪v, n_a⟫|)⁺ da` is bounded by `2ε` times the measure of the slopes
that nearly annihilate `v`, and the two-chart directional estimate gives that as `O(ε² / ‖v‖)`.
The result is `lintegral_chart_sq_measure_interval_le`:

  `∫ ‖(π_a μ)_ε‖₂² da ≤ 16 I₁(μ)`, uniformly in `ε`.

No Fourier transform appears anywhere.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The points within `ε` of both `x` and `y` form an interval, of length `2ε - |x - y|`. -/
theorem volume_setOf_dist_le_both (x y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    volume {u : ℝ | |u - x| ≤ ε ∧ |u - y| ≤ ε} = ENNReal.ofReal (2 * ε - |x - y|) := by
  have hset : {u : ℝ | |u - x| ≤ ε ∧ |u - y| ≤ ε}
      = Set.Icc (x - ε) (x + ε) ∩ Set.Icc (y - ε) (y + ε) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [hset, Set.Icc_inter_Icc, Real.volume_Icc]
  congr 1
  rcases le_total x y with h | h
  · rw [inf_eq_left.2 (by linarith : x + ε ≤ y + ε),
      sup_eq_right.2 (by linarith : x - ε ≤ y - ε),
      abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    ring
  · rw [inf_eq_right.2 (by linarith : y + ε ≤ x + ε),
      sup_eq_left.2 (by linarith : y - ε ≤ x - ε),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    ring

/-- **The overlap estimate.**  The interval of points within `ε` of both `x` and `y` is short
when `x` and `y` are far apart, and the reciprocal-separation bound holds uniformly in `ε`.
This is what makes the `ε`-averages of a measure of finite `1`-energy bounded in `L²`. -/
theorem volume_setOf_dist_le_both_le (x y : ℝ) {ε : ℝ} (hε : 0 < ε) :
    volume {u : ℝ | |u - x| ≤ ε ∧ |u - y| ≤ ε}
      ≤ ENNReal.ofReal (4 * ε ^ 2) / ENNReal.ofReal |x - y| := by
  rw [volume_setOf_dist_le_both x y hε]
  rcases eq_or_ne x y with rfl | hxy
  · have : ENNReal.ofReal (4 * ε ^ 2) / ENNReal.ofReal |x - x| = ⊤ := by
      rw [sub_self, abs_zero, ENNReal.ofReal_zero, ENNReal.div_zero
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)]
    rw [this]; exact le_top
  · have hd : (0 : ℝ) < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
    rw [← ENNReal.ofReal_div_of_pos hd]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hd]
    nlinarith [sq_nonneg (|x - y| - ε)]


/-- **Finite `1`-energy bounds the `ε`-averages in `L²`, uniformly in `ε`.**

For a measure on the line, the square of the mass of the `ε`-interval around `u`, integrated in
`u`, is at most `4 ε²` times the Riesz `1`-energy.  Dividing by `(2ε)²`, the normalized averages
`σ(B(u, ε)) / 2ε` are bounded in `L²` by the energy, with no dependence on `ε`.

This is the elementary substitute for the Fourier characterization `I₁(σ) ≍ ∫ |σ̂|²`: it gives
the `L²` bound that Section 2 of the manuscript needs for the projected densities, with no
Fourier transform and no Riesz-kernel distribution theory. -/
theorem lintegral_sq_measure_interval_eq (σ : Measure ℝ) [SFinite σ] {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ u : ℝ, (σ {x : ℝ | |u - x| ≤ ε}) ^ 2
      = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (2 * ε - |p.1 - p.2|) ∂(σ.prod σ) := by
  set S : Set (ℝ × (ℝ × ℝ)) := {z | |z.1 - z.2.1| ≤ ε ∧ |z.1 - z.2.2| ≤ ε} with hS
  have hSmeas : MeasurableSet S := by
    have h1 : MeasurableSet {z : ℝ × (ℝ × ℝ) | |z.1 - z.2.1| ≤ ε} :=
      measurableSet_le (continuous_abs.measurable.comp
        (measurable_fst.sub (measurable_fst.comp measurable_snd))) measurable_const
    have h2 : MeasurableSet {z : ℝ × (ℝ × ℝ) | |z.1 - z.2.2| ≤ ε} :=
      measurableSet_le (continuous_abs.measurable.comp
        (measurable_fst.sub (measurable_snd.comp measurable_snd))) measurable_const
    exact h1.inter h2
  have hsec : ∀ u : ℝ, (σ {x : ℝ | |u - x| ≤ ε}) ^ 2 = (σ.prod σ) (Prod.mk u ⁻¹' S) := by
    intro u
    have : Prod.mk u ⁻¹' S = {x : ℝ | |u - x| ≤ ε} ×ˢ {x : ℝ | |u - x| ≤ ε} := rfl
    rw [this, Measure.prod_prod, sq]
  calc ∫⁻ u : ℝ, (σ {x : ℝ | |u - x| ≤ ε}) ^ 2
      = ∫⁻ u : ℝ, ∫⁻ p : ℝ × ℝ, S.indicator 1 (u, p) ∂(σ.prod σ) := by
        refine lintegral_congr fun u => ?_
        rw [hsec u, ← lintegral_indicator_one (measurable_prodMk_left hSmeas)]
        rfl
    _ = ∫⁻ p : ℝ × ℝ, (∫⁻ u : ℝ, S.indicator 1 (u, p)) ∂(σ.prod σ) :=
        lintegral_lintegral_swap (measurable_const.indicator hSmeas).aemeasurable
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (2 * ε - |p.1 - p.2|) ∂(σ.prod σ) := by
        refine lintegral_congr fun p => ?_
        have hmp : MeasurableSet ((fun x : ℝ => (x, p)) ⁻¹' S) := measurable_prodMk_right hSmeas
        show ∫⁻ u : ℝ, S.indicator (1 : ℝ × (ℝ × ℝ) → ℝ≥0∞) (u, p) = _
        rw [show (fun u : ℝ => S.indicator (1 : ℝ × (ℝ × ℝ) → ℝ≥0∞) (u, p))
            = ((fun x : ℝ => (x, p)) ⁻¹' S).indicator 1 from rfl,
          lintegral_indicator_one hmp]
        exact volume_setOf_dist_le_both p.1 p.2 hε


/-- The uniform `L²` bound follows from the exact identity and the overlap estimate. -/
theorem lintegral_sq_measure_interval_le (σ : Measure ℝ) [SFinite σ] {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ u : ℝ, (σ {x : ℝ | |u - x| ≤ ε}) ^ 2
      ≤ ENNReal.ofReal (4 * ε ^ 2) * energyLine σ 1 := by
  have hker : Measurable fun q : ℝ × ℝ => (ENNReal.ofReal |q.1 - q.2|) ^ (-(1 : ℝ)) :=
    (ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp (measurable_fst.sub measurable_snd))).pow_const _
  rw [lintegral_sq_measure_interval_eq σ hε]
  calc ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (2 * ε - |p.1 - p.2|) ∂(σ.prod σ)
      ≤ ∫⁻ p : ℝ × ℝ,
          ENNReal.ofReal (4 * ε ^ 2) * (ENNReal.ofReal |p.1 - p.2|) ^ (-(1 : ℝ))
            ∂(σ.prod σ) := by
        refine lintegral_mono fun p => ?_
        rw [ENNReal.rpow_neg_one, ← div_eq_mul_inv, ← volume_setOf_dist_le_both p.1 p.2 hε]
        exact volume_setOf_dist_le_both_le p.1 p.2 hε
    _ = ENNReal.ofReal (4 * ε ^ 2) * energyLine σ 1 := by
        rw [lintegral_const_mul _ hker, energyLine, lintegral_prod _ hker.aemeasurable]


/-- The projection onto the line with normal `n`, as a function of the normal. -/
def projNormal (n x : Plane) : ℝ := ⟪x, n⟫

/-- The projected measure, as a function of the normal. -/
def projMeasureN (μ : Measure Plane) (n : Plane) : Measure ℝ := Measure.map (projNormal n) μ

theorem measurable_projNormal (n : Plane) : Measurable (projNormal n) := by
  have : projNormal n = fun x : Plane => x 0 * n 0 + x 1 * n 1 := by
    funext x; exact inner_plane x n
  rw [this]
  exact ((measurable_coord 0).mul measurable_const).add
    ((measurable_coord 1).mul measurable_const)

instance instSFiniteProjMeasureN (μ : Measure Plane) [SFinite μ] (n : Plane) :
    SFinite (projMeasureN μ n) := by
  rw [projMeasureN]; infer_instance

theorem projMeasure_eq (μ : Measure Plane) (a : ℝ) :
    projMeasure μ a = projMeasureN μ (normalSlope a) := rfl

/-- Change of variables: a kernel of the difference, integrated against the projected measure
squared, is the same kernel of the projected difference integrated against `μ` squared. -/
theorem lintegral_prod_projMeasureN (μ : Measure Plane) [SFinite μ] (n : Plane)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p : ℝ × ℝ, f (p.1 - p.2) ∂((projMeasureN μ n).prod (projMeasureN μ n))
      = ∫⁻ q : Plane × Plane, f ⟪q.1 - q.2, n⟫ ∂(μ.prod μ) := by
  have hm := measurable_projNormal n
  have hfd : Measurable fun p : ℝ × ℝ => f (p.1 - p.2) :=
    hf.comp (measurable_fst.sub measurable_snd)
  calc ∫⁻ p : ℝ × ℝ, f (p.1 - p.2) ∂((projMeasureN μ n).prod (projMeasureN μ n))
      = ∫⁻ u, ∫⁻ v, f (u - v) ∂(Measure.map (projNormal n) μ)
          ∂(Measure.map (projNormal n) μ) := lintegral_prod _ hfd.aemeasurable
    _ = ∫⁻ x, ∫⁻ y, f (projNormal n x - projNormal n y) ∂μ ∂μ := by
        have hOuter : Measurable fun u : ℝ => ∫⁻ v, f (u - v) ∂(Measure.map (projNormal n) μ) :=
          hfd.lintegral_prod_right'
        rw [lintegral_map hOuter hm]
        exact lintegral_congr fun x => lintegral_map (hf.comp (measurable_const.sub measurable_id)) hm
    _ = ∫⁻ q : Plane × Plane, f ⟪q.1 - q.2, n⟫ ∂(μ.prod μ) := by
        rw [lintegral_prod]
        · refine (lintegral_congr fun x => lintegral_congr fun y => ?_).symm
          rw [inner_sub_left]
          rfl
        · exact (hf.comp ((measurable_projNormal n).comp
            (measurable_fst.sub measurable_snd))).aemeasurable



theorem measurable_ofReal_overlap {ε : ℝ} :
    Measurable fun t : ℝ => ENNReal.ofReal (2 * ε - |t|) :=
  ENNReal.measurable_ofReal.comp (measurable_const.sub continuous_abs.measurable)

theorem chart_swap (μ : Measure Plane) [SFinite μ] {ε : ℝ} (hε : 0 < ε) (e : ℝ → Plane)
    (hg : Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, e z.1⟫) :
    (∫⁻ a in Set.Icc (-1 : ℝ) 1, (∫⁻ u : ℝ,
        ((projMeasureN μ (e a)) {x : ℝ | |u - x| ≤ ε}) ^ 2))
      = ∫⁻ q : Plane × Plane, (∫⁻ a in Set.Icc (-1 : ℝ) 1,
          ENNReal.ofReal (2 * ε - |⟪q.1 - q.2, e a⟫|)) ∂(μ.prod μ) := by
  have hstep : ∀ a : ℝ, (∫⁻ u : ℝ, ((projMeasureN μ (e a)) {x : ℝ | |u - x| ≤ ε}) ^ 2)
      = ∫⁻ q : Plane × Plane, ENNReal.ofReal (2 * ε - |⟪q.1 - q.2, e a⟫|) ∂(μ.prod μ) := by
    intro a
    rw [lintegral_sq_measure_interval_eq _ hε,
      lintegral_prod_projMeasureN μ (e a) measurable_ofReal_overlap]
  rw [lintegral_congr hstep]
  exact lintegral_lintegral_swap
    ((measurable_ofReal_overlap.comp hg).aemeasurable)

/-- The overlap kernel integrates over a chart to at most `2ε` times the measure of the slopes
that nearly annihilate the displacement. -/
theorem lintegral_chart_overlap_le (v : Plane) {ε : ℝ} (e : ℝ → Plane)
    (hme : Measurable fun a : ℝ => ⟪v, e a⟫) :
    (∫⁻ a in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (2 * ε - |⟪v, e a⟫|))
      ≤ ENNReal.ofReal (2 * ε) * volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, e a⟫| < 2 * ε} := by
  set B : Set ℝ := {a : ℝ | |⟪v, e a⟫| < 2 * ε} with hB
  have hBmeas : MeasurableSet B :=
    measurableSet_lt (continuous_abs.measurable.comp hme) measurable_const
  have hpt : ∀ a : ℝ, ENNReal.ofReal (2 * ε - |⟪v, e a⟫|)
      ≤ B.indicator (fun _ => ENNReal.ofReal (2 * ε)) a := by
    intro a
    by_cases h : a ∈ B
    · rw [Set.indicator_of_mem h]
      exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg ⟪v, e a⟫])
    · rw [Set.indicator_of_notMem h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
      simp only [hB, Set.mem_setOf_eq, not_lt] at h
      linarith
  calc (∫⁻ a in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (2 * ε - |⟪v, e a⟫|))
      ≤ ∫⁻ a in Set.Icc (-1 : ℝ) 1, B.indicator (fun _ => ENNReal.ofReal (2 * ε)) a :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 * ε) * (volume.restrict (Set.Icc (-1 : ℝ) 1)) B := by
        rw [lintegral_indicator hBmeas, setLIntegral_const]
    _ = ENNReal.ofReal (2 * ε) * volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, e a⟫| < 2 * ε} := by
        rw [Measure.restrict_apply hBmeas]
        congr 2
        ext a
        simp only [Set.mem_inter_iff, hB, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        tauto



theorem measurable_inner_fixed (v : Plane) (e : ℝ → Plane)
    (hg : Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, e z.1⟫) :
    Measurable fun a : ℝ => ⟪v, e a⟫ := by
  have h := hg.comp (measurable_id.prodMk (measurable_const : Measurable
    fun _ : ℝ => ((v : Plane), (0 : Plane))))
  simpa [Function.comp_def, sub_zero] using h

/-- **The projected densities are square integrable on average.**  For a planar measure of finite
Riesz `1`-energy, the `ε`-averages of its projections are bounded in `L²` uniformly in `ε`, after
averaging over the two slope charts.

Dividing by `(2ε)²`, this says `∫ ‖(π_a μ)_ε‖₂² da ≤ 16 I₁(μ)`, with no dependence on `ε`.  It
is the elementary form of the classical Fourier computation
`∫ ‖π_θ μ‖₂² dθ ≍ ∫ |μ̂(ζ)|² |ζ|⁻¹ dζ ≍ I₁(μ)`, and it is what Section 2 of the manuscript needs
to speak of the projected densities `F(θ) ∈ L²(ℝ)`.  No Fourier transform is used. -/
theorem lintegral_chart_sq_measure_interval_le (μ : Measure Plane) [SFinite μ] {ε : ℝ}
    (hε : 0 < ε) :
    (∫⁻ a in Set.Icc (-1 : ℝ) 1, (∫⁻ u : ℝ,
        ((projMeasureN μ (normalSlope a)) {x : ℝ | |u - x| ≤ ε}) ^ 2))
      + (∫⁻ a in Set.Icc (-1 : ℝ) 1, (∫⁻ u : ℝ,
        ((projMeasureN μ (normalSlopeT a)) {x : ℝ | |u - x| ≤ ε}) ^ 2))
      ≤ ENNReal.ofReal (64 * ε ^ 2) * rieszEnergy μ 1 := by
  rw [chart_swap μ hε normalSlope measurable_inner_normalSlope,
    chart_swap μ hε normalSlopeT measurable_inner_normalSlopeT,
    ← lintegral_add_left _]
  · calc ∫⁻ q : Plane × Plane,
          ((∫⁻ a in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (2 * ε - |⟪q.1 - q.2, normalSlope a⟫|))
            + ∫⁻ a in Set.Icc (-1 : ℝ) 1,
                ENNReal.ofReal (2 * ε - |⟪q.1 - q.2, normalSlopeT a⟫|)) ∂(μ.prod μ)
        ≤ ∫⁻ q : Plane × Plane,
            ENNReal.ofReal (64 * ε ^ 2) / ENNReal.ofReal ‖q.1 - q.2‖ ∂(μ.prod μ) := by
          refine lintegral_mono fun q => ?_
          set v : Plane := q.1 - q.2 with hv
          have h1 := lintegral_chart_overlap_le v (ε := ε) normalSlope
            (measurable_inner_fixed v _ measurable_inner_normalSlope)
          have h2 := lintegral_chart_overlap_le v (ε := ε) normalSlopeT
            (measurable_inner_fixed v _ measurable_inner_normalSlopeT)
          have hsum := volume_chart_add_chartT_le_uniform v (δ := 2 * ε) (by linarith)
          calc (∫⁻ a in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (2 * ε - |⟪v, normalSlope a⟫|))
                + ∫⁻ a in Set.Icc (-1 : ℝ) 1, ENNReal.ofReal (2 * ε - |⟪v, normalSlopeT a⟫|)
              ≤ ENNReal.ofReal (2 * ε) * volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlope a⟫| < 2 * ε}
                  + ENNReal.ofReal (2 * ε)
                    * volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlopeT a⟫| < 2 * ε} :=
                add_le_add h1 h2
            _ = ENNReal.ofReal (2 * ε)
                  * (volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlope a⟫| < 2 * ε}
                    + volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlopeT a⟫| < 2 * ε}) := by ring
            _ ≤ ENNReal.ofReal (2 * ε)
                  * (ENNReal.ofReal (16 * (2 * ε)) / ENNReal.ofReal ‖v‖) := by gcongr
            _ = ENNReal.ofReal (64 * ε ^ 2) / ENNReal.ofReal ‖v‖ := by
                rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc,
                  ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * ε),
                  show (2 : ℝ) * ε * (16 * (2 * ε)) = 64 * ε ^ 2 from by ring]
      _ = ENNReal.ofReal (64 * ε ^ 2) * rieszEnergy μ 1 :=
          lintegral_prod_inv_norm_sub μ (64 * ε ^ 2)
  · exact Measurable.lintegral_prod_left' (μ := volume.restrict (Set.Icc (-1 : ℝ) 1))
      (measurable_ofReal_overlap.comp measurable_inner_normalSlope)

end FalconerPacking
