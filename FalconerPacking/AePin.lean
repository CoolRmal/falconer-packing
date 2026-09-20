/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Reduction

/-!
# The almost-every-pin problem

Theorem 1.1 asks for a pin *inside* the set, and that is what needs Orponen's radial-projection
theorem.  The almost-every-pin problem — a pin somewhere in a ball — is far shallower, and this
file shows exactly how much shallower: it reduces to a statement of plane geometry about the
area of a hyperbolic strip, with no harmonic analysis at all.

`StripAreaBound R` says that inside a ball of radius `R`, the pins whose distances to `x` and to
`x'` differ by less than `δ` occupy area `O(δ / ‖x - x'‖)`.  The strip is a neighbourhood of a
hyperbola branch; its width is `δ / |Θ_y x - Θ_y x'|`, and the exact identity
`norm_sub_sq_eq_radial_add_angular` of `PinnedL2.lean` bounds that gradient below by
`‖x - x'‖ / R` on the strip, so the bound is what one expects.  Turning that into an area
statement needs a change of variables or a co-area inequality, neither of which is available
here, so it is recorded as a hypothesis rather than proved.

Given it, `exists_pin_ball_of_stripAreaBound` produces a pin in the ball for any source of
finite Riesz `1`-energy — in particular for any Frostman exponent above one.  The `1`-energy is
exactly where the `δ / ‖x - x'‖` of the strip bound is consumed:

  `∫∫ δ / ‖x - x'‖ dμ dμ = δ · I₁(μ)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- **The hyperbolic strip area bound**, as a named hypothesis: inside a fixed ball, the set of
pins whose distances to `x` and to `x'` differ by less than `δ` has area `O(δ / ‖x - x'‖)`.

This is a statement of plane geometry, not of harmonic analysis: the strip is a neighbourhood of
a hyperbola branch, its width is `δ / |Θ_y x - Θ_y x'|`, and the exact identity
`norm_sub_sq_eq_radial_add_angular` bounds that gradient below by `‖x - x'‖ / R` on the strip.
Turning that into an area bound needs a change of variables or a co-area inequality, neither of
which is available here, so it is recorded as a hypothesis.

`ENNReal` division makes the bound vacuous on the diagonal, where it must be. -/
def StripAreaBound (R : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (x x' : Plane) (δ : ℝ), 0 < δ →
    volume {y : Plane | ‖y‖ ≤ R ∧ |dist x y - dist x' y| < δ}
      ≤ ENNReal.ofReal (C * δ) / ENNReal.ofReal ‖x - x'‖

theorem measurableSet_strip (x x' : Plane) (R δ : ℝ) :
    MeasurableSet {y : Plane | ‖y‖ ≤ R ∧ |dist x y - dist x' y| < δ} := by
  refine MeasurableSet.inter (measurableSet_le continuous_norm.measurable measurable_const) ?_
  exact measurableSet_lt (continuous_abs.measurable.comp
    (((continuous_const.dist continuous_id).measurable).sub
      ((continuous_const.dist continuous_id).measurable))) measurable_const

/-- Tonelli for the strip: the average of the hyperbolic-tube mass over the pins of a ball is
the average of the strip areas over the source pairs. -/
theorem lintegral_hypTube_restrict (μ : Measure Plane) [SFinite μ] (R : ℝ) {δ : ℝ} :
    (∫⁻ y in {y : Plane | ‖y‖ ≤ R}, (μ.prod μ) (hypTube y δ))
      = ∫⁻ q : Plane × Plane,
          volume {y : Plane | ‖y‖ ≤ R ∧ |dist q.1 y - dist q.2 y| < δ} ∂(μ.prod μ) := by
  set S : Set (Plane × (Plane × Plane)) :=
    {z | |dist z.2.1 z.1 - dist z.2.2 z.1| < δ} with hS
  have hSmeas : MeasurableSet S := measurableSet_hypTube_prod δ
  set B : Set Plane := {y : Plane | ‖y‖ ≤ R} with hB
  have hBmeas : MeasurableSet B := measurableSet_le continuous_norm.measurable measurable_const
  calc (∫⁻ y in B, (μ.prod μ) (hypTube y δ))
      = ∫⁻ y, (∫⁻ q : Plane × Plane, S.indicator 1 (y, q) ∂(μ.prod μ))
          ∂(volume.restrict B) := by
        refine lintegral_congr fun y => ?_
        have hEq : hypTube y δ = Prod.mk y ⁻¹' S := rfl
        rw [hEq, ← lintegral_indicator_one (measurable_prodMk_left hSmeas)]
        rfl
    _ = ∫⁻ q : Plane × Plane, (∫⁻ y, S.indicator 1 (y, q) ∂(volume.restrict B))
          ∂(μ.prod μ) :=
        lintegral_lintegral_swap (measurable_const.indicator hSmeas).aemeasurable
    _ = ∫⁻ q : Plane × Plane,
          volume {y : Plane | ‖y‖ ≤ R ∧ |dist q.1 y - dist q.2 y| < δ} ∂(μ.prod μ) := by
        refine lintegral_congr fun q => ?_
        have hmp : MeasurableSet ((fun y : Plane => (y, q)) ⁻¹' S) :=
          measurable_prodMk_right hSmeas
        rw [show (fun y : Plane => S.indicator (1 : Plane × (Plane × Plane) → ℝ≥0∞) (y, q))
            = ((fun y : Plane => (y, q)) ⁻¹' S).indicator 1 from rfl,
          lintegral_indicator_one hmp, Measure.restrict_apply hmp]
        congr 1
        ext y
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hB, hS]
        tauto



/-- **An almost-every-pin theorem, from the strip area bound alone.**  If a probability measure
on the plane has finite Riesz `1`-energy — which a Frostman exponent above one supplies — then
the strip area bound produces a pin in any ball whose pinned distance set has positive length.

The point is how shallow the remaining hypothesis is.  The pin-inside-the-set problem of Theorem
1.1 needs Orponen's radial-projection theorem; the almost-every-pin problem needs only a
statement of plane geometry about the area of a hyperbolic strip. -/
theorem exists_pin_ball_of_stripAreaBound (μ : Measure Plane) [IsProbabilityMeasure μ]
    {E : Set Plane} (hμE : 0 < μ E) {R : ℝ} (hR : 0 < R)
    (hstrip : StripAreaBound R) (hen : rieszEnergy μ 1 ≠ ⊤) :
    ∃ y, ‖y‖ ≤ R ∧ 0 < volume (pinnedDistances E y) := by
  obtain ⟨C, hC, hSA⟩ := hstrip
  set B : Set Plane := {y : Plane | ‖y‖ ≤ R} with hB
  have hBeq : B = Metric.closedBall (0 : Plane) R := by
    ext y; simp [hB, Metric.mem_closedBall, dist_eq_norm]
  have hBmeas : MeasurableSet B := measurableSet_le continuous_norm.measurable measurable_const
  have hBpos : 0 < volume B := by
    rw [hBeq]; exact Metric.measure_closedBall_pos _ _ hR
  have hBtop : volume B ≠ ⊤ := by
    rw [hBeq]; exact (Metric.isBounded_closedBall.measure_lt_top).ne
  set ν : Measure Plane := normalizedRestrict volume B with hν
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_normalizedRestrict hBmeas hBpos.ne' hBtop
  have hνc : ν Bᶜ = 0 := normalizedRestrict_compl_eq_zero volume hBmeas
  set Cb : ℝ≥0∞ := (volume B)⁻¹ * ENNReal.ofReal C * rieszEnergy μ 1 with hCb
  have hCbtop : Cb ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hBpos.ne') ENNReal.ofReal_ne_top)
      hen
  have hkey : ∀ δ : ℝ, 0 < δ →
      (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ)) ∂ν) ≤ ENNReal.ofReal (2 * δ) * Cb := by
    intro δ hδ
    calc (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ)) ∂ν)
        = (volume B)⁻¹ * ∫⁻ y in B, (μ.prod μ) (hypTube y (2 * δ)) := by
          rw [hν, normalizedRestrict, lintegral_smul_measure]
          rfl
      _ = (volume B)⁻¹ * ∫⁻ q : Plane × Plane,
            volume {y : Plane | ‖y‖ ≤ R ∧ |dist q.1 y - dist q.2 y| < 2 * δ} ∂(μ.prod μ) := by
          rw [lintegral_hypTube_restrict μ R]
      _ ≤ (volume B)⁻¹ * ∫⁻ q : Plane × Plane,
            ENNReal.ofReal (C * (2 * δ)) / ENNReal.ofReal ‖q.1 - q.2‖ ∂(μ.prod μ) := by
          gcongr with q
          exact hSA q.1 q.2 (2 * δ) (by linarith)
      _ = (volume B)⁻¹ * (ENNReal.ofReal (C * (2 * δ)) * rieszEnergy μ 1) := by
          rw [lintegral_prod_inv_norm_sub μ (C * (2 * δ))]
      _ = ENNReal.ofReal (2 * δ) * Cb := by
          rw [hCb, ENNReal.ofReal_mul hC.le]
          ring
  obtain ⟨y, hyB, hy⟩ := exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube μ ν
    hμE hνc (by rw [measure_univ]; norm_num) hCbtop
    (fun n : ℕ => (by positivity : (0:ℝ) < 1 / (n + 1)))
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => hkey _ (by positivity))
  exact ⟨y, hyB, hy⟩

end FalconerPacking
