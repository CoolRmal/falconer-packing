/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AePin

/-!
# The remaining hypothesis, as a statement about lines

`AePin.lean` proves that the hyperbolic strip is a slab: inside a ball of radius `M`, the pins
whose distances to `x` and to `x'` differ by less than `δ` all lie within `2 M δ / ‖x - x'‖` of
the perpendicular bisector of `x` and `x'`.  That identity is exact and needs no analysis.

Applying it to the one remaining hypothesis of the development rewrites it as a statement about
how the pin measure distributes over a family of **lines**:

  `∫∫ ν(slab of half-width 4 M δ / ‖x - x'‖ around the bisector of x, x') dμ dμ = O(δ)`.

`hypTubeBoundC_of_bisectorSlabBound` proves that this implies `HypTubeBoundC`, so the entire
formalization — Frostman's lemma, the separation step, the covering piece extracted from the
packing hypothesis, Fatou over the pins, the overlap identity, Cauchy–Schwarz, absolute
continuity, positive length, and the branch combination — now rests on that single inequality.

Its difficulty is visible in the statement.  A `t`-Frostman `ν` obeys only
`ν(slab of width w) ≲ w ^ (t - 1)`, and `t ≤ 2` in the plane, so the trivial bound is one power
short of the `w` that is needed.  The average of `ν` over the *translates* of a slab in a fixed
direction is exactly of order `w`, so the required estimate says that the bisectors of source
pairs are generic enough to see the average rather than the worst case.  That is the content of
Orponen's radial-projection theorem, and it is not proved here.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- The slab of half-width `h` around the perpendicular bisector of `x` and `x'`. -/
def bisectorSlab (x x' : Plane) (h : ℝ) : Set Plane :=
  {y : Plane | |⟪y - (2 : ℝ)⁻¹ • (x + x'), radialProj x x'⟫| ≤ h}

theorem measurableSet_bisectorSlab (x x' : Plane) (h : ℝ) :
    MeasurableSet (bisectorSlab x x' h) := by
  refine measurableSet_le (continuous_abs.measurable.comp ?_) measurable_const
  exact (measurable_projNormal (radialProj x x')).comp (measurable_id.sub measurable_const)

/-- **The hyperbolic strip is a slab.**  Inside a ball of radius `M`, the pins whose distances to
`x` and to `x'` differ by less than `δ` all lie within `2 M δ / ‖x - x'‖` of the perpendicular
bisector.  This is the exact identity
`(‖y - x‖ - ‖y - x'‖)(‖y - x‖ + ‖y - x'‖) = 2⟪y - m, x' - x⟫`, divided by `‖x - x'‖`. -/
theorem strip_subset_bisectorSlab {x x' : Plane} (hxx : x' ≠ x) {M δ : ℝ} (hδ : 0 < δ)
    (hx : ‖x‖ ≤ M) (hx' : ‖x'‖ ≤ M) :
    {y : Plane | ‖y‖ ≤ M ∧ |dist x y - dist x' y| < δ}
      ⊆ bisectorSlab x x' (2 * M * δ / ‖x - x'‖) := by
  have hρ : (0:ℝ) < ‖x - x'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxx))
  have hρ' : ‖x' - x‖ = ‖x - x'‖ := norm_sub_rev _ _
  have hsmul : x' - x = ‖x - x'‖ • radialProj x x' := by
    rw [radialProj, smul_smul, hρ', mul_inv_cancel₀ hρ.ne', one_smul]
  rintro y ⟨hy, hd⟩
  have hM : ‖y - x‖ + ‖y - x'‖ ≤ 4 * M := by
    have h1 : ‖y - x‖ ≤ 2 * M := le_trans (norm_sub_le y x) (by linarith)
    have h2 : ‖y - x'‖ ≤ 2 * M := le_trans (norm_sub_le y x') (by linarith)
    linarith
  have hkey := abs_inner_le_of_abs_dist_sub_lt hM hd hδ
  rw [hsmul, real_inner_smul_right, abs_mul, abs_of_pos hρ] at hkey
  show |⟪y - (2 : ℝ)⁻¹ • (x + x'), radialProj x x'⟫| ≤ 2 * M * δ / ‖x - x'‖
  rw [le_div_iff₀ hρ]
  calc |⟪y - (2 : ℝ)⁻¹ • (x + x'), radialProj x x'⟫| * ‖x - x'‖
      = ‖x - x'‖ * |⟪y - (2 : ℝ)⁻¹ • (x + x'), radialProj x x'⟫| := by ring
    _ ≤ δ * (4 * M) / 2 := hkey
    _ = 2 * M * δ := by ring



/-- The containment holds on the diagonal too, where the slab degenerates to everything. -/
theorem strip_subset_bisectorSlab' (x x' : Plane) {M δ : ℝ} (hδ : 0 < δ)
    (hx : ‖x‖ ≤ M) (hx' : ‖x'‖ ≤ M) :
    {y : Plane | ‖y‖ ≤ M ∧ |dist x y - dist x' y| < δ}
      ⊆ bisectorSlab x x' (2 * M * δ / ‖x - x'‖) := by
  rcases eq_or_ne x' x with rfl | hxx
  · intro y _
    simp [bisectorSlab, radialProj]
  · exact strip_subset_bisectorSlab hxx hδ hx hx'

/-- Tonelli: the tube mass averaged over an arbitrary pin measure is the pin mass of the strips
averaged over the source pairs. -/
theorem lintegral_hypTube_eq (μ ν : Measure Plane) [SFinite μ] [SFinite ν] {δ : ℝ} :
    (∫⁻ y, (μ.prod μ) (hypTube y δ) ∂ν)
      = ∫⁻ q : Plane × Plane, ν {y : Plane | |dist q.1 y - dist q.2 y| < δ} ∂(μ.prod μ) := by
  set S : Set (Plane × (Plane × Plane)) :=
    {z | |dist z.2.1 z.1 - dist z.2.2 z.1| < δ} with hS
  have hSmeas : MeasurableSet S := measurableSet_hypTube_prod δ
  calc (∫⁻ y, (μ.prod μ) (hypTube y δ) ∂ν)
      = ∫⁻ y, (∫⁻ q : Plane × Plane, S.indicator 1 (y, q) ∂(μ.prod μ)) ∂ν := by
        refine lintegral_congr fun y => ?_
        have hEq : hypTube y δ = Prod.mk y ⁻¹' S := rfl
        rw [hEq, ← lintegral_indicator_one (measurable_prodMk_left hSmeas)]
        rfl
    _ = ∫⁻ q : Plane × Plane, (∫⁻ y, S.indicator 1 (y, q) ∂ν) ∂(μ.prod μ) :=
        lintegral_lintegral_swap (measurable_const.indicator hSmeas).aemeasurable
    _ = ∫⁻ q : Plane × Plane, ν {y : Plane | |dist q.1 y - dist q.2 y| < δ} ∂(μ.prod μ) := by
        refine lintegral_congr fun q => ?_
        have hmp : MeasurableSet ((fun y : Plane => (y, q)) ⁻¹' S) :=
          measurable_prodMk_right hSmeas
        rw [show (fun y : Plane => S.indicator (1 : Plane × (Plane × Plane) → ℝ≥0∞) (y, q))
            = ((fun y : Plane => (y, q)) ⁻¹' S).indicator 1 from rfl,
          lintegral_indicator_one hmp]
        rfl



/-- **The bisector-slab hypothesis.**  For a separated pair of `d`-Frostman probability measures
with the source carried by a set of upper box dimension `u`, the pin mass of the slab of
half-width `4 M δ / ‖x - x'‖` around the perpendicular bisector of `x` and `x'`, averaged over
the source pairs, is `O(δ)`.

This is the same analytic content as `HypTubeBoundC`, in the form the literature uses: a
statement about how a measure distributes over a family of **lines**.  The trivial bound is
`ν(slab of width w) ≲ w ^ (t - 1)` for a `t`-Frostman `ν`, which is one power short of the
`w` needed; the gain has to come from the bisectors of source pairs being generic, and that is
what Orponen's radial-projection theorem supplies. -/
def BisectorSlabBound (d u : ℝ) : Prop :=
  ∀ (μ ν : Measure Plane) (S : Set Plane) (Cμ Cν sep M : ℝ),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    IsFrostman μ d Cμ → IsFrostman ν d Cν →
    μ Sᶜ = 0 → HasUpperBoxBound S u →
    0 < sep → (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, sep ≤ dist x y) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ M) → (∀ᵐ y ∂ν, ‖y‖ ≤ M) →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n, (∫⁻ q : Plane × Plane,
          ν (bisectorSlab q.1 q.2 (4 * M * δ n / ‖q.1 - q.2‖)) ∂(μ.prod μ))
        ≤ ENNReal.ofReal (2 * δ n) * C

/-- **The two hypotheses are the same one.**  The strip-is-a-slab containment turns the
bisector-slab bound into the hyperbolic-tube bound, so the whole development rests on a
statement purely about a measure's mass on thin slabs around a family of lines. -/
theorem hypTubeBoundC_of_bisectorSlabBound {d u : ℝ} (h : BisectorSlabBound d u) :
    HypTubeBoundC d u := by
  intro μ ν S Cμ Cν sep M hμp hνp hμfr hνfr hμS hSbox hsep hae hμM hνM
  haveI := hμp
  haveI := hνp
  obtain ⟨C, hC, δ, hpos, hto, hb⟩ :=
    h μ ν S Cμ Cν sep M hμp hνp hμfr hνfr hμS hSbox hsep hae hμM hνM
  refine ⟨C, hC, δ, hpos, hto, fun n => ?_⟩
  refine le_trans (le_of_eq (lintegral_hypTube_eq μ ν)) (le_trans ?_ (hb n))
  have hBnull : ν {y : Plane | ‖y‖ ≤ M}ᶜ = 0 := ae_iff.1 hνM
  have hprod : ∀ᵐ q : Plane × Plane ∂(μ.prod μ), ‖q.1‖ ≤ M ∧ ‖q.2‖ ≤ M := by
    have hcar : μ {x : Plane | ‖x‖ ≤ M}ᶜ = 0 := ae_iff.1 hμM
    have h1 : (μ.prod μ) ({x : Plane | ‖x‖ ≤ M}ᶜ ×ˢ (univ : Set Plane)) = 0 := by
      rw [Measure.prod_prod, hcar, zero_mul]
    have h2 : (μ.prod μ) ((univ : Set Plane) ×ˢ {x : Plane | ‖x‖ ≤ M}ᶜ) = 0 := by
      rw [Measure.prod_prod, hcar, mul_zero]
    refine measure_mono_null (fun q hq => ?_) (measure_union_null h1 h2)
    rcases not_and_or.1 hq with hq' | hq'
    · exact Or.inl ⟨hq', Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, hq'⟩
  refine lintegral_mono_ae ?_
  filter_upwards [hprod] with q hq
  have hwidth : 2 * M * (2 * δ n) / ‖q.1 - q.2‖ = 4 * M * δ n / ‖q.1 - q.2‖ := by
    congr 1; ring
  have hsub : {y : Plane | |dist q.1 y - dist q.2 y| < 2 * δ n}
      ⊆ {y : Plane | ‖y‖ ≤ M ∧ |dist q.1 y - dist q.2 y| < 2 * δ n}
        ∪ {y : Plane | ‖y‖ ≤ M}ᶜ := by
    intro y hy
    by_cases hb' : ‖y‖ ≤ M
    · exact Or.inl ⟨hb', hy⟩
    · exact Or.inr hb'
  calc ν {y : Plane | |dist q.1 y - dist q.2 y| < 2 * δ n}
      ≤ ν ({y : Plane | ‖y‖ ≤ M ∧ |dist q.1 y - dist q.2 y| < 2 * δ n}
            ∪ {y : Plane | ‖y‖ ≤ M}ᶜ) := measure_mono hsub
    _ ≤ ν {y : Plane | ‖y‖ ≤ M ∧ |dist q.1 y - dist q.2 y| < 2 * δ n}
          + ν {y : Plane | ‖y‖ ≤ M}ᶜ := measure_union_le _ _
    _ = ν {y : Plane | ‖y‖ ≤ M ∧ |dist q.1 y - dist q.2 y| < 2 * δ n} := by
        rw [hBnull, add_zero]
    _ ≤ ν (bisectorSlab q.1 q.2 (4 * M * δ n / ‖q.1 - q.2‖)) := by
        refine measure_mono ?_
        rw [← hwidth]
        exact strip_subset_bisectorSlab' q.1 q.2 (by linarith [hpos n]) hq.1 hq.2

end FalconerPacking
