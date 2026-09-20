/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjection
import Mathlib.MeasureTheory.Function.Floor

/-!
# Slabs, tubes, and the averaged tube-square bound

Module 7 of the manuscript's ledger, continued from `RadialProjection.lean`.

Both analytic branches of Theorem 1.1 need to count *heavy tubes*: the `δ`-tubes carrying an
unusually large share of a Frostman measure.  Guth–Iosevich–Ou–Wang delete them in Lemma 3.6,
and Orponen's radial-projection theorem is the statement that they are rare.  This file proves
the soft half of that count, which needs no projection theory at all.

The direction of a tube is parametrized by its slope rather than by a point of the circle, so
no arclength measure and no inverse trigonometry are needed: `normalSlope a = (1, a)` and the
slabs `slab (normalSlope a) δ k` are the level sets of `⌊⟪x, normalSlope a⟫ / δ⌋`.

The main results are

* `tsum_measure_slab_sq`: the slabs of a fixed direction tile the plane, so the sum of the
  squares of their masses is the mass of the coincidence block `{p | same slab}` in `μ × μ`;
* `volume_setOf_abs_inner_normalSlope_lt`: **the directional estimate**, that the slopes whose
  normal nearly annihilates a fixed displacement `v` form a set of measure `≤ 2c / |v 1|`;
* `lintegral_tsum_measure_slab_sq_le`: **the averaged tube-square bound**
  `∫ Σ_k μ(slab a δ k)² da ≤ ∫∫ 2δ / |(x - y) 1| dμ dμ`,
  which is finite whenever `μ` has finite `1`-energy in the second coordinate, hence for every
  Frostman exponent above one;
* `card_mul_le_tsum_measure_slab_sq`: Chebyshev, turning that into a bound on the number of
  heavy slabs.

Division in `ℝ≥0∞` sends `x / 0` to `⊤`, which is the correct value here: a displacement with
`v 1 = 0` is annihilated by every slope, and the left-hand side is genuinely infinite.  No
hypothesis excluding that degenerate direction is therefore needed.

What this does **not** give is Orponen's theorem.  The bound above controls the *second* moment
of the slab masses, so it counts slabs of mass `≥ lam` to precision `lam ^ (-2)`.  The
radial-projection theorem needs the heavy slabs to be rarer than any second-moment argument can
show — that is the step requiring the discretized projection machinery.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The index of the slab of width `δ` perpendicular to `e` containing `x`. -/
def slabIndex (e : Plane) (δ : ℝ) (x : Plane) : ℤ := ⌊⟪x, e⟫ / δ⌋

/-- The slab of width `δ` perpendicular to `e` with index `k`. -/
def slab (e : Plane) (δ : ℝ) (k : ℤ) : Set Plane := {x | slabIndex e δ x = k}

theorem measurable_slabIndex (e : Plane) (δ : ℝ) : Measurable (slabIndex e δ) := by
  unfold slabIndex
  exact Measurable.floor (by fun_prop)

theorem measurableSet_slab (e : Plane) (δ : ℝ) (k : ℤ) : MeasurableSet (slab e δ k) :=
  measurable_slabIndex e δ (measurableSet_singleton k)

theorem pairwise_disjoint_slab (e : Plane) (δ : ℝ) :
    Pairwise (Function.onFun Disjoint (slab e δ)) := by
  intro i j hij
  simp only [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  exact hij (hx ▸ hx')


variable (μ : Measure Plane) [SFinite μ]

/-- The slabs of a fixed direction tile the plane, so the sum of the squares of their masses is
the mass of the "same slab" diagonal block in the product. -/
theorem tsum_measure_slab_sq (e : Plane) (δ : ℝ) :
    ∑' k : ℤ, (μ (slab e δ k)) ^ 2
      = (μ.prod μ) {p : Plane × Plane | slabIndex e δ p.1 = slabIndex e δ p.2} := by
  have hset : {p : Plane × Plane | slabIndex e δ p.1 = slabIndex e δ p.2}
      = ⋃ k : ℤ, (slab e δ k) ×ˢ (slab e δ k) := by
    ext p
    simp only [mem_setOf_eq, mem_iUnion, Set.mem_prod, slab]
    constructor
    · exact fun h => ⟨slabIndex e δ p.1, rfl, h.symm⟩
    · rintro ⟨k, h1, h2⟩; rw [h1, h2]
  rw [hset]
  rw [measure_iUnion ?_ ?_]
  · exact tsum_congr fun k => by rw [Measure.prod_prod, sq]
  · intro i j hij
    simp only [Function.onFun, Set.disjoint_left, Set.mem_prod]
    rintro p ⟨hp, -⟩ ⟨hp', -⟩
    exact hij (hp ▸ hp')
  · exact fun k => (measurableSet_slab e δ k).prod (measurableSet_slab e δ k)

/-- Two points in the same slab have close projections onto the slab normal. -/
theorem abs_inner_sub_lt_of_slabIndex_eq {e : Plane} {δ : ℝ} (hδ : 0 < δ) {x y : Plane}
    (h : slabIndex e δ x = slabIndex e δ y) : |⟪x - y, e⟫| < δ := by
  have h1 : (slabIndex e δ x : ℝ) ≤ ⟪x, e⟫ / δ := Int.floor_le _
  have h2 : ⟪x, e⟫ / δ < slabIndex e δ x + 1 := Int.lt_floor_add_one _
  have h3 : (slabIndex e δ y : ℝ) ≤ ⟪y, e⟫ / δ := Int.floor_le _
  have h4 : ⟪y, e⟫ / δ < slabIndex e δ y + 1 := Int.lt_floor_add_one _
  rw [h] at h1 h2
  have key1 : ⟪x, e⟫ / δ - ⟪y, e⟫ / δ < 1 := by linarith
  have key2 : ⟪y, e⟫ / δ - ⟪x, e⟫ / δ < 1 := by linarith
  rw [div_sub_div_same, div_lt_one hδ] at key1 key2
  rw [inner_sub_left, abs_lt]
  constructor <;> linarith


/-- The unnormalized normal of slope `a`.  Its norm lies between `1` and `√2`, so slabs taken
against it have width comparable to the slab parameter. -/
def normalSlope (a : ℝ) : Plane := !₂[1, a]

theorem inner_normalSlope (v : Plane) (a : ℝ) : ⟪v, normalSlope a⟫ = v 0 + a * v 1 := by
  rw [inner_plane, normalSlope]; simp; ring

theorem one_le_norm_normalSlope (a : ℝ) : 1 ≤ ‖normalSlope a‖ := by
  have h : ‖normalSlope a‖ ^ 2 = 1 + a ^ 2 := by
    rw [norm_sq_plane, normalSlope]; simp
  nlinarith [norm_nonneg (normalSlope a), sq_nonneg a]

theorem norm_normalSlope_le (a : ℝ) (ha : |a| ≤ 1) : ‖normalSlope a‖ ≤ Real.sqrt 2 := by
  have h : ‖normalSlope a‖ ^ 2 = 1 + a ^ 2 := by
    rw [norm_sq_plane, normalSlope]; simp
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_nonneg a, sq_abs a]
  have := Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
  nlinarith [norm_nonneg (normalSlope a), Real.sqrt_nonneg 2]

/-- **The directional estimate.**  For a fixed nonzero displacement, the slopes whose normal
nearly annihilates it form a set of measure at most `2 c / |v 1|`.  This is the trigonometry-free
substitute for `|{θ : |⟪v, θ⟫| < c}| ≲ c / ‖v‖` on the circle. -/
theorem volume_setOf_abs_inner_normalSlope_lt (v : Plane) (hv : v 1 ≠ 0) (c : ℝ) :
    volume {a : ℝ | |⟪v, normalSlope a⟫| < c} ≤ ENNReal.ofReal (2 * c / |v 1|) := by
  have habs : (0 : ℝ) < |v 1| := abs_pos.2 hv
  set m : ℝ := -(v 0) / v 1 with hm
  set w : ℝ := c / |v 1| with hw
  have hsub : {a : ℝ | |⟪v, normalSlope a⟫| < c} ⊆ Set.Ioo (m - w) (m + w) := by
    intro a ha
    simp only [Set.mem_setOf_eq, inner_normalSlope] at ha
    have key : |a - m| < w := by
      have : |a - m| * |v 1| = |v 0 + a * v 1| := by
        rw [← abs_mul, hm]
        congr 1
        field_simp
        ring
      rw [hw, lt_div_iff₀ habs, this]
      exact ha
    rw [abs_lt] at key
    exact ⟨by linarith [key.1], by linarith [key.2]⟩
  refine le_trans (measure_mono hsub) ?_
  rw [Real.volume_Ioo]
  apply ENNReal.ofReal_le_ofReal
  rw [hw]
  field_simp
  ring_nf
  rfl


/-- The directional estimate in `ℝ≥0∞`.  Division by zero is `⊤` there, which is exactly the
right value: when `v 1 = 0` every slope annihilates `v` and the left side is infinite. -/
theorem volume_setOf_lt_le_ennreal (v : Plane) {c : ℝ} (hc : 0 < c) :
    volume {a : ℝ | |⟪v, normalSlope a⟫| < c}
      ≤ ENNReal.ofReal (2 * c) / ENNReal.ofReal |v 1| := by
  rcases eq_or_ne (v 1) 0 with h | h
  · have hne : ENNReal.ofReal (2 * c) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith
    have htop : ENNReal.ofReal (2 * c) / ENNReal.ofReal |v 1| = ⊤ := by
      rw [h, abs_zero, ENNReal.ofReal_zero, ENNReal.div_zero hne]
    rw [htop]
    exact le_top
  · have habs : (0 : ℝ) < |v 1| := abs_pos.2 h
    rw [← ENNReal.ofReal_div_of_pos habs]
    exact volume_setOf_abs_inner_normalSlope_lt v h c

theorem measurable_coord (i : Fin 2) : Measurable fun x : Plane => x i := by
  fun_prop


/-- The slab-coincidence set in the product, as a function of the slope. -/
def coincide (δ : ℝ) (a : ℝ) : Set (Plane × Plane) :=
  {p | |⟪p.1 - p.2, normalSlope a⟫| < δ}

theorem measurableSet_uncurry (δ : ℝ) :
    MeasurableSet {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, normalSlope z.1⟫| < δ} := by
  have hg : Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, normalSlope z.1⟫ := by
    have : (fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, normalSlope z.1⟫)
        = fun z => (z.2.1 - z.2.2) 0 + z.1 * (z.2.1 - z.2.2) 1 := by
      funext z; exact inner_normalSlope _ _
    rw [this]
    exact ((measurable_coord 0).comp ((measurable_fst.comp measurable_snd).sub
        (measurable_snd.comp measurable_snd))).add
      (measurable_fst.mul ((measurable_coord 1).comp ((measurable_fst.comp measurable_snd).sub
        (measurable_snd.comp measurable_snd))))
  have hset : {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, normalSlope z.1⟫| < δ}
      = {z | -δ < ⟪z.2.1 - z.2.2, normalSlope z.1⟫} ∩ {z | ⟪z.2.1 - z.2.2, normalSlope z.1⟫ < δ} := by
    ext z; simp [abs_lt]
  rw [hset]
  exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)

/-- **The averaged tube-square bound.**  Averaging over the slope of the slab direction, the sum
of the squares of the slab masses is controlled by the reciprocal-separation integral of the
measure against itself.  This is the soft input behind every heavy-tube count. -/
theorem lintegral_tsum_measure_slab_sq_le (μ : Measure Plane) [SFinite μ] {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ a : ℝ, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2
      ≤ ∫⁻ p : Plane × Plane,
          ENNReal.ofReal (2 * δ) / ENNReal.ofReal |(p.1 - p.2) 1| ∂(μ.prod μ) := by
  have hms : ∀ a : ℝ, MeasurableSet (coincide δ a) := by
    intro a
    have := measurableSet_uncurry δ
    exact measurable_prodMk_left this
  have step1 : ∀ a : ℝ, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2
      ≤ (μ.prod μ) (coincide δ a) := by
    intro a
    rw [tsum_measure_slab_sq]
    exact measure_mono fun p hp => abs_inner_sub_lt_of_slabIndex_eq hδ hp
  calc ∫⁻ a : ℝ, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2
      ≤ ∫⁻ a : ℝ, (μ.prod μ) (coincide δ a) := lintegral_mono step1
    _ = ∫⁻ a : ℝ, ∫⁻ p, (coincide δ a).indicator 1 p ∂(μ.prod μ) := by
        exact lintegral_congr fun a => (lintegral_indicator_one (hms a)).symm
    _ = ∫⁻ p, ∫⁻ a : ℝ, (coincide δ a).indicator 1 p ∂volume ∂(μ.prod μ) := by
        apply lintegral_lintegral_swap
        refine Measurable.aemeasurable ?_
        exact measurable_const.indicator (measurableSet_uncurry δ)
    _ ≤ ∫⁻ p, ENNReal.ofReal (2 * δ) / ENNReal.ofReal |(p.1 - p.2) 1| ∂(μ.prod μ) := by
        apply lintegral_mono
        intro p
        show ∫⁻ a : ℝ, (coincide δ a).indicator 1 p
            ≤ ENNReal.ofReal (2 * δ) / ENNReal.ofReal |(p.1 - p.2) 1|
        have : ∫⁻ a : ℝ, (coincide δ a).indicator 1 p ∂volume
            = volume {a : ℝ | |⟪p.1 - p.2, normalSlope a⟫| < δ} := by
          rw [← lintegral_indicator_one]
          · exact lintegral_congr fun a => by simp [coincide, Set.indicator_apply]
          · exact measurable_prodMk_right (measurableSet_uncurry δ)
        rw [this]
        exact volume_setOf_lt_le_ennreal _ hδ


/-- **Chebyshev for slabs.**  Any finite family of slabs of a fixed direction, each carrying
mass at least `lam`, has cardinality at most the sum of the squares of the slab masses divided
by `lam ^ 2`.  Combined with the averaged tube-square bound this is the heavy-tube count. -/
theorem card_mul_le_tsum_measure_slab_sq (μ : Measure Plane) (e : Plane) (δ : ℝ)
    (lam : ℝ≥0∞) (s : Finset ℤ) (hs : ∀ k ∈ s, lam ≤ μ (slab e δ k)) :
    (s.card : ℝ≥0∞) * lam ^ 2 ≤ ∑' k : ℤ, (μ (slab e δ k)) ^ 2 := by
  calc (s.card : ℝ≥0∞) * lam ^ 2 = ∑ _k ∈ s, lam ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ s, (μ (slab e δ k)) ^ 2 :=
        Finset.sum_le_sum fun k hk => pow_le_pow_left' (hs k hk) 2
    _ ≤ ∑' k : ℤ, (μ (slab e δ k)) ^ 2 := ENNReal.sum_le_tsum s

end FalconerPacking
