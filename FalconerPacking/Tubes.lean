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

/-! ### The second chart, and the coordinate-free bound

A single slope chart degenerates on one direction: `normalSlope a = (1, a)` never separates a
displacement whose second coordinate vanishes, and the bound above is then vacuously `⊤`.  The
transposed chart `normalSlopeT a = (a, 1)` degenerates on a different direction, and the two
together cover the circle.  Combining them removes the coordinate artifact entirely.
-/

/-- The sublevel set of a nonconstant affine function of the slope is an interval of length
`2c / |β|`.  This is the engine of both chart estimates. -/
theorem volume_setOf_abs_linear_lt (α β c : ℝ) (hβ : β ≠ 0) :
    volume {a : ℝ | |α + a * β| < c} ≤ ENNReal.ofReal (2 * c / |β|) := by
  have habs : (0 : ℝ) < |β| := abs_pos.2 hβ
  set m : ℝ := -α / β with hm
  set w : ℝ := c / |β| with hw
  have hsub : {a : ℝ | |α + a * β| < c} ⊆ Set.Ioo (m - w) (m + w) := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    have key : |a - m| < w := by
      have hmul : |a - m| * |β| = |α + a * β| := by
        rw [← abs_mul, hm]; congr 1; field_simp; ring
      rw [hw, lt_div_iff₀ habs, hmul]; exact ha
    rw [abs_lt] at key
    exact ⟨by linarith [key.1], by linarith [key.2]⟩
  refine le_trans (measure_mono hsub) ?_
  rw [Real.volume_Ioo]
  apply ENNReal.ofReal_le_ofReal
  rw [hw]; field_simp; ring_nf; rfl

/-- The transposed normal of slope `a`: the second chart of the direction circle. -/
def normalSlopeT (a : ℝ) : Plane := !₂[a, 1]

theorem inner_normalSlopeT (v : Plane) (a : ℝ) : ⟪v, normalSlopeT a⟫ = v 1 + a * v 0 := by
  rw [inner_plane, normalSlopeT]; simp; ring

/-- On the first chart the slope is bounded, so a displacement whose first coordinate dominates
is never annihilated. -/
theorem eq_empty_of_lt_sub {v : Plane} {δ : ℝ} (h : δ ≤ |v 0| - |v 1|) :
    {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlope a⟫| < δ} = ∅ := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro ha
  rw [inner_normalSlope]
  have h1 : |a * v 1| ≤ |v 1| := by
    rw [abs_mul]
    nlinarith [abs_nonneg (v 1), abs_nonneg a]
  calc δ ≤ |v 0| - |v 1| := h
    _ ≤ |v 0| - |a * v 1| := by linarith
    _ ≤ |v 0 + a * v 1| := by
        have := abs_sub_abs_le_abs_sub (v 0) (-(a * v 1))
        simp only [abs_neg, sub_neg_eq_add] at this
        linarith


/-- A chart contributes at most `4δ / N` when its slope coefficient is at least `N / 2`. -/
theorem chart_le_of_large (α β δ N : ℝ) (hδ : 0 < δ) (hN : 0 < N) (hβ : N / 2 ≤ |β|) :
    volume {a : ℝ | |a| ≤ 1 ∧ |α + a * β| < δ} ≤ ENNReal.ofReal (4 * δ / N) := by
  have hβ0 : β ≠ 0 := by
    intro h; rw [h, abs_zero] at hβ; linarith
  have habs : (0 : ℝ) < |β| := abs_pos.2 hβ0
  refine le_trans (measure_mono fun a ha => ha.2) ?_
  refine le_trans (volume_setOf_abs_linear_lt α β δ hβ0) ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_div_iff₀ habs hN]
  nlinarith

/-- A chart contributes nothing when its constant term dominates. -/
theorem chart_eq_zero_of_small (α β δ : ℝ) (h : δ ≤ |α| - |β|) :
    volume {a : ℝ | |a| ≤ 1 ∧ |α + a * β| < δ} = 0 := by
  have : {a : ℝ | |a| ≤ 1 ∧ |α + a * β| < δ} = ∅ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
    intro ha
    have h1 : |a * β| ≤ |β| := by
      rw [abs_mul]; nlinarith [abs_nonneg β, abs_nonneg a]
    have h2 := abs_sub_abs_le_abs_sub α (-(a * β))
    simp only [abs_neg, sub_neg_eq_add] at h2
    linarith
  rw [this, measure_empty]

/-- **The two-chart directional estimate.**  The two slope charts cover the circle of
directions, and together they give the coordinate-free bound: the directions nearly
annihilating a displacement `v` occupy measure `≤ 8δ / ‖v‖`.  Neither chart alone can say this,
since each degenerates on one direction; the point is that they degenerate on different ones. -/
theorem volume_chart_add_chartT_le (v : Plane) {δ : ℝ} (hδ : 0 < δ) (hv : 4 * δ ≤ ‖v‖) :
    volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlope a⟫| < δ}
      + volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlopeT a⟫| < δ}
      ≤ ENNReal.ofReal (8 * δ / ‖v‖) := by
  set N := ‖v‖ with hNdef
  have hN : 0 < N := by linarith
  have hsq : N ^ 2 = v 0 ^ 2 + v 1 ^ 2 := norm_sq_plane v
  have habs0 : |v 0| ^ 2 = v 0 ^ 2 := sq_abs _
  have habs1 : |v 1| ^ 2 = v 1 ^ 2 := sq_abs _
  have hform1 : {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlope a⟫| < δ}
      = {a : ℝ | |a| ≤ 1 ∧ |v 0 + a * v 1| < δ} := by
    ext a; simp [inner_normalSlope]
  have hform2 : {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlopeT a⟫| < δ}
      = {a : ℝ | |a| ≤ 1 ∧ |v 1 + a * v 0| < δ} := by
    ext a; simp [inner_normalSlopeT]
  rw [hform1, hform2]
  rcases le_or_gt (N / 2) |v 1| with h1 | h1
  · -- the first chart is good
    have c1 := chart_le_of_large (v 0) (v 1) δ N hδ hN h1
    rcases le_or_gt (N / 2) |v 0| with h0 | h0
    · have c2 := chart_le_of_large (v 1) (v 0) δ N hδ hN h0
      calc _ ≤ ENNReal.ofReal (4 * δ / N) + ENNReal.ofReal (4 * δ / N) := add_le_add c1 c2
        _ = ENNReal.ofReal (8 * δ / N) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    · have hbig : δ ≤ |v 1| - |v 0| := by
        have : |v 1| ^ 2 ≥ 3 * N ^ 2 / 4 := by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
        nlinarith [abs_nonneg (v 1), abs_nonneg (v 0)]
      rw [chart_eq_zero_of_small (v 1) (v 0) δ hbig, add_zero]
      exact le_trans c1 (ENNReal.ofReal_le_ofReal (by
        rw [div_le_div_iff₀ hN hN]; nlinarith))
  · -- the first chart degenerates, so the second is good and the first is empty
    have hv0 : N / 2 ≤ |v 0| := by
      nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
    have c2 := chart_le_of_large (v 1) (v 0) δ N hδ hN hv0
    have hbig : δ ≤ |v 0| - |v 1| := by
      have : |v 0| ^ 2 ≥ 3 * N ^ 2 / 4 := by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]
      nlinarith [abs_nonneg (v 1), abs_nonneg (v 0)]
    rw [chart_eq_zero_of_small (v 0) (v 1) δ hbig, zero_add]
    exact le_trans c2 (ENNReal.ofReal_le_ofReal (by
      rw [div_le_div_iff₀ hN hN]; nlinarith))


/-- The two-chart estimate without the separation hypothesis.  Each chart has length two, so
the trivial bound covers the near-diagonal range, and `ENNReal` division makes the degenerate
value `⊤`. -/
theorem volume_chart_add_chartT_le_uniform (v : Plane) {δ : ℝ} (hδ : 0 < δ) :
    volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlope a⟫| < δ}
      + volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, normalSlopeT a⟫| < δ}
      ≤ ENNReal.ofReal (16 * δ) / ENNReal.ofReal ‖v‖ := by
  have htriv : ∀ e : ℝ → Plane, volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, e a⟫| < δ} ≤ 2 := by
    intro e
    have hsub : {a : ℝ | |a| ≤ 1 ∧ |⟪v, e a⟫| < δ} ⊆ Set.Icc (-1 : ℝ) 1 :=
      fun a ha => abs_le.1 ha.1
    calc volume {a : ℝ | |a| ≤ 1 ∧ |⟪v, e a⟫| < δ} ≤ volume (Set.Icc (-1 : ℝ) 1) :=
          measure_mono hsub
      _ = 2 := by rw [Real.volume_Icc]; norm_num
  rcases eq_or_lt_of_le (norm_nonneg v) with hv0 | hvpos
  · have : ENNReal.ofReal (16 * δ) / ENNReal.ofReal ‖v‖ = ⊤ := by
      rw [← hv0, ENNReal.ofReal_zero, ENNReal.div_zero
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)]
    rw [this]; exact le_top
  · rw [ENNReal.le_div_iff_mul_le (Or.inl (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hvpos))
      (Or.inl ENNReal.ofReal_ne_top)]
    rcases le_or_gt (4 * δ) ‖v‖ with hsep | hsep
    · have hmain := volume_chart_add_chartT_le v hδ hsep
      calc _ ≤ ENNReal.ofReal (8 * δ / ‖v‖) * ENNReal.ofReal ‖v‖ :=
            by gcongr
        _ = ENNReal.ofReal (8 * δ) := by
            rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hvpos.ne']
        _ ≤ ENNReal.ofReal (16 * δ) := ENNReal.ofReal_le_ofReal (by linarith)
    · calc _ ≤ (2 + 2 : ℝ≥0∞) * ENNReal.ofReal ‖v‖ :=
            by gcongr <;> [exact htriv _; exact htriv _]
        _ ≤ ENNReal.ofReal (16 * δ) := by
            rw [show ((2 : ℝ≥0∞) + 2) = ENNReal.ofReal 4 by
              rw [show (4:ℝ) = 2 + 2 by norm_num, ENNReal.ofReal_add (by norm_num) (by norm_num)]
              norm_num,
              ← ENNReal.ofReal_mul (by norm_num)]
            exact ENNReal.ofReal_le_ofReal (by linarith)


/-- Tonelli over the slope chart, for either family of normals. -/
theorem swap_chart (μ : Measure Plane) [SFinite μ] (e : ℝ → Plane) {δ : ℝ}
    (hg : Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, e z.1⟫) :
    ∫⁻ a in Set.Icc (-1 : ℝ) 1, (μ.prod μ) {p : Plane × Plane | |⟪p.1 - p.2, e a⟫| < δ}
      = ∫⁻ p : Plane × Plane,
          volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, e a⟫| < δ} ∂(μ.prod μ) := by
  have hS : MeasurableSet {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, e z.1⟫| < δ} := by
    have : {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, e z.1⟫| < δ}
        = {z | -δ < ⟪z.2.1 - z.2.2, e z.1⟫} ∩ {z | ⟪z.2.1 - z.2.2, e z.1⟫ < δ} := by
      ext z; simp [abs_lt]
    rw [this]
    exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)
  set S := {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, e z.1⟫| < δ} with hSdef
  calc ∫⁻ a in Set.Icc (-1 : ℝ) 1, (μ.prod μ) {p : Plane × Plane | |⟪p.1 - p.2, e a⟫| < δ}
      = ∫⁻ a, ∫⁻ p, S.indicator 1 (a, p) ∂(μ.prod μ) ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)) := by
        refine lintegral_congr fun a => ?_
        have hEq : {p : Plane × Plane | |⟪p.1 - p.2, e a⟫| < δ} = Prod.mk a ⁻¹' S := rfl
        rw [hEq, ← lintegral_indicator_one (measurable_prodMk_left hS)]
        rfl
    _ = ∫⁻ p, ∫⁻ a, S.indicator 1 (a, p) ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)) ∂(μ.prod μ) := by
        exact lintegral_lintegral_swap (measurable_const.indicator hS).aemeasurable
    _ = ∫⁻ p : Plane × Plane,
          volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, e a⟫| < δ} ∂(μ.prod μ) := by
        refine lintegral_congr fun p => ?_
        have hEq : (fun x : ℝ => (x, p)) ⁻¹' S = {a : ℝ | |⟪p.1 - p.2, e a⟫| < δ} := rfl
        have hmp : MeasurableSet ((fun x : ℝ => (x, p)) ⁻¹' S) := measurable_prodMk_right hS
        rw [show (fun a : ℝ => S.indicator (1 : ℝ × (Plane × Plane) → ℝ≥0∞) (a, p))
            = ((fun x : ℝ => (x, p)) ⁻¹' S).indicator 1 from rfl,
          lintegral_indicator_one hmp, Measure.restrict_apply hmp, hEq]
        congr 1
        ext a
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc, abs_le]
        tauto


theorem measurable_chart_volume (e : ℝ → Plane) {δ : ℝ}
    (hg : Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, e z.1⟫) :
    Measurable fun p : Plane × Plane =>
      volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, e a⟫| < δ} := by
  have hS : MeasurableSet {z : ℝ × (Plane × Plane) | |z.1| ≤ 1 ∧ |⟪z.2.1 - z.2.2, e z.1⟫| < δ} := by
    have h1 : MeasurableSet {z : ℝ × (Plane × Plane) | |z.1| ≤ 1} := by
      have hrw : {z : ℝ × (Plane × Plane) | |z.1| ≤ 1} = Prod.fst ⁻¹' (Set.Icc (-1 : ℝ) 1) := by
        ext z; simp [abs_le]
      rw [hrw]
      exact measurable_fst measurableSet_Icc
    have h2 : MeasurableSet {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, e z.1⟫| < δ} := by
      have : {z : ℝ × (Plane × Plane) | |⟪z.2.1 - z.2.2, e z.1⟫| < δ}
          = {z | -δ < ⟪z.2.1 - z.2.2, e z.1⟫} ∩ {z | ⟪z.2.1 - z.2.2, e z.1⟫ < δ} := by
        ext z; simp [abs_lt]
      rw [this]
      exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)
    exact h1.inter h2
  exact measurable_measure_prodMk_right hS

theorem measurable_inner_normalSlope :
    Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, normalSlope z.1⟫ := by
  have : (fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, normalSlope z.1⟫)
      = fun z => (z.2.1 - z.2.2) 0 + z.1 * (z.2.1 - z.2.2) 1 := by
    funext z; exact inner_normalSlope _ _
  rw [this]
  exact ((measurable_coord 0).comp ((measurable_fst.comp measurable_snd).sub
      (measurable_snd.comp measurable_snd))).add
    (measurable_fst.mul ((measurable_coord 1).comp ((measurable_fst.comp measurable_snd).sub
      (measurable_snd.comp measurable_snd))))

theorem measurable_inner_normalSlopeT :
    Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, normalSlopeT z.1⟫ := by
  have : (fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, normalSlopeT z.1⟫)
      = fun z => (z.2.1 - z.2.2) 1 + z.1 * (z.2.1 - z.2.2) 0 := by
    funext z; exact inner_normalSlopeT _ _
  rw [this]
  exact ((measurable_coord 1).comp ((measurable_fst.comp measurable_snd).sub
      (measurable_snd.comp measurable_snd))).add
    (measurable_fst.mul ((measurable_coord 0).comp ((measurable_fst.comp measurable_snd).sub
      (measurable_snd.comp measurable_snd))))


/-- **The coordinate-free averaged tube-square bound.**  Averaging the slab direction over both
slope charts, which together cover the circle of directions, the sum of the squares of the slab
masses is controlled by the `1`-energy integrand of `μ` against itself — with no preferred
coordinate axis.  For a Frostman measure of exponent above one the right-hand side is finite,
so at almost every direction the slab masses are square-summable at every scale, uniformly. -/
theorem lintegral_tsum_measure_slab_sq_two_chart_le
    (μ : Measure Plane) [SFinite μ] {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2)
      + (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlopeT a) δ k)) ^ 2)
      ≤ ∫⁻ p : Plane × Plane,
          ENNReal.ofReal (16 * δ) / ENNReal.ofReal ‖p.1 - p.2‖ ∂(μ.prod μ) := by
  have step : ∀ e : ℝ → Plane,
      (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (e a) δ k)) ^ 2)
        ≤ ∫⁻ a in Set.Icc (-1 : ℝ) 1,
            (μ.prod μ) {p : Plane × Plane | |⟪p.1 - p.2, e a⟫| < δ} := by
    intro e
    refine lintegral_mono fun a => ?_
    rw [tsum_measure_slab_sq]
    exact measure_mono fun p hp => abs_inner_sub_lt_of_slabIndex_eq hδ hp
  calc (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2)
        + (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlopeT a) δ k)) ^ 2)
      ≤ (∫⁻ a in Set.Icc (-1 : ℝ) 1,
            (μ.prod μ) {p : Plane × Plane | |⟪p.1 - p.2, normalSlope a⟫| < δ})
          + (∫⁻ a in Set.Icc (-1 : ℝ) 1,
            (μ.prod μ) {p : Plane × Plane | |⟪p.1 - p.2, normalSlopeT a⟫| < δ}) :=
        add_le_add (step normalSlope) (step normalSlopeT)
    _ = (∫⁻ p, volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, normalSlope a⟫| < δ} ∂(μ.prod μ))
          + (∫⁻ p, volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, normalSlopeT a⟫| < δ} ∂(μ.prod μ)) := by
        rw [swap_chart μ _ measurable_inner_normalSlope,
          swap_chart μ _ measurable_inner_normalSlopeT]
    _ = ∫⁻ p, (volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, normalSlope a⟫| < δ}
          + volume {a : ℝ | |a| ≤ 1 ∧ |⟪p.1 - p.2, normalSlopeT a⟫| < δ}) ∂(μ.prod μ) :=
        (lintegral_add_left (measurable_chart_volume _ measurable_inner_normalSlope) _).symm
    _ ≤ ∫⁻ p : Plane × Plane,
          ENNReal.ofReal (16 * δ) / ENNReal.ofReal ‖p.1 - p.2‖ ∂(μ.prod μ) :=
        lintegral_mono fun p => volume_chart_add_chartT_le_uniform _ hδ

/-! ### Against the Riesz energy

The reciprocal-separation integral on the right of the two-chart bound is exactly the Riesz
`1`-energy of `μ`, which `Energy.lean` shows is finite for every Frostman exponent above one.
-/

/-- The product-form reciprocal-separation integral is the Riesz `1`-energy, up to the constant. -/
theorem lintegral_prod_inv_norm_sub (μ : Measure Plane) [SFinite μ] (c : ℝ) :
    ∫⁻ p : Plane × Plane,
        ENNReal.ofReal c / ENNReal.ofReal ‖p.1 - p.2‖ ∂(μ.prod μ)
      = ENNReal.ofReal c * rieszEnergy μ 1 := by
  have hker : ∀ p : Plane × Plane,
      ENNReal.ofReal c / ENNReal.ofReal ‖p.1 - p.2‖
        = ENNReal.ofReal c * rieszKernel 1 p.1 p.2 := by
    intro p
    rw [rieszKernel, ENNReal.rpow_neg_one, ← dist_eq_norm, div_eq_mul_inv]
  have hmeas : Measurable fun p : Plane × Plane => rieszKernel 1 p.1 p.2 := by
    unfold rieszKernel
    exact (ENNReal.measurable_ofReal.comp measurable_dist).pow_const _
  calc ∫⁻ p : Plane × Plane,
        ENNReal.ofReal c / ENNReal.ofReal ‖p.1 - p.2‖ ∂(μ.prod μ)
      = ∫⁻ p : Plane × Plane, ENNReal.ofReal c * rieszKernel 1 p.1 p.2 ∂(μ.prod μ) :=
        lintegral_congr hker
    _ = ENNReal.ofReal c * ∫⁻ p : Plane × Plane, rieszKernel 1 p.1 p.2 ∂(μ.prod μ) :=
        lintegral_const_mul _ hmeas
    _ = ENNReal.ofReal c * rieszEnergy μ 1 := by
        rw [rieszEnergy, lintegral_prod _ hmeas.aemeasurable]

/-- **The tube-square bound against the energy.**  For a measure of finite `1`-energy — in
particular for any Frostman measure of exponent above one — the averaged sum of the squares of
the slab masses is at most `16 δ` times that energy, uniformly in the scale. -/
theorem lintegral_tsum_measure_slab_sq_le_energy
    (μ : Measure Plane) [SFinite μ] {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2)
      + (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlopeT a) δ k)) ^ 2)
      ≤ ENNReal.ofReal (16 * δ) * rieszEnergy μ 1 := by
  refine le_trans (lintegral_tsum_measure_slab_sq_two_chart_le μ hδ) ?_
  rw [lintegral_prod_inv_norm_sub μ (16 * δ)]

/-- The tube-square bound is finite for a Frostman measure of exponent above one. -/
theorem lintegral_tsum_measure_slab_sq_ne_top
    (μ : Measure Plane) [IsFiniteMeasure μ] {s C δ : ℝ} (hC : 0 < C) (hs : 1 < s)
    (hfr : IsFrostman μ s C) (hδ : 0 < δ) :
    ((∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlope a) δ k)) ^ 2)
      + (∫⁻ a in Set.Icc (-1 : ℝ) 1, ∑' k : ℤ, (μ (slab (normalSlopeT a) δ k)) ^ 2)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_tsum_measure_slab_sq_le_energy μ hδ)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (rieszEnergy_ne_top hC one_pos hs hfr)

end FalconerPacking
