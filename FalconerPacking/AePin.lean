/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Reduction
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The almost-every-pin problem, unconditionally

Theorem 1.1 asks for a pin *inside* the set, and that is what needs Orponen's radial-projection
theorem.  The almost-every-pin problem — a pin somewhere in a ball — turns out to need no
harmonic analysis at all, and this file proves it outright:

**a compactly supported probability measure of finite Riesz `1`-energy has, in every ball
containing its support, a pin whose pinned distance set has positive length**
(`exists_pin_ball_of_energy`).  Since a Frostman exponent above one gives finite `1`-energy, this
is the distance-set analogue of Marstrand's projection theorem.

The whole proof is the `L²` method of `PinnedL2.lean` plus one piece of plane geometry.  The
difference of *squared* distances is affine,

  `(‖y - x‖ - ‖y - x'‖)(‖y - x‖ + ‖y - x'‖) = 2⟪y - m, x' - x⟫`,

so bounding the difference of the distances by `δ` confines `y` to a slab of half-width
`2 R δ / ‖x - x'‖` around the perpendicular bisector — the hyperbolic strip *is* a slab, with no
co-area inequality and no change of variables.  A slab meets a ball of radius `R` in area at
most `8 R` times its width, which is a one-dimensional sublevel estimate integrated over the
other coordinate after transferring to the product measure.  The resulting area
`O(R² δ / ‖x - x'‖)` is then consumed by the Riesz `1`-energy:

  `∫∫ δ / ‖x - x'‖ dμ dμ = δ · I₁(μ)`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- **The difference of squared distances is affine.**  Its level sets are the lines parallel to
the perpendicular bisector of `x` and `x'`. -/
theorem norm_sq_sub_norm_sq (x x' y : Plane) :
    ‖y - x‖ ^ 2 - ‖y - x'‖ ^ 2 = 2 * ⟪y - (2 : ℝ)⁻¹ • (x + x'), x' - x⟫ := by
  simp only [norm_sq_plane, inner_plane, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

/-- **A hyperbolic strip is contained in a slab.**  Since
`(‖y - x‖ - ‖y - x'‖)(‖y - x‖ + ‖y - x'‖) = 2⟪y - m, x' - x⟫`, a bound on the difference of the
distances bounds the distance of `y` to the perpendicular bisector, by the same factor divided
by `‖x - x'‖`.  No co-area inequality and no change of variables: the identity does the work. -/
theorem abs_inner_le_of_abs_dist_sub_lt {x x' y : Plane} {δ M : ℝ}
    (hsum : ‖y - x‖ + ‖y - x'‖ ≤ M) (hδ : |dist x y - dist x' y| < δ) (hδ0 : 0 < δ) :
    |⟪y - (2 : ℝ)⁻¹ • (x + x'), x' - x⟫| ≤ δ * M / 2 := by
  have hfac : (‖y - x‖ - ‖y - x'‖) * (‖y - x‖ + ‖y - x'‖)
      = 2 * ⟪y - (2 : ℝ)⁻¹ • (x + x'), x' - x⟫ := by
    rw [← norm_sq_sub_norm_sq]; ring
  have hdd : |‖y - x‖ - ‖y - x'‖| < δ := by
    rwa [dist_eq_norm, dist_eq_norm, norm_sub_rev x y, norm_sub_rev x' y] at hδ
  have hnn : (0 : ℝ) ≤ ‖y - x‖ + ‖y - x'‖ := by positivity
  have habs : |2 * ⟪y - (2 : ℝ)⁻¹ • (x + x'), x' - x⟫|
      = |‖y - x‖ - ‖y - x'‖| * (‖y - x‖ + ‖y - x'‖) := by
    rw [← hfac, abs_mul, abs_of_nonneg hnn]
  have hbound : |2 * ⟪y - (2 : ℝ)⁻¹ • (x + x'), x' - x⟫| ≤ δ * M := by
    rw [habs]
    exact mul_le_mul hdd.le hsum hnn hδ0.le
  rw [abs_mul, abs_two] at hbound
  linarith

/-- Coordinates on the plane, as a volume-preserving map from `ℝ × ℝ`. -/
def coordPlane (p : ℝ × ℝ) : Plane := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)) ![p.1, p.2]

theorem measurePreserving_coordPlane :
    MeasurePreserving coordPlane (volume : Measure (ℝ × ℝ)) (volume : Measure Plane) := by
  have h1 : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := ℝ)).symm
      (volume : Measure (ℝ × ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm _
  have h2 : MeasurePreserving (@WithLp.toLp 2 (Fin 2 → ℝ))
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure Plane) :=
    PiLp.volume_preserving_toLp (Fin 2)
  exact h2.comp h1

theorem coordPlane_apply_zero (p : ℝ × ℝ) : coordPlane p 0 = p.1 := rfl
theorem coordPlane_apply_one (p : ℝ × ℝ) : coordPlane p 1 = p.2 := rfl



/-- The closed version of the chart sublevel estimate. -/
theorem volume_setOf_abs_linear_le (α β c : ℝ) (hβ : β ≠ 0) :
    volume {a : ℝ | |α + a * β| ≤ c} ≤ ENNReal.ofReal (2 * c / |β|) := by
  have habs : (0 : ℝ) < |β| := abs_pos.2 hβ
  set m : ℝ := -α / β with hm
  set w : ℝ := c / |β| with hw
  have hsub : {a : ℝ | |α + a * β| ≤ c} ⊆ Set.Icc (m - w) (m + w) := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    have key : |a - m| ≤ w := by
      have hmul : |a - m| * |β| = |α + a * β| := by
        rw [← abs_mul, hm]; congr 1; field_simp; ring
      rw [hw, le_div_iff₀ habs, hmul]; exact ha
    rw [abs_le] at key
    exact ⟨by linarith [key.1], by linarith [key.2]⟩
  refine le_trans (measure_mono hsub) ?_
  rw [Real.volume_Icc]
  apply ENNReal.ofReal_le_ofReal
  rw [hw]; field_simp; ring_nf; rfl

/-- **A slab meets a ball in small area.**  In the plane, the points of the ball of radius `R`
lying within `h` of a line have area at most `8 R h`.

The proof transfers to the product measure by the volume-preserving coordinate map, picks
whichever coordinate carries at least half of the normal, and integrates the one-dimensional
sublevel estimate over the other. -/
theorem volume_slab_inter_ball_le {e : Plane} (he : ‖e‖ = 1) (c R h : ℝ)
    (hR : 0 ≤ R) (hh : 0 ≤ h) :
    volume {y : Plane | ‖y‖ ≤ R ∧ |⟪y, e⟫ - c| ≤ h} ≤ ENNReal.ofReal (8 * R * h) := by
  have hsq : e 0 ^ 2 + e 1 ^ 2 = 1 := by rw [← norm_sq_plane, he]; norm_num
  set S : Set Plane := {y : Plane | ‖y‖ ≤ R ∧ |⟪y, e⟫ - c| ≤ h} with hS
  have hSmeas : MeasurableSet S := by
    refine MeasurableSet.inter (measurableSet_le continuous_norm.measurable measurable_const) ?_
    have hg : Measurable fun y : Plane => |⟪y, e⟫ - c| :=
      continuous_abs.measurable.comp ((measurable_projNormal e).sub measurable_const)
    exact measurableSet_le hg measurable_const
  rw [← (measurePreserving_coordPlane).measure_preimage hSmeas.nullMeasurableSet]
  have hpre : coordPlane ⁻¹' S
      ⊆ {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧ |p.1 * e 0 + p.2 * e 1 - c| ≤ h} := by
    rintro p ⟨hn, hin⟩
    have hnorm : (coordPlane p) 0 ^ 2 + (coordPlane p) 1 ^ 2 ≤ R ^ 2 := by
      rw [← norm_sq_plane]
      nlinarith [norm_nonneg (coordPlane p)]
    rw [coordPlane_apply_zero, coordPlane_apply_one] at hnorm
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]; constructor <;> nlinarith [sq_nonneg p.2]
    · rw [abs_le]; constructor <;> nlinarith [sq_nonneg p.1]
    · rw [inner_plane, coordPlane_apply_zero, coordPlane_apply_one] at hin; exact hin
  refine le_trans (measure_mono hpre) ?_
  rcases le_or_gt (1 / Real.sqrt 2) |e 0| with h0 | h0
  · -- the first coordinate carries the normal: section in it
    have hne : e 0 ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at h0
      have : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
      linarith
    have hlow : Real.sqrt 2 * |e 0| ≥ 1 := by
      have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
      rw [ge_iff_le, ← div_le_iff₀' h2]
      simpa [one_div] using h0
    have hmeas : MeasurableSet {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧
        |p.1 * e 0 + p.2 * e 1 - c| ≤ h} := by
      refine MeasurableSet.inter (measurableSet_le (continuous_abs.measurable.comp
        measurable_fst) measurable_const) (MeasurableSet.inter
        (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const) ?_)
      exact measurableSet_le (continuous_abs.measurable.comp
        (((measurable_fst.mul measurable_const).add
          (measurable_snd.mul measurable_const)).sub measurable_const)) measurable_const
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      Measure.prod_apply_symm hmeas]
    have hsec : ∀ v : ℝ, volume ((fun u : ℝ => (u, v)) ⁻¹'
        {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧ |p.1 * e 0 + p.2 * e 1 - c| ≤ h})
        ≤ (Set.Icc (-R) R).indicator (fun _ => ENNReal.ofReal (2 * Real.sqrt 2 * h)) v := by
      intro v
      by_cases hv : v ∈ Set.Icc (-R) R
      · rw [Set.indicator_of_mem hv]
        have hsub : (fun u : ℝ => (u, v)) ⁻¹' {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧
            |p.1 * e 0 + p.2 * e 1 - c| ≤ h}
            ⊆ {u : ℝ | |(v * e 1 - c) + u * e 0| ≤ h} := by
          intro u hu
          simp only [Set.mem_setOf_eq]
          have heq : |(v * e 1 - c) + u * e 0| = |u * e 0 + v * e 1 - c| := by
            congr 1; ring
          rw [heq]
          exact hu.2.2
        refine le_trans (measure_mono hsub) ?_
        refine le_trans (volume_setOf_abs_linear_le (v * e 1 - c) (e 0) h hne) ?_
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (abs_pos.2 hne)]
        nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
          abs_nonneg (e 0), hh]
      · rw [Set.indicator_of_notMem hv]
        refine le_of_eq ?_
        convert measure_empty (μ := (volume : Measure ℝ))
        ext u
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, hv2, -⟩
        exact hv (abs_le.1 hv2)
    calc ∫⁻ v, volume ((fun u : ℝ => (u, v)) ⁻¹' _)
        ≤ ∫⁻ v, (Set.Icc (-R) R).indicator (fun _ => ENNReal.ofReal (2 * Real.sqrt 2 * h)) v :=
          lintegral_mono hsec
      _ = ENNReal.ofReal (2 * Real.sqrt 2 * h) * volume (Set.Icc (-R) R) := by
          rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
      _ ≤ ENNReal.ofReal (8 * R * h) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have ht : Real.sqrt 2 ≤ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
          nlinarith [mul_nonneg hR hh, ht, hR, hh]
  · -- the second coordinate carries the normal
    have he1 : 1 / Real.sqrt 2 ≤ |e 1| := by
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hs2 : (0:ℝ) < Real.sqrt 2 := by positivity
      have hinv : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by rw [div_pow, one_pow, h2]
      have hlt : e 0 ^ 2 < 1 / 2 := by
        nlinarith [abs_nonneg (e 0), sq_abs (e 0), h0, hinv]
      have hge : (1 / 2 : ℝ) < e 1 ^ 2 := by nlinarith [hsq]
      rw [div_le_iff₀ hs2]
      nlinarith [abs_nonneg (e 1), sq_abs (e 1), h2, hs2, hge]
    have hne : e 1 ≠ 0 := by
      intro hz
      rw [hz, abs_zero] at he1
      have : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
      linarith
    have hkey : (1:ℝ) ≤ |e 1| * Real.sqrt 2 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < Real.sqrt 2)] at he1
      exact he1
    have hmeas : MeasurableSet {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧
        |p.1 * e 0 + p.2 * e 1 - c| ≤ h} := by
      refine MeasurableSet.inter (measurableSet_le (continuous_abs.measurable.comp
        measurable_fst) measurable_const) (MeasurableSet.inter
        (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const) ?_)
      exact measurableSet_le (continuous_abs.measurable.comp
        (((measurable_fst.mul measurable_const).add
          (measurable_snd.mul measurable_const)).sub measurable_const)) measurable_const
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      Measure.prod_apply hmeas]
    have hsec : ∀ u : ℝ, volume (Prod.mk u ⁻¹'
        {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧ |p.1 * e 0 + p.2 * e 1 - c| ≤ h})
        ≤ (Set.Icc (-R) R).indicator (fun _ => ENNReal.ofReal (2 * Real.sqrt 2 * h)) u := by
      intro u
      by_cases hu : u ∈ Set.Icc (-R) R
      · rw [Set.indicator_of_mem hu]
        have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | |p.1| ≤ R ∧ |p.2| ≤ R ∧
            |p.1 * e 0 + p.2 * e 1 - c| ≤ h}
            ⊆ {v : ℝ | |(u * e 0 - c) + v * e 1| ≤ h} := by
          intro v hv
          simp only [Set.mem_setOf_eq]
          have heq : |(u * e 0 - c) + v * e 1| = |u * e 0 + v * e 1 - c| := by
            congr 1; ring
          rw [heq]
          exact hv.2.2
        refine le_trans (measure_mono hsub) ?_
        refine le_trans (volume_setOf_abs_linear_le (u * e 0 - c) (e 1) h hne) ?_
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (abs_pos.2 hne)]
        nlinarith [hkey, hh, abs_nonneg (e 1), Real.sqrt_nonneg 2]
      · rw [Set.indicator_of_notMem hu]
        refine le_of_eq ?_
        convert measure_empty (μ := (volume : Measure ℝ))
        ext v
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hv1, -, -⟩
        exact hu (abs_le.1 hv1)
    calc ∫⁻ u, volume (Prod.mk u ⁻¹' _)
        ≤ ∫⁻ u, (Set.Icc (-R) R).indicator (fun _ => ENNReal.ofReal (2 * Real.sqrt 2 * h)) u :=
          lintegral_mono hsec
      _ = ENNReal.ofReal (2 * Real.sqrt 2 * h) * volume (Set.Icc (-R) R) := by
          rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
      _ ≤ ENNReal.ofReal (8 * R * h) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have ht : Real.sqrt 2 ≤ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
          nlinarith [mul_nonneg hR hh, ht, hR, hh]



/-- **The hyperbolic strip area bound, proved.**  Inside the ball of radius `R`, the pins whose
distances to `x` and to `x'` differ by less than `δ` occupy area at most `16 R² δ / ‖x - x'‖`.

The strip is contained in a slab: the difference of the squared distances is affine, so
`(‖y - x‖ - ‖y - x'‖)(‖y - x‖ + ‖y - x'‖) = 2⟪y - m, x' - x⟫`, and a bound on the difference
bounds the distance of `y` to the perpendicular bisector.  The slab then meets the ball in area
`O(R · width)`. -/
theorem volume_strip_le {R : ℝ} (hR : 0 ≤ R) (x x' : Plane) (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R)
    {δ : ℝ} (hδ : 0 < δ) :
    volume {y : Plane | ‖y‖ ≤ R ∧ |dist x y - dist x' y| < δ}
      ≤ ENNReal.ofReal (16 * R ^ 2 * δ) / ENNReal.ofReal ‖x - x'‖ := by
  rcases eq_or_ne (‖x - x'‖) 0 with hz | hz
  · rcases eq_or_lt_of_le hR with hR0 | hRpos
    · have hzero : volume {y : Plane | ‖y‖ ≤ R ∧ |dist x y - dist x' y| < δ} = 0 := by
        refine measure_mono_null (fun y hy => ?_) (measure_singleton (0 : Plane))
        rw [← hR0] at hy
        simpa using norm_le_zero_iff.1 hy.1
      rw [hzero]
      exact zero_le'
    · have hnum : ENNReal.ofReal (16 * R ^ 2 * δ) ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
        positivity
      rw [hz, ENNReal.ofReal_zero, ENNReal.div_zero hnum]
      exact le_top
  · have hρ : (0:ℝ) < ‖x - x'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hxx : x' ≠ x := fun h => hz (by rw [h, sub_self, norm_zero])
    have hρ' : ‖x' - x‖ = ‖x - x'‖ := norm_sub_rev _ _
    set e : Plane := radialProj x x' with he
    have hen : ‖e‖ = 1 := norm_radialProj x hxx
    have hsmul : x' - x = ‖x - x'‖ • e := by
      rw [he, radialProj, smul_smul, hρ', mul_inv_cancel₀ hρ.ne', one_smul]
    set m : Plane := (2 : ℝ)⁻¹ • (x + x') with hm
    have hsub : {y : Plane | ‖y‖ ≤ R ∧ |dist x y - dist x' y| < δ}
        ⊆ {y : Plane | ‖y‖ ≤ R ∧ |⟪y, e⟫ - ⟪m, e⟫| ≤ 2 * R * δ / ‖x - x'‖} := by
      rintro y ⟨hy, hd⟩
      refine ⟨hy, ?_⟩
      have hM : ‖y - x‖ + ‖y - x'‖ ≤ 4 * R := by
        have h1 : ‖y - x‖ ≤ 2 * R := le_trans (norm_sub_le y x) (by linarith)
        have h2 : ‖y - x'‖ ≤ 2 * R := le_trans (norm_sub_le y x') (by linarith)
        linarith
      have hkey := abs_inner_le_of_abs_dist_sub_lt hM hd hδ
      rw [hsmul, real_inner_smul_right, abs_mul, abs_of_pos hρ, inner_sub_left] at hkey
      rw [le_div_iff₀ hρ]
      calc |⟪y, e⟫ - ⟪m, e⟫| * ‖x - x'‖ = ‖x - x'‖ * |⟪y, e⟫ - ⟪m, e⟫| := by ring
        _ ≤ δ * (4 * R) / 2 := hkey
        _ = 2 * R * δ := by ring
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (volume_slab_inter_ball_le hen ⟪m, e⟫ R (2 * R * δ / ‖x - x'‖) hR
      (by positivity)) ?_
    rw [← ENNReal.ofReal_div_of_pos hρ]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
    ring

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


/-- **The almost-every-pin theorem.**  A probability measure carried by the ball of radius `R`
with finite Riesz `1`-energy has a pin in that ball whose pinned distance set has positive
length; in fact almost every pin works.

A Frostman exponent above one gives finite `1`-energy, so this applies to every set of Hausdorff
dimension above one.  Contrast Theorem 1.1, which asks for the pin to lie inside the set: that
is what needs Orponen's theorem, and it is still open here. -/
theorem exists_pin_ball_of_energy (μ : Measure Plane) [IsProbabilityMeasure μ]
    {E : Set Plane} (hμE : 0 < μ E) {R : ℝ} (hR : 0 < R)
    (hcar : μ {x : Plane | ‖x‖ ≤ R}ᶜ = 0) (hen : rieszEnergy μ 1 ≠ ⊤) :
    ∃ y, ‖y‖ ≤ R ∧ 0 < volume (pinnedDistances E y) := by
  set B : Set Plane := {y : Plane | ‖y‖ ≤ R} with hB
  have hBeq : B = Metric.closedBall (0 : Plane) R := by
    ext y; simp [hB, Metric.mem_closedBall, dist_eq_norm]
  have hBmeas : MeasurableSet B := measurableSet_le continuous_norm.measurable measurable_const
  have hBpos : 0 < volume B := by rw [hBeq]; exact Metric.measure_closedBall_pos _ _ hR
  have hBtop : volume B ≠ ⊤ := by
    rw [hBeq]; exact (Metric.isBounded_closedBall.measure_lt_top).ne
  set ν : Measure Plane := normalizedRestrict volume B with hν
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_normalizedRestrict hBmeas hBpos.ne' hBtop
  have hνc : ν Bᶜ = 0 := normalizedRestrict_compl_eq_zero volume hBmeas
  set Cb : ℝ≥0∞ := (volume B)⁻¹ * ENNReal.ofReal (16 * R ^ 2) * rieszEnergy μ 1 with hCb
  have hCbtop : Cb ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hBpos.ne') ENNReal.ofReal_ne_top)
      hen
  -- the source pairs lie in the ball almost surely
  have hprod : ∀ᵐ q : Plane × Plane ∂(μ.prod μ), ‖q.1‖ ≤ R ∧ ‖q.2‖ ≤ R := by
    have h1 : (μ.prod μ) (Bᶜ ×ˢ (univ : Set Plane)) = 0 := by
      rw [Measure.prod_prod, hcar, zero_mul]
    have h2 : (μ.prod μ) ((univ : Set Plane) ×ˢ Bᶜ) = 0 := by
      rw [Measure.prod_prod, hcar, mul_zero]
    have hnull : (μ.prod μ) ((Bᶜ ×ˢ (univ : Set Plane)) ∪ ((univ : Set Plane) ×ˢ Bᶜ)) = 0 :=
      measure_union_null h1 h2
    refine measure_mono_null (fun q hq => ?_) hnull
    rcases not_and_or.1 hq with h | h
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · exact Or.inr ⟨Set.mem_univ _, h⟩
  have hkey : ∀ δ : ℝ, 0 < δ →
      (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ)) ∂ν) ≤ ENNReal.ofReal (2 * δ) * Cb := by
    intro δ hδ
    calc (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ)) ∂ν)
        = (volume B)⁻¹ * ∫⁻ y in B, (μ.prod μ) (hypTube y (2 * δ)) := by
          rw [hν, normalizedRestrict, lintegral_smul_measure]; rfl
      _ = (volume B)⁻¹ * ∫⁻ q : Plane × Plane,
            volume {y : Plane | ‖y‖ ≤ R ∧ |dist q.1 y - dist q.2 y| < 2 * δ} ∂(μ.prod μ) := by
          rw [lintegral_hypTube_restrict μ R]
      _ ≤ (volume B)⁻¹ * ∫⁻ q : Plane × Plane,
            ENNReal.ofReal (16 * R ^ 2 * (2 * δ)) / ENNReal.ofReal ‖q.1 - q.2‖ ∂(μ.prod μ) := by
          refine mul_le_mul_left' (lintegral_mono_ae ?_) _
          filter_upwards [hprod] with q hq
          exact volume_strip_le hR.le q.1 q.2 hq.1 hq.2 (by linarith)
      _ = (volume B)⁻¹ * (ENNReal.ofReal (16 * R ^ 2 * (2 * δ)) * rieszEnergy μ 1) := by
          rw [lintegral_prod_inv_norm_sub μ (16 * R ^ 2 * (2 * δ))]
      _ = ENNReal.ofReal (2 * δ) * Cb := by
          rw [hCb, show (16 : ℝ) * R ^ 2 * (2 * δ) = (16 * R ^ 2) * (2 * δ) from by ring,
            ENNReal.ofReal_mul (by positivity)]
          ring
  obtain ⟨y, hyB, hy⟩ := exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube μ ν
    hμE hνc (by rw [measure_univ]; norm_num) hCbtop
    (fun n : ℕ => (by positivity : (0:ℝ) < 1 / (n + 1)))
    tendsto_one_div_add_atTop_nhds_zero_nat
    (fun n => hkey _ (by positivity))
  exact ⟨y, hyB, hy⟩

end FalconerPacking
