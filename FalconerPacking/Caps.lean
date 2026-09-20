/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Tubes

/-!
# Radial caps and the tubes that carry them

Module 7 of the manuscript's ledger, joining `RadialProjection.lean` to `Tubes.lean`.

Orponen's theorem is a statement about the `L^q` norm of the density of a radial projection,
and the discretized form of that norm is a sum over the caps of the circle of the `q`-th powers
of the cap masses.  This file expresses a cap mass in the slab language of the tube-square
bound, which is the dictionary any attack on the theorem has to speak.

The route is purely geometric and uses no covering argument:

* `mem_pinTube_of_dist_radialProj_le` — if `Θ_x y` is within `r` of the unit direction `e` and
  `‖y - x‖ ≤ R`, then the component of `y - x` perpendicular to `e` is at most `R r`, because
  `y - x = ‖y - x‖ • Θ_x y` exactly and `e` is annihilated by its own perpendicular;
* `pinTube_subset_iUnion_slab` — a tube through a pin meets only the slabs whose indices lie in
  an explicit integer interval, and `card_tube_slabs_le` counts them as `≤ 2 w / δ + 2`;
* `measure_capPreimage_le_of_slab_bound` — hence a cap of radius `r` carries mass at most
  `(2 R r / δ + 2) M` whenever every slab carries at most `M`.

Choosing `δ ≍ R r` makes the factor `O(1)`, so the cap bound is as good as the slab bound `M`.
The tube-square estimate of `Tubes.lean` controls `M` in a second-moment sense; Orponen's
theorem is the assertion that `M` is better than that on average over the pin, and it is the
step this file does not supply.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The counterclockwise perpendicular of a planar vector. -/
def perp (v : Plane) : Plane := !₂[-(v 1), v 0]

theorem inner_perp_self (v : Plane) : ⟪v, perp v⟫ = 0 := by
  rw [inner_plane, perp]; simp; ring

theorem norm_perp (v : Plane) : ‖perp v‖ = ‖v‖ := by
  have h : ‖perp v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_plane, norm_sq_plane, perp]; simp; ring
  nlinarith [norm_nonneg (perp v), norm_nonneg v]

theorem inner_perp_left (u v : Plane) : ⟪u, perp v⟫ = -(u 0 * v 1) + u 1 * v 0 := by
  rw [inner_plane, perp]; simp

/-- The tube of half-width `w` through the pin `x` in the direction `e`. -/
def pinTube (x e : Plane) (w : ℝ) : Set Plane := {y | |⟪y - x, perp e⟫| ≤ w}

/-- **Caps pull back into tubes.**  If the radial projection of `y` from `x` is within `r` of
the unit direction `e`, and `y` is within `R` of the pin, then `y` lies in the tube through `x`
in the direction `e` of half-width `R * r`.

This is the containment `Θ_x⁻¹(cap) ∩ B(x, R) ⊆ tube`, proved without any covering argument:
the radial projection is exactly the unit vector along `y - x`, so the perpendicular component
of `y - x` is `‖y - x‖` times the perpendicular component of `Θ_x y - e`. -/
theorem mem_pinTube_of_dist_radialProj_le {x y e : Plane} {R r : ℝ}
    (he : ‖e‖ = 1) (hy : y ≠ x) (hyR : ‖y - x‖ ≤ R) (hr : dist (radialProj x y) e ≤ r) :
    y ∈ pinTube x e (R * r) := by
  have hyn : (0 : ℝ) < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hsplit : y - x = ‖y - x‖ • radialProj x y := by
    rw [radialProj, smul_smul, mul_inv_cancel₀ hyn.ne', one_smul]
  have hzero : ⟪e, perp e⟫ = 0 := inner_perp_self e
  have hkey : ⟪radialProj x y, perp e⟫ = ⟪radialProj x y - e, perp e⟫ := by
    rw [inner_sub_left, hzero, sub_zero]
  have hbound : |⟪radialProj x y, perp e⟫| ≤ r := by
    rw [hkey]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    rw [norm_perp, he, mul_one, ← dist_eq_norm]
    exact hr
  show |⟪y - x, perp e⟫| ≤ R * r
  rw [hsplit, real_inner_smul_left, abs_mul, abs_of_nonneg hyn.le]
  have hr0 : 0 ≤ r := le_trans dist_nonneg hr
  exact mul_le_mul hyR hbound (abs_nonneg _) (le_trans (norm_nonneg _) hyR)


/-- The first slab index met by a tube. -/
def tubeLo (x e : Plane) (w δ : ℝ) : ℤ := ⌊(⟪x, perp e⟫ - w) / δ⌋

/-- The last slab index met by a tube. -/
def tubeHi (x e : Plane) (w δ : ℝ) : ℤ := ⌊(⟪x, perp e⟫ + w) / δ⌋

/-- A tube through a pin is covered by the slabs of the perpendicular direction whose indices
lie in an explicit interval. -/
theorem pinTube_subset_iUnion_slab (x e : Plane) {w δ : ℝ} (hδ : 0 < δ) :
    pinTube x e w ⊆ ⋃ k ∈ Finset.Icc (tubeLo x e w δ) (tubeHi x e w δ), slab (perp e) δ k := by
  intro y hy
  have hy' : |⟪y - x, perp e⟫| ≤ w := hy
  rw [inner_sub_left, abs_le] at hy'
  simp only [Set.mem_iUnion, Finset.mem_Icc, slab, Set.mem_setOf_eq, exists_prop]
  refine ⟨slabIndex (perp e) δ y, ⟨?_, ?_⟩, rfl⟩
  · exact Int.floor_le_floor (by gcongr; linarith [hy'.1])
  · exact Int.floor_le_floor (by gcongr; linarith [hy'.2])

/-- The number of slabs a tube meets. -/
theorem card_tube_slabs_le (x e : Plane) {w δ : ℝ} (hδ : 0 < δ) (hw : 0 ≤ w) :
    ((Finset.Icc (tubeLo x e w δ) (tubeHi x e w δ)).card : ℝ) ≤ 2 * w / δ + 2 := by
  set A := ⟪x, perp e⟫ with hA
  have hlo : ((tubeLo x e w δ : ℝ)) > (A - w) / δ - 1 := by
    have := Int.lt_floor_add_one ((A - w) / δ)
    simp only [tubeLo, ← hA]
    linarith
  have hhi : ((tubeHi x e w δ : ℝ)) ≤ (A + w) / δ := by
    simpa [tubeHi, ← hA] using Int.floor_le ((A + w) / δ)
  have hle : tubeLo x e w δ ≤ tubeHi x e w δ := by
    exact Int.floor_le_floor (by gcongr; linarith)
  rw [Int.card_Icc]
  have hnn : (0 : ℤ) ≤ tubeHi x e w δ + 1 - tubeLo x e w δ := by omega
  have hz : ((tubeHi x e w δ + 1 - tubeLo x e w δ).toNat : ℤ)
      = tubeHi x e w δ + 1 - tubeLo x e w δ := Int.toNat_of_nonneg hnn
  have hcast : (((tubeHi x e w δ + 1 - tubeLo x e w δ).toNat : ℕ) : ℝ)
      = (tubeHi x e w δ : ℝ) + 1 - (tubeLo x e w δ : ℝ) := by
    calc (((tubeHi x e w δ + 1 - tubeLo x e w δ).toNat : ℕ) : ℝ)
        = ((((tubeHi x e w δ + 1 - tubeLo x e w δ).toNat : ℕ) : ℤ) : ℝ) := by norm_cast
      _ = ((tubeHi x e w δ + 1 - tubeLo x e w δ : ℤ) : ℝ) := by rw [hz]
      _ = (tubeHi x e w δ : ℝ) + 1 - (tubeLo x e w δ : ℝ) := by push_cast; ring
  rw [hcast]
  have hdiv : (A + w) / δ - (A - w) / δ = 2 * w / δ := by field_simp; ring
  linarith

/-- The mass of a tube is at most the total mass of the slabs it meets. -/
theorem measure_pinTube_le (μ : Measure Plane) (x e : Plane) {w δ : ℝ} (hδ : 0 < δ) :
    μ (pinTube x e w)
      ≤ ∑ k ∈ Finset.Icc (tubeLo x e w δ) (tubeHi x e w δ), μ (slab (perp e) δ k) := by
  refine le_trans (measure_mono (pinTube_subset_iUnion_slab x e hδ)) ?_
  exact measure_biUnion_finset_le _ _


/-- The source points seen from the pin `x` inside the cap of radius `r` around the unit
direction `e`, at distance at most `R`. -/
def capPreimage (x e : Plane) (R r : ℝ) : Set Plane :=
  {y | y ≠ x ∧ ‖y - x‖ ≤ R ∧ dist (radialProj x y) e ≤ r}

/-- **A radial cap is covered by the slabs a tube meets.**  Composing the cap-to-tube
containment with the tube-to-slab covering expresses the radial projection of a measure in the
slab language of the tube-square bound. -/
theorem measure_capPreimage_le (ν : Measure Plane) {x e : Plane} {R r δ : ℝ}
    (he : ‖e‖ = 1) (hδ : 0 < δ) :
    ν (capPreimage x e R r)
      ≤ ∑ k ∈ Finset.Icc (tubeLo x e (R * r) δ) (tubeHi x e (R * r) δ),
          ν (slab (perp e) δ k) := by
  refine le_trans (measure_mono ?_) (measure_pinTube_le ν x e hδ)
  rintro y ⟨hne, hyR, hr⟩
  exact mem_pinTube_of_dist_radialProj_le he hne hyR hr

/-- **The cap bound from a uniform slab bound.**  If every slab of the perpendicular direction
carries mass at most `M`, then the cap of radius `r` carries mass at most `(2 R r / δ + 2) M`.
Choosing `δ ≍ R r` gives the expected `O(M)`; the gain over the trivial bound has to come from
`M`, which is what the tube-square estimate controls. -/
theorem measure_capPreimage_le_of_slab_bound (ν : Measure Plane) {x e : Plane} {R r δ : ℝ}
    {M : ℝ≥0∞} (he : ‖e‖ = 1) (hδ : 0 < δ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (hM : ∀ k : ℤ, ν (slab (perp e) δ k) ≤ M) :
    ν (capPreimage x e R r) ≤ ENNReal.ofReal (2 * (R * r) / δ + 2) * M := by
  refine le_trans (measure_capPreimage_le ν he hδ) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ M fun k _ => hM k) ?_
  rw [nsmul_eq_mul]
  gcongr
  have hcard := card_tube_slabs_le x e hδ (mul_nonneg hR hr)
  calc ((Finset.Icc (tubeLo x e (R * r) δ) (tubeHi x e (R * r) δ)).card : ℝ≥0∞)
      = ENNReal.ofReal ((Finset.Icc (tubeLo x e (R * r) δ) (tubeHi x e (R * r) δ)).card : ℝ) := by
        rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * (R * r) / δ + 2) := ENNReal.ofReal_le_ofReal hcard

end FalconerPacking
