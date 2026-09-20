/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Energy
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Radial projections and the separation estimate

Module 7 of the manuscript's ledger.  The original branch of Theorem 1.1 consumes Orponen's
radial-projection theorem in the form quoted as Theorem 3.7 of Guth–Iosevich–Ou–Wang: for
Frostman measures `μ`, `ν` with separated supports and exponents above one, the radial
projections `(Θ x)_* ν` have an `L^q` density for some `q > 1`, with `∫ ‖ρ x‖_q ^ q dμ x < ∞`.

The manuscript **cites** that theorem; it does not prove it.  This file supplies the part of
module 7 that is elementary and self-contained, and states the remaining input precisely:

* `det2`, the scalar cross product of the plane, with Lagrange's identity;
* `radialProj`, the radial projection `Θ x y = (y - x) / ‖y - x‖`, and its measurability;
* `abs_det2_le_norm_mul_dist_radialProj`, **the separation estimate**
  `|det (y - x, z - x)| ≤ ‖y - x‖ ‖z - x‖ · |Θ x y - Θ x z|`,
  which is the `sin θ ≤ 2 sin (θ / 2)` comparison underlying every radial-projection energy
  bound;
* `lineTube`, the tubes in which the estimate degenerates, in determinant form;
* `OrponenRadialProjection`, the literature input itself, stated for the `q`-th power average.

The separation estimate reduces the radial-projection energy to a triple integral against the
reciprocal determinant, and thereby to a non-concentration estimate for `μ` on tubes.  Crude
Frostman covering gives only `μ (lineTube w) ≲ w ^ (s - 1)` with `s ≤ 2`, which is one power
short of what the reciprocal integral needs; closing that gap is exactly the content of
Orponen's theorem, and needs Bourgain's discretized projection theorem.  That is why
`OrponenRadialProjection` is stated here rather than proved.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The plane, as the statement's Euclidean space. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ### The scalar cross product -/

/-- The scalar cross product `u₀ v₁ - u₁ v₀` of two planar vectors.  Its absolute value is
twice the area of the triangle they span. -/
def det2 (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

/-- The real inner product of the plane, in coordinates. -/
theorem inner_plane (u v : Plane) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- The squared norm of the plane, in coordinates. -/
theorem norm_sq_plane (u : Plane) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_plane]; ring

/-- **Lagrange's identity** in the plane: the cross product and the inner product together
recover the product of the norms. -/
theorem det2_sq_add_inner_sq (u v : Plane) :
    det2 u v ^ 2 + ⟪u, v⟫ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_plane, norm_sq_plane, norm_sq_plane, det2]; ring

theorem det2_smul_left (a : ℝ) (u v : Plane) : det2 (a • u) v = a * det2 u v := by
  simp [det2]; ring

theorem det2_smul_right (a : ℝ) (u v : Plane) : det2 u (a • v) = a * det2 u v := by
  simp [det2]; ring

theorem det2_comm (u v : Plane) : det2 u v = -det2 v u := by simp [det2]; ring

theorem det2_self (u : Plane) : det2 u u = 0 := by simp [det2]; ring

/-- Bilinearity in the second slot: the pin may be replaced by the other source point.  This is
the identity behind `|det (y - x, z - x)| = ‖y - z‖ · d (x, line y z)`, since the second factor
is now a fixed vector of length `‖y - z‖`. -/
theorem det2_sub_right (x y z : Plane) : det2 (y - x) (z - x) = det2 (y - x) (z - y) := by
  simp [det2, PiLp.sub_apply]; ring

/-! ### The radial projection -/

/-- The radial projection `Θ x y = (y - x) / ‖y - x‖` of the source point `y` from the pin `x`.
At `y = x` it is `0`, which keeps the map globally measurable. -/
def radialProj (x y : Plane) : Plane := ‖y - x‖⁻¹ • (y - x)

/-- Away from the pin the radial projection lands on the unit circle. -/
theorem norm_radialProj (x : Plane) {y : Plane} (h : y ≠ x) : ‖radialProj x y‖ = 1 := by
  have hne : ‖y - x‖ ≠ 0 := by simpa [sub_eq_zero] using h
  rw [radialProj, norm_smul]
  simp [inv_mul_cancel₀ hne]

theorem measurable_radialProj (x : Plane) : Measurable (radialProj x) := by
  have h1 : Measurable fun y : Plane => y - x := measurable_id.sub_const x
  exact (h1.norm.inv).smul h1

/-- **The separation estimate.**  The cross product of the two source displacements is a lower
bound for the distance between their radial projections, after normalizing by the two distances
to the pin.  Geometrically this is `sin θ ≤ 2 sin (θ / 2)`: the chord between two unit vectors
dominates the sine of the angle between them. -/
theorem abs_det2_le_norm_mul_dist_radialProj (x : Plane) {y z : Plane}
    (hy : y ≠ x) (hz : z ≠ x) :
    |det2 (y - x) (z - x)| ≤ ‖y - x‖ * ‖z - x‖ * dist (radialProj x y) (radialProj x z) := by
  have hyn : (0 : ℝ) < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hzn : (0 : ℝ) < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  set u := radialProj x y with hu
  set v := radialProj x z with hv
  have hun : ‖u‖ = 1 := norm_radialProj x hy
  have hvn : ‖v‖ = 1 := norm_radialProj x hz
  -- the unit-vector case
  have key : |det2 u v| ≤ dist u v := by
    have hc : ⟪u, v⟫ ≤ 1 := by simpa [hun, hvn] using real_inner_le_norm u v
    have hd : dist u v ^ 2 = 2 - 2 * ⟪u, v⟫ := by
      rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
      simp [hun, hvn, real_inner_comm u v]; ring
    have hL : det2 u v ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      have := det2_sq_add_inner_sq u v; rw [hun, hvn] at this; linarith
    have hsq : det2 u v ^ 2 ≤ dist u v ^ 2 := by
      rw [hL, hd]; nlinarith [sq_nonneg (1 - ⟪u, v⟫)]
    nlinarith [abs_nonneg (det2 u v), sq_abs (det2 u v), dist_nonneg (x := u) (y := v)]
  rw [hu, hv, radialProj, radialProj, det2_smul_left, det2_smul_right, abs_mul, abs_mul,
    abs_of_nonneg (inv_nonneg.2 hyn.le), abs_of_nonneg (inv_nonneg.2 hzn.le)] at key
  calc |det2 (y - x) (z - x)|
      = ‖y - x‖ * ‖z - x‖ * (‖y - x‖⁻¹ * (‖z - x‖⁻¹ * |det2 (y - x) (z - x)|)) := by
        field_simp
    _ ≤ ‖y - x‖ * ‖z - x‖ * dist u v := mul_le_mul_of_nonneg_left key (by positivity)

/-- The reciprocal form of the separation estimate: the radial-projection kernel is dominated
by the reciprocal determinant, weighted by the two distances to the pin.  This is the inequality
that turns the radial-projection energy into a tube count. -/
theorem inv_dist_radialProj_le (x : Plane) {y z : Plane}
    (hy : y ≠ x) (hz : z ≠ x) (hdet : det2 (y - x) (z - x) ≠ 0) :
    (dist (radialProj x y) (radialProj x z))⁻¹
      ≤ ‖y - x‖ * ‖z - x‖ / |det2 (y - x) (z - x)| := by
  have hyn : (0 : ℝ) < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have hzn : (0 : ℝ) < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hdpos : (0 : ℝ) < |det2 (y - x) (z - x)| := abs_pos.2 hdet
  have hsep := abs_det2_le_norm_mul_dist_radialProj x hy hz
  have hd : 0 < dist (radialProj x y) (radialProj x z) := by
    rcases (dist_nonneg (x := radialProj x y) (y := radialProj x z)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hsep
      simp only [mul_zero] at hsep
      exact absurd (abs_nonpos_iff.1 hsep) hdet
  rw [le_div_iff₀ hdpos]
  calc (dist (radialProj x y) (radialProj x z))⁻¹ * |det2 (y - x) (z - x)|
      ≤ (dist (radialProj x y) (radialProj x z))⁻¹ *
          (‖y - x‖ * ‖z - x‖ * dist (radialProj x y) (radialProj x z)) :=
        mul_le_mul_of_nonneg_left hsep (by positivity)
    _ = ‖y - x‖ * ‖z - x‖ := by field_simp

/-! ### Tubes and the remaining input -/

/-- The tube of width `w` around the line through `y` and `z`, written with the determinant so
that no affine-span machinery is needed: `|det (y - x, z - x)| = ‖y - z‖ · d (x, line y z)`. -/
def lineTube (y z : Plane) (w : ℝ) : Set Plane :=
  {x | |det2 (y - x) (z - x)| ≤ w * ‖y - z‖}

theorem lineTube_mono {y z : Plane} {w w' : ℝ} (h : w ≤ w') :
    lineTube y z w ⊆ lineTube y z w' := fun _ hx =>
  le_trans hx (mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem measurableSet_lineTube (y z : Plane) (w : ℝ) : MeasurableSet (lineTube y z w) := by
  have : Measurable fun x : Plane => |det2 (y - x) (z - x)| := by
    unfold det2
    fun_prop
  exact this measurableSet_Iic

/-- The cross product is bounded by the product of the norms, by Lagrange's identity. -/
theorem abs_det2_le_norm_mul_norm (u v : Plane) : |det2 u v| ≤ ‖u‖ * ‖v‖ := by
  have hL := det2_sq_add_inner_sq u v
  have h : det2 u v ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by nlinarith [sq_nonneg ⟪u, v⟫]
  nlinarith [abs_nonneg (det2 u v), sq_abs (det2 u v),
    mul_nonneg (norm_nonneg u) (norm_nonneg v)]

/-- **Close radial projections force the pin into a thin tube.**  If two source points at
distance at most `R` from the pin have radial projections within `δ`, then the pin lies in the
tube of width `R ^ 2 * δ / ‖y - z‖` around the line through them.

This is the form in which the separation estimate is used: a lower bound on the tube widths that
`μ` must charge, hence the non-concentration estimate that Orponen's theorem supplies. -/
theorem mem_lineTube_of_dist_radialProj_le {x y z : Plane} {R δ : ℝ}
    (hy : y ≠ x) (hz : z ≠ x) (hyz : y ≠ z)
    (hyR : ‖y - x‖ ≤ R) (hzR : ‖z - x‖ ≤ R)
    (hδ : dist (radialProj x y) (radialProj x z) ≤ δ) :
    x ∈ lineTube y z (R ^ 2 * δ / ‖y - z‖) := by
  have hyzn : (0 : ℝ) < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hyz)
  have hδ0 : 0 ≤ δ := le_trans dist_nonneg hδ
  have hsep := abs_det2_le_norm_mul_dist_radialProj x hy hz
  have hR : (0 : ℝ) ≤ R := le_trans (norm_nonneg _) hyR
  show |det2 (y - x) (z - x)| ≤ R ^ 2 * δ / ‖y - z‖ * ‖y - z‖
  rw [div_mul_cancel₀ _ hyzn.ne']
  refine hsep.trans ?_
  have h1 : ‖y - x‖ * ‖z - x‖ ≤ R ^ 2 := by nlinarith [norm_nonneg (y - x), norm_nonneg (z - x)]
  nlinarith [dist_nonneg (x := radialProj x y) (y := radialProj x z),
    mul_nonneg (norm_nonneg (y - x)) (norm_nonneg (z - x))]

/-- Arclength on the unit circle, pushed forward to the plane, so that densities of radial
projections can be written against a measure on `Plane` itself. -/
def circleMeasure : Measure Plane :=
  Measure.map Subtype.val (volume : Measure Plane).toSphere

/-- **Orponen's radial-projection theorem**, in the averaged form quoted as Theorem 3.7 of
Guth–Iosevich–Ou–Wang, stated as a hypothesis.

For compactly supported Frostman probabilities `μ` and `ν` with exponents above one and
positively separated supports, there is `q > 1` such that the radial projection of `ν` from
`μ`-almost every pin has an `L^q` density `ρ x`, with `∫ ‖ρ x‖_q ^ q dμ x` finite.

This is the one input of the original branch that is neither in Mathlib nor proved in the
manuscript.  Its proof runs through Bourgain's discretized projection theorem; the elementary
reduction above (`inv_dist_radialProj_le`) shows why no softer argument can work, since the
reciprocal determinant integral needs `μ (lineTube y z w) ≲ w ^ (1 + ε)`, one power more than
a planar Frostman exponent can supply. -/
def OrponenRadialProjection : Prop :=
  ∀ (μ ν : Measure Plane) (s t Cμ Cν : ℝ),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    IsFrostman μ s Cμ → IsFrostman ν t Cν → 1 < s → 1 < t →
    (∃ c > 0, ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, c ≤ dist x y) →
    ∃ q > 1, ∃ ρ : Plane → Plane → ℝ,
      (∀ᵐ x ∂μ, Measure.map (radialProj x) ν
        = circleMeasure.withDensity fun θ => ENNReal.ofReal (ρ x θ)) ∧
      (∫⁻ x, ∫⁻ θ, ENNReal.ofReal (ρ x θ) ^ q ∂circleMeasure ∂μ) ≠ ∞

end FalconerPacking
