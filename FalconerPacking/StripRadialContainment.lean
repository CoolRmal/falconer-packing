/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialAngleChart

/-!
# Actual radial angular containment of source strips

A common narrow strip and positive coordinate separation place all source directions
in a quantitatively small interval about any witnessed direction.
-/

@[expose] public section

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- A unit strip normal controls the planar determinant using the two normal components. -/
theorem abs_planar_det_le_normal
    (n v u : EuclideanSpace ℝ (Fin 2)) (hn : ‖n‖ = 1) :
    |v 1 * u 0 - u 1 * v 0| ≤ |⟪n, u⟫| * ‖v‖ + |⟪n, v⟫| * ‖u‖ := by
  let p : EuclideanSpace ℝ (Fin 2) := !₂[-n 1, n 0]
  have hn₂ : n 0 ^ 2 + n 1 ^ 2 = 1 := by
    simpa only [hn, one_pow, Fin.sum_univ_two] using (EuclideanSpace.real_norm_sq_eq n).symm
  have hp : ‖p‖ = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq p
    simp only [p, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, neg_sq] at h
    nlinarith [norm_nonneg p]
  have hdet : v 1 * u 0 - u 1 * v 0 = ⟪n, u⟫ * ⟪p, v⟫ - ⟪n, v⟫ * ⟪p, u⟫ := by
    calc
      _ = (n 0 ^ 2 + n 1 ^ 2) * (v 1 * u 0 - u 1 * v 0) := by rw [hn₂, one_mul]
      _ = _ := by
        simp only [p, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
  rw [hdet]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hv := abs_real_inner_le_norm p v
  have hu := abs_real_inner_le_norm p u
  rw [hp, one_mul] at hv hu
  gcongr

/-- Subtracting two points in a width-`w` strip gives normal component at most `2w`. -/
theorem abs_normal_sub_le_of_common_strip
    (n c x y : EuclideanSpace ℝ (Fin 2)) {w : ℝ}
    (hx : |⟪n, x - c⟫| ≤ w) (hy : |⟪n, y - c⟫| ≤ w) :
    |⟪n, y - x⟫| ≤ 2 * w := by
  have he : ⟪n, y - x⟫ = ⟪n, y - c⟫ - ⟪n, x - c⟫ := by
    simp only [inner_sub_right]
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

/-- The strip angle bound follows from actual source/pin geometry, with no assumed cone. -/
theorem radialAngle_sub_le_of_common_strip
    {n c y x x' : EuclideanSpace ℝ (Fin 2)} {R w δ : ℝ}
    (hn : ‖n‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hyR : ‖y‖ ≤ R) (hxR : ‖x‖ ≤ R) (hxR' : ‖x'‖ ≤ R)
    (hxδ : δ ≤ (y - x) 0) (hxδ' : δ ≤ (y - x') 0)
    (hy : |⟪n, y - c⟫| ≤ w) (hx : |⟪n, x - c⟫| ≤ w)
    (hx' : |⟪n, x' - c⟫| ≤ w) :
    |radialAngle y x - radialAngle y x'| ≤ 8 * R * w / δ ^ 2 := by
  have hv : ‖y - x‖ ≤ 2 * R := (norm_sub_le y x).trans (by linarith)
  have hu : ‖y - x'‖ ≤ 2 * R := (norm_sub_le y x').trans (by linarith)
  have hnv := abs_normal_sub_le_of_common_strip n c x y hx hy
  have hnu := abs_normal_sub_le_of_common_strip n c x' y hx' hy
  have hdet := abs_planar_det_le_normal n (y - x) (y - x') hn
  have hb : |(y - x) 1 * (y - x') 0 - (y - x') 1 * (y - x) 0| ≤ 8 * R * w := by
    refine hdet.trans ?_
    calc
      _ ≤ (2 * w) * (2 * R) + (2 * w) * (2 * R) := by gcongr
      _ = _ := by ring
  exact (radialAngle_sub_le_det hδ hxδ hxδ').trans
    (div_le_div_of_nonneg_right hb (sq_nonneg δ))

/-- A single witnessed source point centers an interval containing every direction from the tube. -/
theorem radialAngle_image_subset_interval_of_common_strip
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {n c y x₀ : EuclideanSpace ℝ (Fin 2)} {R w δ : ℝ}
    (hn : ‖n‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hyR : ‖y‖ ≤ R) (hSR : ∀ x ∈ S, ‖x‖ ≤ R)
    (hSδ : ∀ x ∈ S, δ ≤ (y - x) 0)
    (hy : |⟪n, y - c⟫| ≤ w) (hS : ∀ x ∈ S, |⟪n, x - c⟫| ≤ w)
    (hx₀ : x₀ ∈ S) :
    radialAngle y '' S ⊆ Icc (radialAngle y x₀ - 8 * R * w / δ ^ 2)
      (radialAngle y x₀ + 8 * R * w / δ ^ 2) := by
  rintro _ ⟨x, hx, rfl⟩
  have h := radialAngle_sub_le_of_common_strip hn hw hδ hyR (hSR x hx) (hSR x₀ hx₀)
    (hSδ x hx) (hSδ x₀ hx₀) hy (hS x hx) (hS x₀ hx₀)
  rcases abs_le.mp h with ⟨hl, hu⟩
  exact ⟨by linarith, by linarith⟩

end FalconerPacking
