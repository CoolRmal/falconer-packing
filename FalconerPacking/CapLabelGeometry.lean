/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularGridRefinement
import FalconerPacking.SmoothAngularCaps

/-!
# Geometry and uniform overlap of actual coarse and fine cap labels

Coarse labels group whole standard caps. Fine labels are standard-cap/cell pairs
whose enlarged angular supports meet. Their enclosing frequency balls have bounded
overlap independently of both grid sizes.
-/

noncomputable section

open Set Metric Classical

namespace FalconerPacking

/-- Only geometrically incident standard-cap and fine-cell pairs are retained as labels. -/
def fineCapLabels (S F : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range S) ×ˢ (Finset.range F)).filter fun p ↦
    ∃ θ ∈ angularGridCell F p.2,
      dist (angularDirection θ) (angularDirection (angularGridPoint S p.1)) < 4 * Real.pi / S

/-- Fine ancestry preserves the actual active label set and keeps the standard label fixed. -/
theorem fineCapLabels_parent_mem {S M F : ℕ} (hM : 0 < M) (hF : 0 < F)
    {p : ℕ × ℕ} (hp : p ∈ fineCapLabels S (M * F)) :
    (p.1, p.2 / M) ∈ fineCapLabels S F := by
  obtain ⟨hindex, θ, hθ, hd⟩ := Finset.mem_filter.mp hp
  have hindex' := Finset.mem_product.mp hindex
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hindex'.1, ?_⟩,
    θ, angularGridCell_refinement_subset hM hF p.2 hθ, hd⟩
  apply Finset.mem_range.mpr
  apply (Nat.div_lt_iff_lt_mul hM).mpr
  simpa only [mul_comm] using Finset.mem_range.mp hindex'.2

/-- An incident fine cell lies within six standard angular widths of its standard center. -/
theorem fineCapLabels_centers_close {S F : ℕ} (hS : 0 < S) (hSF : S ≤ F)
    {p : ℕ × ℕ} (hp : p ∈ fineCapLabels S F) :
    dist (angularDirection (angularGridPoint S p.1))
      (angularDirection (angularGridPoint F p.2)) < 6 * Real.pi / S := by
  obtain ⟨θ, hθ, hd⟩ := (Finset.mem_filter.mp hp).2
  have hf := circleGridCell_dist_le (by norm_num : (0 : ℝ) ≤ 1) hθ
  simp only [one_smul, one_mul] at hf
  have hw : 2 * Real.pi / F ≤ 2 * Real.pi / S := by
    gcongr
  calc
    _ ≤ dist (angularDirection (angularGridPoint S p.1)) (angularDirection θ) +
        dist (angularDirection θ) (angularDirection (angularGridPoint F p.2)) := dist_triangle _ _ _
    _ < 4 * Real.pi / S + 2 * Real.pi / S := by
      rw [dist_comm (angularDirection (angularGridPoint S p.1))]
      exact add_lt_add_of_lt_of_le hd (hf.trans hw)
    _ = _ := by ring

/-- Near a fine enclosing ball, every incident standard center is near at the standard scale. -/
theorem fineCapLabels_standard_ball {S F : ℕ} (hS : 0 < S) (hSF : S ≤ F)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) {p : ℕ × ℕ}
    (hp : p ∈ fineCapLabels S F) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (C * r / F)) :
    z ∈ ball (r • angularDirection (angularGridPoint S p.1))
      ((C + 6 * Real.pi) * r / S) := by
  have hd := fineCapLabels_centers_close hS hSF hp
  have hs : dist (r • angularDirection (angularGridPoint F p.2))
      (r • angularDirection (angularGridPoint S p.1)) < r * (6 * Real.pi / S) := by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr, dist_comm]
    exact mul_lt_mul_of_pos_left hd hr
  have hw : C * r / F ≤ C * r / S := by
    gcongr
  calc
    dist z _ ≤ dist z (r • angularDirection (angularGridPoint F p.2)) +
        dist (r • angularDirection (angularGridPoint F p.2)) _ := dist_triangle _ _ _
    _ < C * r / F + r * (6 * Real.pi / S) := add_lt_add hz hs
    _ ≤ C * r / S + r * (6 * Real.pi / S) := add_le_add_left hw _
    _ = _ := by ring

/-- Fine pair labels have genuinely uniform enclosing-ball overlap, not a factor of S. -/
theorem fineCapLabels_ball_overlap {S F : ℕ} (hS : 0 < S) (hSF : S ≤ F)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (z : EuclideanSpace ℝ (Fin 2)) :
    ((fineCapLabels S F).filter (fun p ↦
      z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (C * r / F))).card ≤
        Nat.ceil (C + 8 * Real.pi) * Nat.ceil (C + 2 * Real.pi) := by
  let A := (Finset.range S).filter (fun j ↦
    z ∈ ball (r • angularDirection (angularGridPoint S j)) ((C + 6 * Real.pi) * r / S))
  let B := (Finset.range F).filter (fun j ↦
    z ∈ ball (r • angularDirection (angularGridPoint F j)) (C * r / F))
  have hsub : (fineCapLabels S F).filter (fun p ↦
      z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (C * r / F)) ⊆ A ×ˢ B := by
    intro p hp
    obtain ⟨hp, hz⟩ := Finset.mem_filter.mp hp
    have hindex := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr
      ⟨hindex.1, fineCapLabels_standard_ball hS hSF hr hC hp hz⟩,
      Finset.mem_filter.mpr ⟨hindex.2, hz⟩⟩
  have hA : A.card ≤ Nat.ceil (C + 8 * Real.pi) := by
    convert card_circle_grid_balls_le S hS hr (by positivity : 0 ≤ C + 6 * Real.pi) z using 1
    congr 1
    ring
  have hB : B.card ≤ Nat.ceil (C + 2 * Real.pi) :=
    card_circle_grid_balls_le F (hS.trans_le hSF) hr hC z
  exact (Finset.card_le_card hsub).trans (by rw [Finset.card_product]; exact Nat.mul_le_mul hA hB)

/-- A direction in a standard cap lies within a fixed enlargement of its nominal coarse ancestor. -/
theorem standardCap_coarse_direction_bound {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (j : ℕ) {v : EuclideanSpace ℝ (Fin 2)}
    (hv : dist v (angularDirection (angularGridPoint (M * N) j)) < 4 * Real.pi / (M * N)) :
    dist v (angularDirection (angularGridPoint N (j / M))) < 6 * Real.pi / N := by
  have hw : 4 * Real.pi / (M * N) ≤ 4 * Real.pi / N := by
    gcongr
    exact_mod_cast (Nat.le_mul_of_pos_left N hM)
  calc
    _ ≤ dist v (angularDirection (angularGridPoint (M * N) j)) +
        dist (angularDirection (angularGridPoint (M * N) j))
          (angularDirection (angularGridPoint N (j / M))) := dist_triangle _ _ _
    _ < 4 * Real.pi / N + 2 * Real.pi / N :=
      add_lt_add_of_lt_of_le (hv.trans_le hw) (angularGridDirection_ancestor_bound hM hN j)
    _ = _ := by ring

/-- Coarse labels use one ball per nominal ancestor, with a uniform bound independent of
how many whole standard caps were grouped into each ancestor. -/
theorem coarseCapLabels_ball_overlap {N : ℕ} (hN : 0 < N) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (z : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun j ↦
      z ∈ ball (r • angularDirection (angularGridPoint N j))
        ((6 * Real.pi + C) * r / N))).card ≤ Nat.ceil (8 * Real.pi + C) := by
  convert card_circle_grid_balls_le N hN hr (by positivity : 0 ≤ 6 * Real.pi + C) z using 1
  congr 1
  ring

end FalconerPacking
