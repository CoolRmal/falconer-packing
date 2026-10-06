/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.InheritedFineCapSupport
public import FalconerPacking.InheritedCoarseCapSupport

/-!
# Inherited circle overlap on one fixed broad annulus

The upper frequency fixes every label and spatial mark throughout the annulus.
Allowing the circle radius to be smaller by a fixed factor only changes overlap constants.
-/

@[expose] public section

noncomputable section

open Set Metric Classical

namespace FalconerPacking

/-- A fixed annular ratio still forces positive circle radius. -/
theorem circle_radius_pos_of_ratio {B R r : ℝ} (hB : 0 < B) (hR : 0 < R)
    (h : R ≤ B * r) : 0 < r := by
  by_contra hn
  have := mul_nonpos_of_nonneg_of_nonpos hB.le (le_of_not_gt hn)
  linarith

/-- Fine enclosing balls have uniformly bounded overlap over a fixed broad annulus. -/
theorem inheritedFineCapCircle_ball_overlap_ratio {S F : ℕ} (hS : 0 < S) (hSF : S ≤ F)
    {B R r a : ℝ} (hB : 0 < B) (hR : 0 < R) (hrR : R ≤ B * r) (ha : 0 < a)
    (hscale : (F : ℝ) ≤ 2 * (R * a)) (z : EuclideanSpace ℝ (Fin 2)) :
    ((fineCapLabels S F).filter (fun p ↦
      z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (100 / a))).card ≤
      Nat.ceil (200 * B + 8 * Real.pi) * Nat.ceil (200 * B + 2 * Real.pi) := by
  have hF : (0 : ℝ) < F := Nat.cast_pos.mpr (hS.trans_le hSF)
  have hr := circle_radius_pos_of_ratio hB hR hrR
  have hw : 100 / a ≤ (200 * B) * r / F := by
    rw [div_le_div_iff₀ ha hF]
    have hRa := mul_le_mul_of_nonneg_right hrR ha.le
    nlinarith
  apply (Finset.card_le_card (show (fineCapLabels S F).filter (fun p ↦
    z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (100 / a)) ⊆
      (fineCapLabels S F).filter (fun p ↦
    z ∈ ball (r • angularDirection (angularGridPoint F p.2)) ((200 * B) * r / F)) from ?_)).trans
      (fineCapLabels_ball_overlap hS hSF hr (by positivity) z)
  intro p hp
  obtain ⟨hp, hz⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, lt_of_lt_of_le hz hw⟩

/-- Coarse enclosing balls have the same fixed-ratio extension, without counting standard caps. -/
theorem inheritedCoarseCapCircle_ball_overlap_ratio {N : ℕ} (hN : 0 < N)
    {B R r a : ℝ} (hB : 0 < B) (hR : 0 < R) (hrR : R ≤ B * r) (ha : 0 < a)
    (hscale : (N : ℝ) ≤ 2 * (R * a)) (z : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun c ↦
      z ∈ ball (r • angularDirection (angularGridPoint N c)) (1000 / a))).card ≤
        Nat.ceil (2000 * B + 2 * Real.pi) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hr := circle_radius_pos_of_ratio hB hR hrR
  have hw : 1000 / a ≤ (2000 * B) * r / N := by
    rw [div_le_div_iff₀ ha hN']
    have hRa := mul_le_mul_of_nonneg_right hrR ha.le
    nlinarith
  apply (Finset.card_le_card (show (Finset.range N).filter (fun c ↦
    z ∈ ball (r • angularDirection (angularGridPoint N c)) (1000 / a)) ⊆
      (Finset.range N).filter (fun c ↦
    z ∈ ball (r • angularDirection (angularGridPoint N c)) ((2000 * B) * r / N)) from ?_)).trans
      (card_circle_grid_balls_le N hN hr (by positivity) z)
  intro c hc
  obtain ⟨hc, hz⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨hc, lt_of_lt_of_le hz hw⟩

end FalconerPacking
