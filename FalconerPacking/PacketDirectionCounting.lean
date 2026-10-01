/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularGridGeometry
import FalconerPacking.CircleCapGeometry
import FalconerPacking.RadialAngleGeometry

/-!
# Counting standard packet directions through a separated pair

A small transverse component places an axis near one of the two normalized pair directions.
The actual angular grid then gives a count linear in grid size times transverse width.
-/

noncomputable section

open Set Metric Classical
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The angular axis and its normal give the actual orthogonal coordinate decomposition. -/
theorem angularDirection_decompose (θ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    z = ⟪angularDirection θ, z⟫ • angularDirection θ +
      ⟪angularDirection (θ + Real.pi / 2), z⟫ • angularDirection (θ + Real.pi / 2) := by
  have hunit := Real.cos_sq_add_sin_sq θ
  have hc (i : Fin 2) (hi : i = 0 ∨ i = 1) :
      z i = (⟪angularDirection θ, z⟫ • angularDirection θ +
        ⟪angularDirection (θ + Real.pi / 2), z⟫ •
          angularDirection (θ + Real.pi / 2)) i := by
    rcases hi with rfl | rfl <;>
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply,
        Fin.sum_univ_two, Real.inner_apply, angularDirection_apply_zero,
        angularDirection_apply_one, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] <;>
      nlinarith [congrArg (fun t : ℝ ↦ t * z 0) hunit,
        congrArg (fun t : ℝ ↦ t * z 1) hunit]
  ext i
  exact hc i (by fin_cases i <;> simp)

/-- Either orientation of an axis is quantitatively close to the normalized pair direction. -/
theorem angularDirection_close_of_transverse
    (θ : ℝ) {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0) :
    ‖NormedSpace.normalize z - angularDirection θ‖ ≤
        2 * |⟪angularDirection (θ + Real.pi / 2), z⟫| / ‖z‖ ∨
    ‖NormedSpace.normalize z + angularDirection θ‖ ≤
        2 * |⟪angularDirection (θ + Real.pi / 2), z⟫| / ‖z‖ := by
  let a := ⟪angularDirection θ, z⟫
  let b := ⟪angularDirection (θ + Real.pi / 2), z⟫
  have hu := norm_angularDirection θ
  have he := angularDirection_decompose θ z
  have hres : ‖z - a • angularDirection θ‖ = |b| := by
    have hx : z - a • angularDirection θ = b • angularDirection (θ + Real.pi / 2) := by
      apply sub_eq_iff_eq_add.mpr
      simpa only [add_comm] using he
    rw [hx, norm_smul, Real.norm_eq_abs, norm_angularDirection, mul_one]
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnormalized : NormedSpace.normalize (angularDirection θ) = angularDirection θ := by
    simp only [NormedSpace.normalize, hu, inv_one, one_smul]
  by_cases ha : a = 0
  · left
    have habs : ‖z‖ = |b| := by simpa only [ha, zero_smul, sub_zero] using hres
    calc
      _ ≤ ‖NormedSpace.normalize z‖ + ‖angularDirection θ‖ := norm_sub_le _ _
      _ = 2 := by rw [NormedSpace.norm_normalize hz, hu]; norm_num
      _ = _ := by rw [← habs]; field_simp
  · have hp : a • angularDirection θ ≠ 0 :=
      smul_ne_zero ha (norm_ne_zero_iff.mp (by rw [hu]; norm_num))
    have h := norm_normalize_sub_le hp (v := z)
    rw [hres] at h
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · right
      rw [NormedSpace.normalize_smul_of_neg hneg, hnormalized, sub_neg_eq_add] at h
      exact (le_div_iff₀ hnorm).mpr (by simpa only [mul_comm] using h)
    · left
      rw [NormedSpace.normalize_smul_of_pos hpos, hnormalized] at h
      exact (le_div_iff₀ hnorm).mpr (by simpa only [mul_comm] using h)

/-- The actual grid has only linearly many axes with a small transverse component. -/
theorem card_transverse_angularGrid_le {N : ℕ} (hN : 0 < N)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : z ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (((Finset.range N).filter (fun k ↦
      |⟪angularDirection (angularGridPoint N k + Real.pi / 2), z⟫| ≤ ε)).card : ℝ) ≤
      4 * ε * N / ‖z‖ + 4 * Real.pi := by
  let ρ := 2 * ε / ‖z‖
  let v := NormedSpace.normalize z
  let P := (Finset.range N).filter (fun k ↦
    angularDirection (angularGridPoint N k) ∈ closedBall v ρ)
  let Q := (Finset.range N).filter (fun k ↦
    angularDirection (angularGridPoint N k) ∈ closedBall (-v) ρ)
  let I := (Finset.range N).filter (fun k ↦
    |⟪angularDirection (angularGridPoint N k + Real.pi / 2), z⟫| ≤ ε)
  have hρ : 0 ≤ ρ := by positivity
  have hsub : I ⊆ P ∪ Q := by
    intro k hk
    obtain ⟨hk, ht⟩ := Finset.mem_filter.mp hk
    have hb : 2 * |⟪angularDirection (angularGridPoint N k + Real.pi / 2), z⟫| / ‖z‖ ≤
        ρ := by dsimp only [ρ]; gcongr
    rcases angularDirection_close_of_transverse (angularGridPoint N k) hz with hp | hq
    · apply Finset.mem_union.mpr
      apply Or.inl
      refine Finset.mem_filter.mpr ⟨hk, ?_⟩
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hp.trans hb
    · apply Finset.mem_union.mpr
      apply Or.inr
      refine Finset.mem_filter.mpr ⟨hk, ?_⟩
      simpa only [mem_closedBall, dist_eq_norm, sub_neg_eq_add, add_comm] using hq.trans hb
  have hc (W : Finset ℕ) (u : EuclideanSpace ℝ (Fin 2))
      (hW : W ⊆ Finset.range N)
      (hmem : ∀ k ∈ W, angularDirection (angularGridPoint N k) ∈ closedBall u ρ) :
      (W.card : ℝ) ≤ ρ * N + 2 * Real.pi := by
    simpa only [one_smul, div_one] using card_circle_grid_centers_le hN
      (by norm_num : (0 : ℝ) < 1) hρ u W hW (fun k hk ↦ by simpa only [one_smul] using hmem k hk)
  have hp := hc P v (Finset.filter_subset _ _) (fun _ hk ↦ (Finset.mem_filter.mp hk).2)
  have hq := hc Q (-v) (Finset.filter_subset _ _) (fun _ hk ↦ (Finset.mem_filter.mp hk).2)
  have hcard : (I.card : ℝ) ≤ P.card + Q.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le P Q)
  change (I.card : ℝ) ≤ _
  calc
    _ ≤ 2 * (ρ * N + 2 * Real.pi) := by linarith
    _ = _ := by dsimp only [ρ]; ring

end FalconerPacking
