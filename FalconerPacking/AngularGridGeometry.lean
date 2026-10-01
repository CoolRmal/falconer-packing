/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleBallMass
import FalconerPacking.BallOverlap
import Mathlib.Order.Interval.Set.Union

/-!
# Equal angular grids and frequency-ball overlap

Half-open equal angular cells have exactly equal normalized mass. Their disjointness
and the actual circle-ball mass estimate control the overlap of frequency balls centered
at grid directions, without an assumption on the overlap.
-/

noncomputable section

open MeasureTheory Set Metric Classical
open scoped ENNReal

namespace FalconerPacking

/-- The k-th endpoint of an equal subdivision of the fixed angular chart. -/
def angularGridPoint (N k : ℕ) : ℝ := -Real.pi + (2 * Real.pi / N) * k

/-- Half-open cells assign each common endpoint to exactly one interval. -/
def angularGridCell (N k : ℕ) : Set ℝ :=
  Ioc (angularGridPoint N k) (angularGridPoint N (k + 1))

theorem angularGridPoint_step (N k : ℕ) :
    angularGridPoint N (k + 1) - angularGridPoint N k = 2 * Real.pi / N := by
  simp only [angularGridPoint, Nat.cast_add, Nat.cast_one]
  ring

theorem angularGridPoint_mono (N : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    angularGridPoint N k ≤ angularGridPoint N l := by
  dsimp only [angularGridPoint]
  gcongr

theorem angularGridCell_subset_chart {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    angularGridCell N k ⊆ Ioc (-Real.pi) Real.pi := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := angularGridPoint_mono N (Nat.zero_le k)
  have hhi := angularGridPoint_mono N (Nat.succ_le_of_lt hk)
  have hzero : angularGridPoint N 0 = -Real.pi := by simp [angularGridPoint]
  have hend : angularGridPoint N N = Real.pi := by
    dsimp only [angularGridPoint]
    rw [div_mul_cancel₀ _ hN'.ne']
    ring
  rw [hzero] at hlo
  rw [hend] at hhi
  exact fun _ hθ ↦ ⟨lt_of_le_of_lt hlo hθ.1, hθ.2.trans hhi⟩

theorem disjoint_angularGridCell (N : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (angularGridCell N k) (angularGridCell N l) := by
  apply disjoint_left.mpr
  intro θ hk hl
  rcases lt_or_gt_of_ne hkl with h | h
  · have hh := angularGridPoint_mono N (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hk.2.trans hh)) hl.1
  · have hh := angularGridPoint_mono N (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (hl.2.trans hh)) hk.1

/-- Each grid cell has its exact share of the normalized angular probability. -/
theorem radialAngularProbability_angularGridCell {N k : ℕ} (hN : 0 < N) (hk : k < N) :
    radialAngularProbability (angularGridCell N k) = ENNReal.ofReal ((N : ℝ)⁻¹) := by
  rw [radialAngularProbability, Measure.smul_apply, smul_eq_mul,
    radialAngularMeasure, Measure.restrict_apply
      (show MeasurableSet (angularGridCell N k) from measurableSet_Ioc),
    inter_eq_left.mpr (angularGridCell_subset_chart hN hk),
    angularGridCell, Real.volume_Ioc, angularGridPoint_step,
    ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  congr 1
  field_simp

theorem angularGridCell_angle_bound {N k : ℕ} {θ : ℝ}
    (hθ : θ ∈ angularGridCell N k) : |θ - angularGridPoint N k| ≤ 2 * Real.pi / N := by
  rw [abs_of_nonneg (sub_nonneg.mpr hθ.1.le)]
  have hs := angularGridPoint_step N k
  linarith [hθ.2]

/-- Arc length controls chord length without any restriction on the angles. -/
theorem norm_angularDirection_sub_le_angle (θ φ : ℝ) :
    ‖angularDirection θ - angularDirection φ‖ ≤ |θ - φ| := by
  rw [norm_angularDirection_sub]
  have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := (θ - φ) / 2))
    (by norm_num : (0 : ℝ) ≤ 2)
  simp only [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

/-- Every point of a cell is within the corresponding arc length of its grid center. -/
theorem circleGridCell_dist_le {r : ℝ} (hr : 0 ≤ r) {N k : ℕ} {θ : ℝ}
    (hθ : θ ∈ angularGridCell N k) :
    dist (r • angularDirection θ) (r • angularDirection (angularGridPoint N k)) ≤
      r * (2 * Real.pi / N) := by
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left
    ((norm_angularDirection_sub_le_angle _ _).trans (angularGridCell_angle_bound hθ)) hr

/-- The half-open cells partition the entire angular chart, including its right endpoint. -/
theorem biUnion_angularGridCell {N : ℕ} (hN : 0 < N) :
    (⋃ k ∈ Finset.range N, angularGridCell N k) = Ioc (-Real.pi) Real.pi := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun k hk ↦ angularGridCell_subset_chart hN (Finset.mem_range.mp hk)
  · have h := Ioc_subset_biUnion_Ioc N (angularGridPoint N)
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have he : angularGridPoint N N = Real.pi := by
      dsimp only [angularGridPoint]
      rw [div_mul_cancel₀ _ hN']
      ring
    rw [he] at h
    simpa only [angularGridPoint, Nat.cast_zero, mul_zero, add_zero, angularGridCell] using h

/-- Coarse endpoints are exact endpoints of every integral refinement. -/
theorem angularGridPoint_refinement {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (k : ℕ) :
    angularGridPoint (M * N) (M * k) = angularGridPoint N k := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [angularGridPoint, Nat.cast_mul]
  field_simp

/-- Every refined cell has one actual coarse ancestor; no boundary convention is omitted. -/
theorem angularGridCell_refinement_subset {M N : ℕ} (hM : 0 < M) (hN : 0 < N) (k : ℕ) :
    angularGridCell (M * N) k ⊆ angularGridCell N (k / M) := by
  have hlo := angularGridPoint_mono (M * N) (Nat.mul_div_le k M)
  have hdiv : k + 1 ≤ M * (k / M + 1) := by
    have hm := Nat.mod_lt k hM
    have he := Nat.mod_add_div k M
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hhi := angularGridPoint_mono (M * N) hdiv
  rw [angularGridPoint_refinement hM hN] at hlo hhi
  exact fun _ hθ ↦ ⟨lt_of_le_of_lt hlo hθ.1, hθ.2.trans hhi⟩

/-- Disjoint grid cells convert a frequency-ball mass bound into a count of their centers. -/
theorem card_circle_grid_centers_le {N : ℕ} (hN : 0 < N) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (z : EuclideanSpace ℝ (Fin 2))
    (I : Finset ℕ) (hI : I ⊆ Finset.range N)
    (hc : ∀ k ∈ I, r • angularDirection (angularGridPoint N k) ∈ closedBall z ρ) :
    (I.card : ℝ) ≤ ρ * N / r + 2 * Real.pi := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  let U := (fun θ ↦ r • angularDirection θ) ⁻¹'
    closedBall z (ρ + r * (2 * Real.pi / N))
  have hUm : MeasurableSet U := (by fun_prop : Measurable (fun θ ↦ r • angularDirection θ))
    isClosed_closedBall.measurableSet
  have hsub : (⋃ k ∈ I, angularGridCell N k) ⊆ U := by
    intro θ hθ
    obtain ⟨k, hk, hθ⟩ := mem_iUnion₂.mp hθ
    have hd := circleGridCell_dist_le hr.le hθ
    have hc' := mem_closedBall.mp (hc k hk)
    have ht := dist_triangle (r • angularDirection θ)
      (r • angularDirection (angularGridPoint N k)) z
    change dist (r • angularDirection θ) z ≤ ρ + r * (2 * Real.pi / N)
    linarith
  have hsum : (∑ k ∈ I, radialAngularProbability (angularGridCell N k)) =
      ENNReal.ofReal ((I.card : ℝ) / N) := by
    have he (k : ℕ) (hk : k ∈ I) :=
      radialAngularProbability_angularGridCell hN (Finset.mem_range.mp (hI hk))
    rw [Finset.sum_congr rfl he]
    simp [div_eq_mul_inv, ENNReal.ofReal_mul]
  have hmass : ENNReal.ofReal ((I.card : ℝ) / N) ≤
      ENNReal.ofReal ((ρ + r * (2 * Real.pi / N)) / r) := by
    rw [← hsum, ← measure_biUnion_finset
      (fun _ _ _ _ h ↦ disjoint_angularGridCell N h)
      (fun _ _ ↦ show MeasurableSet (angularGridCell N _) from measurableSet_Ioc)]
    apply (measure_mono hsub).trans
    have hm : Measurable (fun θ ↦ r • angularDirection θ) := by fun_prop
    have he := Measure.map_apply (μ := radialAngularProbability) hm
      (isClosed_closedBall.measurableSet : MeasurableSet
        (closedBall z (ρ + r * (2 * Real.pi / N))))
    rw [← he]
    exact normalizedCircleMeasure_closedBall_le hr (by positivity) z
  have hreal : (I.card : ℝ) / N ≤ (ρ + r * (2 * Real.pi / N)) / r :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmass
  have h := (div_le_iff₀ hN').mp hreal
  calc
    _ ≤ (ρ + r * (2 * Real.pi / N)) / r * N := h
    _ = _ := by
      field_simp

/-- Frequency balls centered on the actual angular grid have uniformly bounded overlap. -/
theorem card_circle_grid_balls_le (N : ℕ) (hN : 0 < N) {r C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (z : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun k ↦
      z ∈ ball (r • angularDirection (angularGridPoint N k)) (C * r / N))).card ≤
      Nat.ceil (C + 2 * Real.pi) := by
  let I := (Finset.range N).filter (fun k ↦
    z ∈ ball (r • angularDirection (angularGridPoint N k)) (C * r / N))
  have h := card_circle_grid_centers_le hN hr (by positivity : 0 ≤ C * r / N) z I
    (Finset.filter_subset _ _) (fun k hk ↦ by
      have hk' := (Finset.mem_filter.mp hk).2
      rw [mem_ball, dist_comm] at hk'
      exact hk'.le)
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : C * r / N * N / r + 2 * Real.pi = C + 2 * Real.pi := by
    field_simp
  rw [he] at h
  exact_mod_cast h.trans (Nat.le_ceil _)

end FalconerPacking
