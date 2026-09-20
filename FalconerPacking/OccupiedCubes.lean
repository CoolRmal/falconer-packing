/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.WeightMeasure
import Mathlib.Data.Finset.Pi

/-!
# Finite occupied dyadic covers

At each generation a compact planar set meets only finitely many dyadic cubes.  This file proves
the form needed by the finite Frostman construction.  It first covers the compact set by finitely
many balls of radius `2⁻ⁿ⁻¹`; each ball meets at most four generation-`n` cubes.  Empty cubes are
then discarded, allowing one point of the compact set to be selected in every remaining cube.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Half the side length of a generation-`n` dyadic cube. -/
def dyadicCoverRadius (n : ℕ) : ℝ := (2 : ℝ) ^ (-((n : ℝ) + 1))

theorem dyadicCoverRadius_pos (n : ℕ) : 0 < dyadicCoverRadius n :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- The at most four generation-`n` cube indices that can meet the small ball centered at `x`. -/
def neighboringCubeIndices (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun i ↦
    {⌊(2 : ℝ) ^ n * (x i - dyadicCoverRadius n)⌋,
      ⌊(2 : ℝ) ^ n * (x i - dyadicCoverRadius n)⌋ + 1}

theorem cubeIndex_mem_neighboringCubeIndices {n : ℕ} {x y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Metric.ball x (dyadicCoverRadius n)) :
    cubeIndex n y ∈ neighboringCubeIndices n x := by
  rw [neighboringCubeIndices, Fintype.mem_piFinset]
  intro i
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact cubeIndex_eq_lower_or_succ n x (dyadicCoverRadius_pos n) le_rfl y hy i

/-- All cube indices supplied by a finite cover by small balls. -/
def coveringCubeIndices (n : ℕ) (t : Finset (EuclideanSpace ℝ (Fin 2))) :
    Finset (Fin 2 → ℤ) :=
  t.biUnion (neighboringCubeIndices n)

/-- Discard from the finite candidate family all cubes that do not meet `K`. -/
def occupiedCubeIndices (K : Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (t : Finset (EuclideanSpace ℝ (Fin 2))) : Finset (Fin 2 → ℤ) :=
  by
    classical
    exact (coveringCubeIndices n t).filter fun k ↦ (K ∩ dyadicCube n k).Nonempty

/-- A finite cover by the small balls yields a cover by the occupied candidate cubes. -/
theorem subset_iUnion_occupiedCubeIndices {K : Set (EuclideanSpace ℝ (Fin 2))} {n : ℕ}
    {t : Finset (EuclideanSpace ℝ (Fin 2))}
    (hcover : K ⊆ ⋃ x ∈ t, Metric.ball x (dyadicCoverRadius n)) :
    K ⊆ ⋃ k ∈ occupiedCubeIndices K n t, dyadicCube n k := by
  classical
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (hcover hy)
  have hcandidate : cubeIndex n y ∈ coveringCubeIndices n t := by
    rw [coveringCubeIndices, Finset.mem_biUnion]
    exact ⟨x, hxt, cubeIndex_mem_neighboringCubeIndices hyx⟩
  have hoccupied : cubeIndex n y ∈ occupiedCubeIndices K n t := by
    rw [occupiedCubeIndices, Finset.mem_filter]
    exact ⟨hcandidate, ⟨y, hy, mem_dyadicCube_cubeIndex n y⟩⟩
  exact Set.mem_iUnion₂.2
    ⟨cubeIndex n y, hoccupied, mem_dyadicCube_cubeIndex n y⟩

/-- Compactness supplies a finite cover by balls at the dyadic covering radius. -/
theorem exists_finset_ball_cover_of_isCompact {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (n : ℕ) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin 2)),
      K ⊆ ⋃ x ∈ t, Metric.ball x (dyadicCoverRadius n) := by
  obtain ⟨t, _htK, htfinite, hcover⟩ :=
    finite_cover_balls_of_compact hK (dyadicCoverRadius_pos n)
  refine ⟨htfinite.toFinset, ?_⟩
  simpa using hcover

/-- A compact set has a finite generation-`n` dyadic cover consisting only of occupied cubes,
with one selected point of the set in each cube. -/
theorem exists_occupiedCubeIndices_and_points {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (n : ℕ) :
    ∃ (S : Finset (Fin 2 → ℤ))
      (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)),
      K ⊆ ⋃ k ∈ S, dyadicCube n k ∧
        ∀ k ∈ S, pt k ∈ K ∩ dyadicCube n k := by
  classical
  obtain ⟨t, hcover⟩ := exists_finset_ball_cover_of_isCompact hK n
  let S := occupiedCubeIndices K n t
  have hnonempty : ∀ k ∈ S, (K ∩ dyadicCube n k).Nonempty := by
    intro k hk
    have hk' : k ∈ coveringCubeIndices n t ∧ (K ∩ dyadicCube n k).Nonempty := by
      simpa only [S, occupiedCubeIndices, Finset.mem_filter] using hk
    exact hk'.2
  let pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2) := fun k ↦
    if hk : k ∈ S then Classical.choose (hnonempty k hk) else 0
  refine ⟨S, pt, subset_iUnion_occupiedCubeIndices hcover, ?_⟩
  intro k hk
  simp only [pt, dif_pos hk]
  exact Classical.choose_spec (hnonempty k hk)

/-- Combining compact discretization with the finite Frostman lemma gives normalized atomic
probability measures at every positive depth.  Their atoms lie in `K`, and they satisfy all
dyadic estimates together with the finest-scale ball estimate. -/
theorem exists_compact_weightProbabilityMeasure_estimates
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) {n : ℕ} (hn : 1 ≤ n)
    {d : ℝ} (hd : 0 ≤ d) (hcontent : 0 < hausdorffContent d K) :
    ∃ (S : Finset (Fin 2 → ℤ))
      (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
      (w : (Fin 2 → ℤ) → ℝ),
      (∀ k ∈ S, pt k ∈ K) ∧
      (∀ k ∈ S, pt k ∈ dyadicCube n k) ∧
      (∀ k, 0 ≤ w k) ∧
      0 < ∑ k' ∈ S, w k' ∧
      (∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) ∧
      (∀ i ≤ n, ∀ c,
        (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
            (dyadicCube i c) ≤
          ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (allowance i d)) ∧
      ∀ x r, 0 < r → r ≤ dyadicCoverRadius n →
        (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
            (Metric.ball x r) ≤
          ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ *
            (4 * ENNReal.ofReal (allowance n d)) := by
  obtain ⟨S, pt, hcover, hpt⟩ := exists_occupiedCubeIndices_and_points hK n
  have hptK : ∀ k ∈ S, pt k ∈ K := fun k hk ↦ (hpt k hk).1
  have hptcube : ∀ k ∈ S, pt k ∈ dyadicCube n k := fun k hk ↦ (hpt k hk).2
  obtain ⟨w, hw, hmass, hbound, hcube, hball⟩ :=
    exists_weightProbabilityMeasure_estimates S hn hd hcontent hcover pt hptcube
  exact ⟨S, pt, w, hptK, hptcube, hw, hmass, hbound, hcube, hball⟩

end FalconerPacking
