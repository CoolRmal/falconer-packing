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

/-- In the plane there are exactly four candidate dyadic cubes around a ball center. -/
theorem card_neighboringCubeIndices (n : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    (neighboringCubeIndices n x).card = 4 := by
  simp [neighboringCubeIndices]

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

/-- Passing from a finite ball cover to the occupied dyadic cubes loses a factor of at most four. -/
theorem card_occupiedCubeIndices_le (K : Set (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (t : Finset (EuclideanSpace ℝ (Fin 2))) :
    (occupiedCubeIndices K n t).card ≤ 4 * t.card := by
  classical
  calc
    (occupiedCubeIndices K n t).card ≤ (coveringCubeIndices n t).card := by
      exact Finset.card_filter_le _ _
    _ ≤ t.card * 4 := by
      apply Finset.card_biUnion_le_card_mul
      intro x hx
      rw [card_neighboringCubeIndices]
    _ = 4 * t.card := Nat.mul_comm _ _

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

/-- A polynomial dyadic ball-cover bound gives occupied dyadic-cube covers with the same
exponent and only a factor-four loss in cardinality. -/
theorem exists_occupiedCubeIndices_card_le_of_hasUpperBoxBound
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u : ℝ}
    (hK : HasUpperBoxBound K u) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ S : Finset (Fin 2 → ℤ),
      K ⊆ ⋃ k ∈ S, dyadicCube n k ∧
      (S.card : ℝ) ≤ 4 * C * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) := by
  obtain ⟨C, hC, hcover⟩ := hK
  refine ⟨C, hC, fun n ↦ ?_⟩
  obtain ⟨t, htcover, htcard⟩ := hcover (n + 1)
  let S := occupiedCubeIndices K n t
  have htcover' : K ⊆ ⋃ x ∈ t, Metric.ball x (dyadicCoverRadius n) := by
    simpa only [dyadicCoverRadius, Nat.cast_add, Nat.cast_one] using htcover
  refine ⟨S, subset_iUnion_occupiedCubeIndices htcover', ?_⟩
  have hcardNat : S.card ≤ 4 * t.card := by
    exact card_occupiedCubeIndices_le K n t
  calc
    (S.card : ℝ) ≤ 4 * (t.card : ℝ) := by exact_mod_cast hcardNat
    _ ≤ 4 * (C * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) := by
      gcongr
    _ = 4 * C * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) := by ring

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

/-- The compact finite-depth construction with a normalization constant uniform in the depth. -/
theorem exists_compact_weightProbabilityMeasure_uniform_estimates
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
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            ENNReal.ofReal (allowance i d)) ∧
      ∀ x r, 0 < r → r ≤ dyadicCoverRadius n →
        (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
            (Metric.ball x r) ≤
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            (4 * ENNReal.ofReal (allowance n d)) := by
  obtain ⟨S, pt, hcover, hpt⟩ := exists_occupiedCubeIndices_and_points hK n
  have hptK : ∀ k ∈ S, pt k ∈ K := fun k hk ↦ (hpt k hk).1
  have hptcube : ∀ k ∈ S, pt k ∈ dyadicCube n k := fun k hk ↦ (hpt k hk).2
  obtain ⟨w, hw, hmass, hbound, hcube, hball⟩ :=
    exists_weightProbabilityMeasure_uniform_estimates S hn hd hcontent hcover pt hptcube
  refine ⟨S, pt, w, hptK, hptcube, hw, hmass, hbound, hcube, ?_⟩
  simpa only [dyadicCoverRadius] using hball

/-- At a fixed depth there is a probability measure carried by `K` whose Frostman ball estimate
holds at every dyadic scale up to that depth, with a constant independent of the depth. -/
theorem exists_compact_probabilityMeasure_all_scale_estimates
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) {n : ℕ} (hn : 1 ≤ n)
    {d : ℝ} (hd : 0 ≤ d) (hcontent : 0 < hausdorffContent d K) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0 ∧
      ∀ i ≤ n, ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            (4 * ENNReal.ofReal (allowance i d)) := by
  obtain ⟨S, pt, w, hptK, _hptcube, hw, hmass, _hbound, hcube, _hball⟩ :=
    exists_compact_weightProbabilityMeasure_uniform_estimates hK hn hd hcontent
  refine ⟨weightProbabilityMeasure S pt w,
    weightProbabilityMeasure_compl_eq_zero hK.measurableSet hw hmass hptK,
    ?_⟩
  intro i hi x r hr hri
  have hball := measure_ball_le_of_cube_bound (μ :=
      (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))))
    (n := i) (x := x) (r := r)
    hr (by simpa only [dyadicCoverRadius] using hri) (hcube i hi)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hball

end FalconerPacking
