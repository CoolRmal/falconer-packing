/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AffineDistance
import FalconerPacking.OccupiedCubes

/-!
# Measurable dyadic source centers

The coherent affine construction chooses one point in every occupied source cube.  This file
turns those points into a measurable center map and records its uniform dyadic error.
-/

noncomputable section

open Set

namespace FalconerPacking

/-- Select the prescribed representative of the dyadic cube containing `x`. -/
def dyadicCenterMap (n : ℕ)
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  pt (cubeIndex n x)

/-- A function constant on each member of the countable measurable dyadic partition is
measurable, with no regularity assumption on its values. -/
theorem measurable_dyadicCenterMap (n : ℕ)
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) :
    Measurable (dyadicCenterMap n pt) := by
  intro s hs
  have hpreimage : dyadicCenterMap n pt ⁻¹' s =
      ⋃ k : Fin 2 → ℤ, ⋃ _h : pt k ∈ s, dyadicCube n k := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.2 ⟨cubeIndex n x,
        Set.mem_iUnion.2 ⟨hx, mem_dyadicCube_cubeIndex n x⟩⟩
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      obtain ⟨hpt, hxk⟩ := Set.mem_iUnion.1 hk
      change pt (cubeIndex n x) ∈ s
      rwa [mem_dyadicCube_iff.1 hxk]
  rw [hpreimage]
  exact MeasurableSet.iUnion fun k ↦
    MeasurableSet.iUnion fun _h ↦ measurableSet_dyadicCube n k

/-- Every point covered by selected occupied cubes has its own cube index in the selected
finite family. -/
theorem cubeIndex_mem_of_subset_iUnion_dyadicCube
    {K : Set (EuclideanSpace ℝ (Fin 2))} {n : ℕ}
    {S : Finset (Fin 2 → ℤ)}
    (hcover : K ⊆ ⋃ k ∈ S, dyadicCube n k)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ K) :
    cubeIndex n x ∈ S := by
  obtain ⟨k, hkS, hxk⟩ := Set.mem_iUnion₂.1 (hcover hx)
  rwa [mem_dyadicCube_iff.1 hxk]

/-- A compact set admits, at every generation, a measurable center selector taking source
points to representatives in the same occupied cube. -/
theorem exists_measurable_dyadicCenterMap_of_isCompact
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (n : ℕ) :
    ∃ c : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      Measurable c ∧
      (∀ x ∈ K, c x ∈ K) ∧
      ∀ x ∈ K, dist x (c x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  obtain ⟨S, pt, hcover, hpt⟩ := exists_occupiedCubeIndices_and_points hK n
  refine ⟨dyadicCenterMap n pt, measurable_dyadicCenterMap n pt, ?_, ?_⟩
  · intro x hx
    have hxS := cubeIndex_mem_of_subset_iUnion_dyadicCube hcover hx
    exact (hpt (cubeIndex n x) hxS).1
  · intro x hx
    have hxS := cubeIndex_mem_of_subset_iUnion_dyadicCube hcover hx
    exact dist_le_of_mem_dyadicCube
      (mem_dyadicCube_cubeIndex n x) (hpt (cubeIndex n x) hxS).2

/-- Choose the measurable source-center map coherently as a sequence in the generation.  Each
center remains in the compact source and is within the diameter of its point's dyadic cube. -/
theorem exists_measurable_dyadicCenterMap_sequence_of_isCompact
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) :
    ∃ c : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ n, Measurable (c n)) ∧
      (∀ n x, x ∈ K → c n x ∈ K) ∧
      ∀ n x, x ∈ K →
        dist x (c n x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  have hex : ∀ n, ∃ c : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      Measurable c ∧
      (∀ x ∈ K, c x ∈ K) ∧
      ∀ x ∈ K, dist x (c x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n :=
    fun n ↦ exists_measurable_dyadicCenterMap_of_isCompact hK n
  choose c hcmeas hcK hcdist using hex
  exact ⟨c, hcmeas, fun n ↦ hcK n, fun n ↦ hcdist n⟩

end FalconerPacking
