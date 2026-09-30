/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AffineDistance
import FalconerPacking.OccupiedCubes
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measurable dyadic source centers

The coherent affine construction chooses one point in every occupied source cube.  This file
turns those points into a measurable center map and records its uniform dyadic error.
-/

noncomputable section

open MeasureTheory Set

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

/-- For probability measures carried by separated compact sets, the dyadic center sequence
satisfies the source-cell and center-pin estimates almost everywhere for the product law. -/
theorem exists_measurable_dyadicCenterMap_sequence_ae_geometry
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hL : IsCompact L)
    (hμK : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0)
    (hνL : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Lᶜ = 0)
    {δ : ℝ} (hseparated : ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y) :
    ∃ c : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      (∀ n, Measurable (c n)) ∧
      ∀ n,
        (∀ᵐ p ∂((ν.prod μ : ProbabilityMeasure
          (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) :
            Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
          dist p.2 (c n p.2) ≤ Real.sqrt 2 / (2 : ℝ) ^ n) ∧
        (∀ᵐ p ∂((ν.prod μ : ProbabilityMeasure
          (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) :
            Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
          δ ≤ dist (c n p.2) p.1) := by
  obtain ⟨c, hcmeas, hcK, hcdist⟩ :=
    exists_measurable_dyadicCenterMap_sequence_of_isCompact hK
  have hμmem : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))), x ∈ K := by
    rw [ae_iff]
    exact hμK
  have hνmem : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))), y ∈ L := by
    rw [ae_iff]
    exact hνL
  have hpairs : ∀ᵐ p ∂((ν.prod μ : ProbabilityMeasure
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
      p.1 ∈ L ∧ p.2 ∈ K := by
    rw [ProbabilityMeasure.toMeasure_prod]
    apply (Measure.ae_prod_iff_ae_ae (hL.measurableSet.prod hK.measurableSet)).mpr
    filter_upwards [hνmem] with y hy
    filter_upwards [hμmem] with x hx
    exact ⟨hy, hx⟩
  refine ⟨c, hcmeas, fun n ↦ ⟨?_, ?_⟩⟩
  · filter_upwards [hpairs] with p hp
    exact hcdist n p.2 hp.2
  · filter_upwards [hpairs] with p hp
    exact hseparated (c n p.2) (hcK n p.2 hp.2) p.1 hp.1

end FalconerPacking
