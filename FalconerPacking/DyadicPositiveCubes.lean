/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicMomentCenters

/-!
# Finite families of all positive-mass dyadic cubes

A finite geometric cover contains every positive-mass cube. Removing null cubes gives the
actual finite partition used for the positive affine approximation, with the same card bound.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Every positive-mass cube occurs in a finite cube cover of a conull source. -/
theorem mem_cube_cover_of_measure_pos
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : μ Kᶜ = 0)
    {n : ℕ} {I : Finset (Fin 2 → ℤ)}
    (hcover : K ⊆ ⋃ k ∈ I, dyadicCube n k)
    {k : Fin 2 → ℤ} (hk : 0 < μ (dyadicCube n k)) : k ∈ I := by
  by_contra hnot
  have hsub : dyadicCube n k ⊆ Kᶜ := by
    intro x hx hxK
    have hxI := cubeIndex_mem_of_subset_iUnion_dyadicCube hcover hxK
    exact hnot (by simpa only [mem_dyadicCube_iff.mp hx] using hxI)
  exact hk.not_ge ((measure_mono hsub).trans_eq hK)

/-- A source with an upper box bound has finitely many positive-mass cubes at each scale. -/
theorem exists_positive_mass_cube_family
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u : ℝ}
    (hK : μ Kᶜ = 0) (hbox : HasUpperBoxBound K u) :
    ∃ (C : ℝ) (I : ℕ → Finset (Fin 2 → ℤ)), 0 < C ∧
      (∀ n k, k ∈ I n ↔ 0 < μ (dyadicCube n k)) ∧
      (∀ n, ((I n).card : ℝ) ≤ 4 * C * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) ∧
      ∀ n, ∀ᵐ x ∂μ, cubeIndex n x ∈ I n := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_occupiedCubeIndices_card_le_of_hasUpperBoxBound hbox
  choose J hJ hcard using hcover
  let I (n : ℕ) := (J n).filter (fun k ↦ 0 < μ (dyadicCube n k))
  have hI (n : ℕ) (k : Fin 2 → ℤ) : k ∈ I n ↔ 0 < μ (dyadicCube n k) := by
    refine ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun hk ↦ ?_⟩
    exact Finset.mem_filter.mpr ⟨mem_cube_cover_of_measure_pos μ hK (hJ n) hk, hk⟩
  refine ⟨C, I, hC, hI, ?_, ?_⟩
  · intro n
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hcard n)
  · intro n
    exact (ae_measure_dyadicCube_pos μ n).mono fun x hx ↦ (hI n _).mpr hx

/-- Normalized restrictions remain in their source cube almost everywhere. -/
theorem ae_mem_dyadicCube_normalizedRestrict
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (k : Fin 2 → ℤ) :
    ∀ᵐ x ∂normalizedRestrict μ (dyadicCube n k), x ∈ dyadicCube n k := by
  rw [ae_iff]
  change normalizedRestrict μ (dyadicCube n k) (dyadicCube n k)ᶜ = 0
  rw [normalizedRestrict_apply _ _ _ (measurableSet_dyadicCube n k).compl]
  simp

/-- A normalized child source lies within its parent-square diameter of any child center. -/
theorem ae_dist_le_normalizedRestrict_dyadicCube
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {n : ℕ} {k : Fin 2 → ℤ}
    {b : EuclideanSpace ℝ (Fin 2)} (hb : b ∈ dyadicCube n k) :
    ∀ᵐ x ∂normalizedRestrict μ (dyadicCube n k),
      dist x b ≤ Real.sqrt 2 / (2 : ℝ) ^ n :=
  (ae_mem_dyadicCube_normalizedRestrict μ n k).mono fun _ hx ↦
    dist_le_of_mem_dyadicCube hx hb

end FalconerPacking
