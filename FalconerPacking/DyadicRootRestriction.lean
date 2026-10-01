/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SeparatedBallMeasures
import FalconerPacking.RegularPartitionInitialLoss

/-!
# Positive compact pin measures in one unit dyadic cube

A countable unit-cube partition followed by inner regularity supplies the root required
by finite regularization. Restriction preserves the covering exponent and changes only
the Frostman constant. All previously established support geometry is preserved by inclusion.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A positive compact set has a positive compact subset in one literal unit dyadic cube. -/
theorem exists_positive_compact_in_dyadicRoot
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hμK : 0 < μ K) :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))) (q : Fin 2 → ℤ),
      IsCompact A ∧ A ⊆ K ∧ A ⊆ dyadicCube 0 q ∧ 0 < μ A := by
  obtain ⟨q, hq⟩ : ∃ q : Fin 2 → ℤ, 0 < μ (K ∩ dyadicCube 0 q) := by
    by_contra h
    have hz : ∀ q : Fin 2 → ℤ, μ (K ∩ dyadicCube 0 q) = 0 := by
      simpa only [not_exists, not_lt, nonpos_iff_eq_zero] using h
    have hcover : K ⊆ ⋃ q : Fin 2 → ℤ, K ∩ dyadicCube 0 q := by
      intro x hx
      exact mem_iUnion.mpr ⟨cubeIndex 0 x, hx, mem_dyadicCube_cubeIndex 0 x⟩
    have hzero := (measure_mono hcover).trans_eq (measure_iUnion_null hz)
    exact (not_le_of_gt hμK) hzero
  obtain ⟨A, hA, hAsub, hμA⟩ := exists_isCompact_subset_of_measure_pos
    (hK.measurableSet.inter (measurableSet_dyadicCube 0 q)) hq
  exact ⟨A, q, hA, hAsub.trans inter_subset_left, hAsub.trans inter_subset_right, hμA⟩

/-- A compact Frostman probability of controlled covering exponent yields the same data
in one unit dyadic cube, with the same exponents. -/
theorem exists_frostman_probability_in_dyadicRoot
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s u C : ℝ}
    (hK : IsCompact K) (hnull : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0)
    (hfr : IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s C)
    (hbox : HasUpperBoxBound K u) :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))) (q : Fin 2 → ℤ)
      (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C' : ℝ),
      IsCompact A ∧ A ⊆ K ∧ A ⊆ dyadicCube 0 q ∧ HasUpperBoxBound A u ∧
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) Aᶜ = 0 ∧
      IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) s C' := by
  have hmass : (μ : Measure (EuclideanSpace ℝ (Fin 2))) K = 1 := by
    have h := measure_add_measure_compl (μ := (μ : Measure _)) hK.measurableSet
    simpa only [hnull, add_zero, measure_univ] using h
  obtain ⟨A, q, hA, hAK, hAq, hμA⟩ := exists_positive_compact_in_dyadicRoot hK
    (show 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) K by rw [hmass]; exact zero_lt_one)
  let ν := normalizedRestrict (μ : Measure (EuclideanSpace ℝ (Fin 2))) A
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_normalizedRestrict
    hA.measurableSet hμA.ne' (measure_ne_top _ _)
  refine ⟨A, q, ⟨ν, inferInstance⟩, C / ((μ : Measure _) A).toReal,
    hA, hAK, hAq, hbox.mono hAK, ?_, ?_⟩
  · change ν Aᶜ = 0
    dsimp [ν]
    rw [normalizedRestrict_apply _ _ _ hA.measurableSet.compl]
    simp
  · exact isFrostman_normalizedRestrict hfr hμA.ne' (measure_ne_top _ _)

end FalconerPacking
