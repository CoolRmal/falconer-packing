/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicRootRestriction
import FalconerPacking.CoherentBorelParameters

/-!
# Compact source and pin data for the physical packet construction

An explicit common isometry supplies coordinate separation. The actual pin probability is
then restricted to a positive compact subset of one unit dyadic cube. Frostman exponents,
covering exponents, and the coordinate gap are preserved through these operations.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The physical construction's bounded separated source and rooted pin measures can be
obtained from arbitrary separated compact Frostman probabilities. -/
theorem exists_separated_dyadic_frostman_data
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {K L : Set (EuclideanSpace ℝ (Fin 2))} {s u Cμ Cν δ₀ : ℝ}
    (hK : IsCompact K) (hL : IsCompact L)
    (hμK : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0)
    (hνL : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Lᶜ = 0)
    (hμ : IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ)
    (hν : IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) s Cν)
    (hbox : HasUpperBoxBound L u) (hδ₀ : 0 < δ₀)
    (hsep : ∀ x ∈ K, ∀ y ∈ L, δ₀ ≤ dist x y) :
    ∃ (X Y : Set (EuclideanSpace ℝ (Fin 2)))
      (μ' ν' : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
      (e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))
      (q₀ : Fin 2 → ℤ) (Cμ' Cν' δ R : ℝ),
      IsCompact X ∧ IsCompact Y ∧ X ⊆ e '' K ∧ Y ⊆ e '' L ∧
      Y ⊆ dyadicCube 0 q₀ ∧ HasUpperBoxBound Y u ∧
      (μ' : Measure (EuclideanSpace ℝ (Fin 2))) Xᶜ = 0 ∧
      (ν' : Measure (EuclideanSpace ℝ (Fin 2))) Yᶜ = 0 ∧
      1 ≤ Cμ' ∧ 1 ≤ Cν' ∧
      IsFrostman (μ' : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ' ∧
      IsFrostman (ν' : Measure (EuclideanSpace ℝ (Fin 2))) s Cν' ∧
      0 < δ ∧ 1 ≤ R ∧
      (∀ x ∈ X, ‖x‖ ≤ R) ∧ (∀ y ∈ Y, ‖y‖ ≤ R) ∧
      (∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0) := by
  have hmassK : (μ : Measure (EuclideanSpace ℝ (Fin 2))) K = 1 := by
    have h := measure_add_measure_compl (μ := (μ : Measure _)) hK.measurableSet
    simpa only [hμK, add_zero, measure_univ] using h
  have hmassL : (ν : Measure (EuclideanSpace ℝ (Fin 2))) L = 1 := by
    have h := measure_add_measure_compl (μ := (ν : Measure _)) hL.measurableSet
    simpa only [hνL, add_zero, measure_univ] using h
  obtain ⟨A, B, e, δ, R, hA, hB, hAK, hBL, hμA, hνB, hδ, _, hAR, hBR, hgap⟩ :=
    exists_positive_compacts_in_separated_chart hK hL
      (show 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) K by rw [hmassK]; exact zero_lt_one)
      (show 0 < (ν : Measure (EuclideanSpace ℝ (Fin 2))) L by rw [hmassL]; exact zero_lt_one)
      hδ₀ hsep
  let μ₁ := (normalizedRestrict (μ : Measure (EuclideanSpace ℝ (Fin 2))) A).map e
  let ν₁ := (normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2))) B).map e
  obtain ⟨hμ₁prob, hμ₁A, hμ₁fr⟩ := normalizedRestrict_map_isometry_data hA hμA hμ e
  obtain ⟨hν₁prob, hν₁B, hν₁fr⟩ := normalizedRestrict_map_isometry_data hB hνB hν e
  haveI : IsProbabilityMeasure μ₁ := hμ₁prob
  haveI : IsProbabilityMeasure ν₁ := hν₁prob
  obtain ⟨Y, q₀, ν', Cν', hY, hYB, hYroot, hYbox, hν'Y, hν'fr⟩ :=
    exists_frostman_probability_in_dyadicRoot (⟨ν₁, inferInstance⟩ : ProbabilityMeasure _)
      (hB.image e.continuous) hν₁B hν₁fr ((hbox.mono hBL).image_isometryEquiv e)
  refine ⟨e '' A, Y, ⟨μ₁, inferInstance⟩, ν', e, q₀,
    max (Cμ / ((μ : Measure _) A).toReal) 1, max Cν' 1, δ, max R 1,
    hA.image e.continuous, hY, image_mono hAK, hYB.trans (image_mono hBL),
    hYroot, hYbox, hμ₁A, hν'Y, le_max_right _ _, le_max_right _ _,
    hμ₁fr.mono_constant (le_max_left _ _), hν'fr.mono_constant (le_max_left _ _),
    hδ, le_max_right _ _, ?_, ?_, ?_⟩
  · exact fun x hx ↦ (hAR x hx).trans (le_max_left _ _)
  · exact fun y hy ↦ (hBR y (hYB hy)).trans (le_max_left _ _)
  · exact fun y hy x hx ↦ hgap x hx y (hYB hy)

end FalconerPacking
