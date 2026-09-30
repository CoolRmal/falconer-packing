/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Extraction
import FalconerPacking.FrostmanLimit

/-!
# Compact source and pin measures

A finite Frostman measure giving positive mass to a Borel set of controlled packing dimension
can be restricted to two separated compact subsets with the required covering bounds. For a
compact original set, the existing compact Frostman theorem supplies the initial measure.

This module does not assert the separate Borel compact-dimension extraction theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Passing to the closure preserves a polynomial dyadic covering bound. -/
theorem HasUpperBoxBound.closure {E : Set (EuclideanSpace ℝ (Fin 2))} {u : ℝ}
    (h : HasUpperBoxBound E u) : HasUpperBoxBound (closure E) u := by
  classical
  obtain ⟨C, hC, hcover⟩ := h
  refine ⟨C * 2 ^ u, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), fun n ↦ ?_⟩
  obtain ⟨pts, hsub, hcard⟩ := hcover (n + 1)
  refine ⟨pts, ?_, ?_⟩
  · have hclosure := closure_mono hsub
    rw [pts.closure_biUnion] at hclosure
    refine hclosure.trans ?_
    intro x hx
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.1 hx
    refine mem_iUnion₂.2 ⟨p, hp, ?_⟩
    exact Metric.closedBall_subset_ball (dyadicRadius_succ_lt n)
      (Metric.closure_ball_subset_closedBall hx)
  · refine hcard.trans_eq ?_
    have heq : ((n + 1 : ℕ) : ℝ) * u = (n : ℝ) * u + u := by push_cast; ring
    rw [heq, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring

/-- Positive finite mass and a strict packing bound supply a compact positive-mass subset
with a genuine polynomial covering bound. -/
theorem exists_isCompact_subset_hasUpperBoxBound_of_measure_pos
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {u : ℝ} (hu : 0 < u)
    (hpack : packingDim E < ENNReal.ofReal u) (hμE : 0 < μ E) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact K ∧ K ⊆ E ∧ HasUpperBoxBound K u ∧ 0 < μ K := by
  obtain ⟨A, _, hdim, hμA⟩ := exists_bounded_piece_of_measure_pos hpack hμE
  have hbound := (hasUpperBoxBound_of_upperBoxDim_lt hu hdim).closure
  have hpos : 0 < μ (closure A ∩ E) :=
    hμA.trans_le (measure_mono (inter_subset_inter_left E subset_closure))
  obtain ⟨K, hK, hKA, hμK⟩ := exists_isCompact_subset_of_measure_pos
    (isClosed_closure.measurableSet.inter hE) hpos
  exact ⟨K, hK, hKA.trans inter_subset_right, hbound.mono
    (hKA.trans inter_subset_left), hμK⟩

private theorem exists_frostman_probability_on_compact_aux
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ] {s C : ℝ}
    (hfr : IsFrostman μ s C) {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hμK : 0 < μ K) :
    ∃ (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (D : ℝ),
      ν ∈ probabilityMeasuresSupportedOn K ∧ IsFrostman (ν : Measure _) s D := by
  letI := isProbabilityMeasure_normalizedRestrict hK.measurableSet hμK.ne'
    (measure_ne_top μ K)
  refine ⟨⟨normalizedRestrict μ K, inferInstance⟩, C / (μ K).toReal, ?_,
    isFrostman_normalizedRestrict hfr hμK.ne' (measure_ne_top μ K)⟩
  change normalizedRestrict μ K Kᶜ = 0
  rw [normalizedRestrict_apply μ K Kᶜ hK.measurableSet.compl]
  simp

/-- A finite Frostman measure on a Borel set with a strict packing bound yields separated
compact source and pin probabilities with the same Frostman and covering exponents. -/
theorem exists_separated_frostman_probabilities_of_measure_pos
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E)
    {s C u : ℝ} (hs : 0 < s) (hu : 0 < u) (hfr : IsFrostman μ s C)
    (hpack : packingDim E < ENNReal.ofReal u) (hμE : 0 < μ E) :
    ∃ (K L : Set (EuclideanSpace ℝ (Fin 2)))
      (μ₁ ν₁ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C₁ C₂ δ : ℝ),
      IsCompact K ∧ IsCompact L ∧ K ⊆ E ∧ L ⊆ E ∧
      HasUpperBoxBound K u ∧ HasUpperBoxBound L u ∧
      μ₁ ∈ probabilityMeasuresSupportedOn K ∧ ν₁ ∈ probabilityMeasuresSupportedOn L ∧
      IsFrostman (μ₁ : Measure _) s C₁ ∧ IsFrostman (ν₁ : Measure _) s C₂ ∧
      0 < δ ∧ ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y := by
  obtain ⟨A, hA, hAE, hbound, hμA⟩ :=
    exists_isCompact_subset_hasUpperBoxBound_of_measure_pos hE hu hpack hμE
  obtain ⟨K, L, δ, hK, hL, hKA, hLA, hμK, hμL, hδ, hsep⟩ :=
    exists_separated_compacts hs hfr hA hμA
  obtain ⟨μ₁, C₁, hμ₁K, hμ₁⟩ :=
    exists_frostman_probability_on_compact_aux hfr hK hμK
  obtain ⟨ν₁, C₂, hν₁L, hν₁⟩ :=
    exists_frostman_probability_on_compact_aux hfr hL hμL
  exact ⟨K, L, μ₁, ν₁, C₁, C₂, δ, hK, hL, hKA.trans hAE, hLA.trans hAE,
    hbound.mono hKA, hbound.mono hLA, hμ₁K, hν₁L, hμ₁, hν₁, hδ, hsep⟩

/-- The compact case of the measure extraction used in the pinned-distance theorem. -/
theorem exists_separated_frostman_probabilities_of_isCompact
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : IsCompact E) {s u : ℝ}
    (hs : 0 < s) (hu : 0 < u) (hdim : ENNReal.ofReal s < dimH E)
    (hpack : packingDim E < ENNReal.ofReal u) :
    ∃ (K L : Set (EuclideanSpace ℝ (Fin 2)))
      (μ₁ ν₁ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C₁ C₂ δ : ℝ),
      IsCompact K ∧ IsCompact L ∧ K ⊆ E ∧ L ⊆ E ∧
      HasUpperBoxBound K u ∧ HasUpperBoxBound L u ∧
      μ₁ ∈ probabilityMeasuresSupportedOn K ∧ ν₁ ∈ probabilityMeasuresSupportedOn L ∧
      IsFrostman (μ₁ : Measure _) s C₁ ∧ IsFrostman (ν₁ : Measure _) s C₂ ∧
      0 < δ ∧ ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y := by
  obtain ⟨μ, C, hμE, hfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH hE hs hdim
  have hmass : (μ : Measure _) E = 1 := by
    have hcompl : (μ : Measure _) Eᶜ = 0 := hμE
    have hsum := measure_add_measure_compl (μ := (μ : Measure _)) hE.measurableSet
    simpa [hcompl] using hsum
  exact exists_separated_frostman_probabilities_of_measure_pos hE.measurableSet hs hu hfr
    hpack (by rw [hmass]; exact zero_lt_one)

end FalconerPacking
