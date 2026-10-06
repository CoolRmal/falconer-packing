/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.Extraction
public import FalconerPacking.FrostmanLimit
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Compact extraction and the remaining Borel reduction

For a σ-compact set, a strict Hausdorff-dimension inequality already holds on one compact
subset. The compact Frostman theorem then supplies a probability on that subset. A Borel set
of positive finite Hausdorff measure also contains a compact subset of positive measure.

Neither statement asserts that an arbitrary Borel set is σ-compact or that its Hausdorff
measure below its dimension is σ-finite. The general Borel compact-dimension extraction
theorem remains a separate dependency.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FalconerPacking

/-- A strict dimension bound on a σ-compact set holds on one compact subset. -/
theorem exists_isCompact_subset_lt_dimH_of_isSigmaCompact
    {X : Type*} [EMetricSpace X] {E : Set X} (hE : IsSigmaCompact E) {s : ℝ≥0∞}
    (hs : s < dimH E) : ∃ K : Set X, IsCompact K ∧ K ⊆ E ∧ s < dimH K := by
  obtain ⟨K, hK, rfl⟩ := hE
  rw [dimH_iUnion] at hs
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hs
  exact ⟨K n, hK n, subset_iUnion K n, hn⟩

/-- A σ-compact planar set carries a compactly supported Frostman probability at every
positive exponent strictly below its Hausdorff dimension. -/
theorem exists_isFrostman_probabilityMeasure_of_isSigmaCompact
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : IsSigmaCompact E) {s : ℝ}
    (hs : 0 < s) (hdim : ENNReal.ofReal s < dimH E) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2)))
      (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C : ℝ),
      IsCompact K ∧ K ⊆ E ∧ μ ∈ probabilityMeasuresSupportedOn K ∧
      IsFrostman (μ : Measure _) s C := by
  obtain ⟨K, hK, hKE, hdimK⟩ :=
    exists_isCompact_subset_lt_dimH_of_isSigmaCompact hE hdim
  obtain ⟨μ, C, hμK, hfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH hK hs hdimK
  exact ⟨K, μ, C, hK, hKE, hμK, hfr⟩

/-- Positive finite Hausdorff measure on a Borel set can be retained on a compact subset. -/
theorem exists_isCompact_subset_hausdorffMeasure_pos
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {t : ℝ}
    (hpos : 0 < μH[t] E) (hfin : μH[t] E ≠ ∞) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)), IsCompact K ∧ K ⊆ E ∧ 0 < μH[t] K := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := (μH[t]).restrict E
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hfin.lt_top⟩
  have hμE : 0 < μ E := by simpa [μ] using hpos
  obtain ⟨K, hK, hKE, hμK⟩ := exists_isCompact_subset_of_measure_pos hE hμE
  refine ⟨K, hK, hKE, ?_⟩
  simpa [μ, Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKE] using hμK

/-- A specified positive finite Hausdorff-measure piece gives a compact subset of dimension
at least the measure exponent. No finiteness below the dimension is assumed implicitly. -/
theorem exists_isCompact_subset_le_dimH_of_hausdorffMeasure
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {t : ℝ≥0}
    (hpos : 0 < μH[t] E) (hfin : μH[t] E ≠ ∞) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact K ∧ K ⊆ E ∧ (t : ℝ≥0∞) ≤ dimH K := by
  obtain ⟨K, hK, hKE, hμK⟩ := exists_isCompact_subset_hausdorffMeasure_pos hE hpos hfin
  exact ⟨K, hK, hKE, le_dimH_of_hausdorffMeasure_ne_zero hμK.ne'⟩

/-- σ-finiteness of the restricted Hausdorff measure forces the corresponding dimension
upper bound. In particular it cannot hold at an exponent strictly below `dimH E`. -/
theorem dimH_le_of_sigmaFinite_restrict_hausdorffMeasure
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (t : ℝ≥0) [SigmaFinite ((μH[t]).restrict E)] : dimH E ≤ t := by
  let μ : Measure X := (μH[t]).restrict E
  have hcover : E = ⋃ n : ℕ, spanningSets μ n ∩ E := by
    rw [← iUnion_inter, iUnion_spanningSets, univ_inter]
  rw [hcover, dimH_iUnion]
  refine iSup_le fun n ↦ dimH_le_of_hausdorffMeasure_ne_top ?_
  have hfin := measure_spanningSets_lt_top μ n
  change (μH[t]).restrict E (spanningSets μ n) < ∞ at hfin
  rw [Measure.restrict_apply (measurableSet_spanningSets μ n)] at hfin
  exact hfin.ne

/-- Hausdorff measure restricted to a set is not σ-finite below that set's dimension. -/
theorem not_sigmaFinite_restrict_hausdorffMeasure_of_lt_dimH
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {E : Set X} {t : ℝ≥0} (hdim : (t : ℝ≥0∞) < dimH E) :
    ¬ SigmaFinite ((μH[t]).restrict E) := by
  intro h
  letI := h
  exact hdim.not_ge (dimH_le_of_sigmaFinite_restrict_hausdorffMeasure E t)

end FalconerPacking
