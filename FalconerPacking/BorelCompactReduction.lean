/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicContentComparison
public import FalconerPacking.CompactReduction
public import FalconerPacking.HardGapCurve

/-!
# Unconditional compact reduction for Borel sets

The dyadic capacity proof supplies the initial Frostman measure on an arbitrary Borel set.
The existing positive-mass reduction then gives separated compact source and pin measures
with the selected Frostman exponent and polynomial covering bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A Borel planar set with strict Hausdorff and packing bounds supplies separated compact
Frostman source and pin probabilities with a genuine polynomial covering bound. -/
theorem exists_separated_frostman_probabilities_of_measurableSet
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {s u : ℝ}
    (hs : 1 < s) (hu : 0 < u) (hdim : ENNReal.ofReal s < dimH E)
    (hpack : packingDim E < ENNReal.ofReal u) :
    ∃ (K L : Set (EuclideanSpace ℝ (Fin 2)))
      (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C₁ C₂ δ : ℝ),
      IsCompact K ∧ IsCompact L ∧ K ⊆ E ∧ L ⊆ E ∧
      HasUpperBoxBound K u ∧ HasUpperBoxBound L u ∧
      μ ∈ probabilityMeasuresSupportedOn K ∧ ν ∈ probabilityMeasuresSupportedOn L ∧
      IsFrostman (μ : Measure _) s C₁ ∧ IsFrostman (ν : Measure _) s C₂ ∧
      0 < δ ∧ ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y := by
  obtain ⟨A, μ₀, C, hA, hAE, hμA, hfr⟩ :=
    exists_isFrostman_probabilityMeasure_of_measurableSet hE hs hdim
  have hmass : (μ₀ : Measure _) A = 1 := by
    have hcompl : (μ₀ : Measure _) Aᶜ = 0 := hμA
    have hsum := measure_add_measure_compl (μ := (μ₀ : Measure _)) hA.measurableSet
    simpa only [hcompl, add_zero, measure_univ] using hsum
  have hpos : 0 < (μ₀ : Measure _) E :=
    (show 0 < (μ₀ : Measure _) A by rw [hmass]; exact zero_lt_one).trans_le (measure_mono hAE)
  exact exists_separated_frostman_probabilities_of_measure_pos hE
    (lt_trans zero_lt_one hs) hu hfr hpack hpos

/-- A strict hard-gap cutoff leaves Hausdorff and packing exponents strictly inside the
same cutoff, with the source exponent smaller than the packing exponent. -/
theorem exists_strict_exponents_of_hardGap_cutoff
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ}
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd' : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (hausdorffPackingBound d)) :
    ∃ s u : ℝ, 1 < s ∧ s < d ∧ s < u ∧ s ≤ 5 / 4 ∧
      ENNReal.ofReal s < dimH E ∧ packingDim E < ENNReal.ofReal u ∧
      u < hausdorffPackingBound s := by
  have hfin : packingDim E ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpack.le
  have hD : (packingDim E).toReal < hausdorffPackingBound d :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hpack
  have hdD : d ≤ (packingDim E).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hdim ▸ dimH_le_packingDim E)
  obtain ⟨s, u, hs, hsd, hDu, hu⟩ := exists_strict_exponents hd (by linarith) hD
  refine ⟨s, u, hs, hsd, hsd.trans (hdD.trans_lt hDu), hsd.le.trans hd', ?_, ?_, hu⟩
  · rw [hdim]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hsd
  · exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hDu

end FalconerPacking
