/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dyadic
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Hausdorff content

The first step towards Frostman's lemma, which Mathlib does not have: the `s`-dimensional
Hausdorff *content* is the infimum of `∑ diam ^ s` over countable covers with **no** constraint
on the diameters.

The content is dominated by the measure, and — the direction the construction needs — a set of
vanishing content is null for the Hausdorff measure.  So a set of positive `s`-dimensional
measure has positive `s`-content, which is the hypothesis of the Frostman construction.
-/

noncomputable section

open EMetric MeasureTheory Set
open scoped ENNReal NNReal

namespace FalconerPacking

/-- The cost of a single set: its diameter to the power `d`, and zero for the empty set. -/
def contentCost (d : ℝ) (s : Set (EuclideanSpace ℝ (Fin 2))) : ℝ≥0∞ := ⨆ _ : s.Nonempty, Metric.ediam s ^ d

@[simp] theorem contentCost_empty (d : ℝ) : contentCost d (∅ : Set (EuclideanSpace ℝ (Fin 2))) = 0 := by
  simp [contentCost]

/-- The `d`-dimensional Hausdorff content, as an outer measure: countable covers with **no**
constraint on the diameters. -/
def hausdorffContent (d : ℝ) : MeasureTheory.OuterMeasure (EuclideanSpace ℝ (Fin 2)) :=
  MeasureTheory.OuterMeasure.ofFunction (contentCost d) (contentCost_empty d)

theorem hausdorffContent_apply (d : ℝ) (A : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffContent d A
      = ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (_ : A ⊆ ⋃ n, t n), ∑' n, contentCost d (t n) :=
  MeasureTheory.OuterMeasure.ofFunction_apply _ _ _

theorem hausdorffContent_le_contentCost (d : ℝ) (A : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffContent d A ≤ contentCost d A :=
  MeasureTheory.OuterMeasure.ofFunction_le _

theorem hausdorffContent_le_of_cover {d : ℝ} {A : Set (EuclideanSpace ℝ (Fin 2))} {t : ℕ → Set (EuclideanSpace ℝ (Fin 2))}
    (ht : A ⊆ ⋃ n, t n) : hausdorffContent d A ≤ ∑' n, contentCost d (t n) := by
  rw [hausdorffContent_apply]
  exact iInf_le_of_le t (iInf_le _ ht)

/-- Each piece of an efficient cover is small: its diameter is controlled by the total cost. -/
theorem ediam_le_of_tsum_le {d : ℝ} {t : ℕ → Set (EuclideanSpace ℝ (Fin 2))} {ε : ℝ≥0∞} (n : ℕ)
    (hne : (t n).Nonempty) (h : ∑' m, contentCost d (t m) ≤ ε) :
    Metric.ediam (t n) ^ d ≤ ε := by
  refine le_trans (le_trans ?_ (ENNReal.le_tsum n)) h
  exact le_iSup (fun _ : (t n).Nonempty ↦ Metric.ediam (t n) ^ d) hne

/-- **Vanishing content forces vanishing measure.**  Given a cover of total cost below `ε`, every
piece has diameter at most `ε ^ (1 / d)`, so the cover is admissible for the `r`-truncated
Hausdorff measure once `ε` is small. -/
theorem hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero {d : ℝ} (hd : 0 < d)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (h : hausdorffContent d A = 0) : μH[d] A = 0 := by
  refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hεpos _ ↦ ?_)
  have hε : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hεpos
  rw [zero_add, MeasureTheory.Measure.hausdorffMeasure_apply]
  refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
  set δ : ℝ≥0∞ := min ε (r ^ d) with hδ
  have hrd : (0 : ℝ≥0∞) < r ^ d := by
    rcases eq_or_ne r ⊤ with rfl | hne
    · rw [ENNReal.top_rpow_of_pos hd]
      exact ENNReal.zero_lt_top
    · exact ENNReal.rpow_pos hr hne
  have hδpos : 0 < δ := lt_min hε hrd
  have hlt : hausdorffContent d A < δ := by rw [h]; exact hδpos
  rw [hausdorffContent_apply, iInf_lt_iff] at hlt
  obtain ⟨t, ht⟩ := hlt
  rw [iInf_lt_iff] at ht
  obtain ⟨hcov, hcost⟩ := ht
  have hsmall : ∀ n, Metric.ediam (t n) ≤ r := by
    intro n
    rcases Set.eq_empty_or_nonempty (t n) with hempty | hne
    · rw [hempty, Metric.ediam_empty]
      exact bot_le
    · have hle : Metric.ediam (t n) ^ d ≤ r ^ d :=
        le_trans (ediam_le_of_tsum_le n hne hcost.le) (min_le_right _ _)
      by_contra hcon
      rw [not_le] at hcon
      exact absurd hle (not_le.2 (ENNReal.rpow_lt_rpow hcon hd))
  refine le_trans (iInf_le_of_le t (iInf_le_of_le hcov (iInf_le _ hsmall))) ?_
  exact le_trans hcost.le (min_le_left _ _)

/-- A set of positive Hausdorff measure has positive Hausdorff content: the hypothesis of the
Frostman construction. -/
theorem hausdorffContent_pos {d : ℝ} (hd : 0 < d) {A : Set (EuclideanSpace ℝ (Fin 2))} (h : μH[d] A ≠ 0) :
    0 < hausdorffContent d A := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ hausdorffContent d A) with h0 | h0
  · exact absurd (hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero hd h0.symm) h
  · exact h0

section DyadicCover

/-- The cost of a dyadic cube, compared with its side length. -/
theorem contentCost_dyadicCube_le {d : ℝ} (hd : 0 ≤ d) (n : ℕ) (k : Fin 2 → ℤ) :
    contentCost d (dyadicCube n k)
      ≤ ENNReal.ofReal (Real.sqrt 2 ^ d) * ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) * d)) := by
  refine iSup_le fun hne ↦ ?_
  have hdiam : Metric.ediam (dyadicCube n k) ≤ ENNReal.ofReal (Real.sqrt 2 / (2 : ℝ) ^ n) := by
    refine Metric.ediam_le fun y hy z hz ↦ ?_
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (dist_le_of_mem_dyadicCube hy hz)
  refine le_trans (ENNReal.rpow_le_rpow hdiam hd) (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < Real.sqrt 2 / 2 ^ n),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.div_rpow (Real.sqrt_nonneg 2) (by positivity), ← Real.rpow_natCast (2 : ℝ) n,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (-(n : ℝ) * d) = -((n : ℝ) * d) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]

/-- **A finite dyadic cover bounds the content.**  This is the lower bound that the saturated
cubes of the Frostman construction supply. -/
theorem hausdorffContent_le_of_finset_cover {d : ℝ} (hd : 0 ≤ d) {A : Set (EuclideanSpace ℝ (Fin 2))}
    {F : Finset (ℕ × (Fin 2 → ℤ))} (hcov : A ⊆ ⋃ p ∈ F, dyadicCube p.1 p.2) :
    hausdorffContent d A
      ≤ ∑ p ∈ F, ENNReal.ofReal (Real.sqrt 2 ^ d)
          * ENNReal.ofReal ((2 : ℝ) ^ (-(p.1 : ℝ) * d)) := by
  calc hausdorffContent d A
      ≤ hausdorffContent d (⋃ p ∈ F, dyadicCube p.1 p.2) := measure_mono hcov
    _ ≤ ∑ p ∈ F, hausdorffContent d (dyadicCube p.1 p.2) :=
        measure_biUnion_finset_le F _
    _ ≤ ∑ p ∈ F, ENNReal.ofReal (Real.sqrt 2 ^ d)
          * ENNReal.ofReal ((2 : ℝ) ^ (-(p.1 : ℝ) * d)) :=
        Finset.sum_le_sum fun p _ ↦
          (hausdorffContent_le_contentCost d _).trans (contentCost_dyadicCube_le hd _ _)

end DyadicCover

end FalconerPacking
