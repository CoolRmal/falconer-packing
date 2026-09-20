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

/-- The `d`-dimensional Hausdorff content: countable covers with unconstrained diameters. -/
def hausdorffContent (d : ℝ) (A : Set Plane) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set Plane) (_ : A ⊆ ⋃ n, t n),
    ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d

theorem hausdorffContent_le_of_cover {d : ℝ} {A : Set Plane} {t : ℕ → Set Plane}
    (ht : A ⊆ ⋃ n, t n) :
    hausdorffContent d A ≤ ∑' n, ⨆ _ : (t n).Nonempty, Metric.ediam (t n) ^ d :=
  iInf_le_of_le t (iInf_le _ ht)

/-- Each piece of an efficient cover is small: its diameter is controlled by the total cost. -/
theorem ediam_le_of_tsum_le {d : ℝ} (hd : 0 < d) {t : ℕ → Set Plane} {ε : ℝ≥0∞} (n : ℕ)
    (hne : (t n).Nonempty)
    (h : ∑' m, ⨆ _ : (t m).Nonempty, Metric.ediam (t m) ^ d ≤ ε) :
    Metric.ediam (t n) ^ d ≤ ε :=
  le_trans (le_trans (le_iSup (fun _ : (t n).Nonempty ↦ Metric.ediam (t n) ^ d) hne)
    (ENNReal.le_tsum n)) h

/-- **Vanishing content forces vanishing measure.**  Given a cover of total cost below `ε`, every
piece has diameter at most `ε ^ (1 / d)`, so the cover is admissible for the `r`-truncated
Hausdorff measure once `ε` is small. -/
theorem hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero {d : ℝ} (hd : 0 < d)
    {A : Set Plane} (h : hausdorffContent d A = 0) : μH[d] A = 0 := by
  refine nonpos_iff_eq_zero.1 (ENNReal.le_of_forall_pos_le_add fun ε hεpos _ ↦ ?_)
  have hε : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hεpos
  rw [zero_add]
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
  -- choose a cover cheaper than `min ε (r ^ d)`
  set δ : ℝ≥0∞ := min ε (r ^ d) with hδ
  have hrd : (0 : ℝ≥0∞) < r ^ d := by
    rcases eq_or_ne r ⊤ with rfl | hne
    · rw [ENNReal.top_rpow_of_pos hd]
      exact ENNReal.zero_lt_top
    · exact ENNReal.rpow_pos hr hne
  have hδpos : 0 < δ := lt_min hε hrd
  have hlt : hausdorffContent d A < δ := by rw [h]; exact hδpos
  rw [hausdorffContent, iInf_lt_iff] at hlt
  obtain ⟨t, ht⟩ := hlt
  rw [iInf_lt_iff] at ht
  obtain ⟨hcov, hcost⟩ := ht
  have hsmall : ∀ n, Metric.ediam (t n) ≤ r := by
    intro n
    rcases Set.eq_empty_or_nonempty (t n) with hempty | hne
    · rw [hempty, Metric.ediam_empty]
      exact bot_le
    · have hle : Metric.ediam (t n) ^ d ≤ r ^ d :=
        le_trans (ediam_le_of_tsum_le hd n hne hcost.le) (min_le_right _ _)
      by_contra hcon
      rw [not_le] at hcon
      exact absurd hle (not_le.2 (ENNReal.rpow_lt_rpow hcon hd))
  refine le_trans (iInf_le_of_le t (iInf_le_of_le hcov (iInf_le _ hsmall))) ?_
  exact le_trans hcost.le (min_le_left _ _)

/-- A set of positive Hausdorff measure has positive Hausdorff content: the hypothesis of the
Frostman construction. -/
theorem hausdorffContent_pos {d : ℝ} (hd : 0 < d) {A : Set Plane} (h : μH[d] A ≠ 0) :
    0 < hausdorffContent d A := by
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0∞) ≤ hausdorffContent d A) with h0 | h0
  · exact absurd (hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero hd h0.symm) h
  · exact h0

/-- Conversely the content never exceeds the measure. -/
theorem hausdorffContent_le_hausdorffMeasure (d : ℝ) (A : Set Plane) :
    hausdorffContent d A ≤ μH[d] A := by
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine le_iSup_of_le 1 (le_iSup_of_le (by norm_num) ?_)
  refine le_iInf fun t ↦ le_iInf fun hcov ↦ le_iInf fun _ ↦ ?_
  exact hausdorffContent_le_of_cover hcov

section DyadicContent

/-- The dyadic `d`-content: countable covers by dyadic cubes, charged by the side length. -/
def dyadicContent (d : ℝ) (A : Set Plane) : ℝ≥0∞ :=
  ⨅ (c : ℕ → ℕ × (Fin 2 → ℤ)) (_ : A ⊆ ⋃ n, dyadicCube (c n).1 (c n).2),
    ∑' n, ENNReal.ofReal ((2 : ℝ) ^ (-((c n).1 : ℝ) * d))

/-- The cost of a dyadic cube in the ordinary content, compared with its side length. -/
theorem ediam_dyadicCube_rpow_le {d : ℝ} (hd : 0 ≤ d) (n : ℕ) (k : Fin 2 → ℤ) :
    (⨆ _ : (dyadicCube n k).Nonempty, Metric.ediam (dyadicCube n k) ^ d)
      ≤ ENNReal.ofReal (Real.sqrt 2 ^ d) * ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) * d)) := by
  refine iSup_le fun hne ↦ ?_
  obtain ⟨x, hx⟩ := hne
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

/-- **The contents are comparable.**  A dyadic cover is in particular a cover, so the ordinary
content is at most `(√2) ^ d` times the dyadic content: a positive content forces every dyadic
cover to be expensive, which is the lower bound the Frostman construction needs. -/
theorem hausdorffContent_le_dyadicContent {d : ℝ} (hd : 0 ≤ d) (A : Set Plane) :
    hausdorffContent d A ≤ ENNReal.ofReal (Real.sqrt 2 ^ d) * dyadicContent d A := by
  rw [dyadicContent, ENNReal.mul_iInf_of_ne (by positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun c ↦ ?_
  rw [ENNReal.mul_iInf_of_ne (by positivity) ENNReal.ofReal_ne_top]
  refine le_iInf fun hcov ↦ ?_
  refine le_trans (hausdorffContent_le_of_cover (t := fun n ↦ dyadicCube (c n).1 (c n).2) hcov) ?_
  rw [ENNReal.tsum_mul_left.symm]
  exact ENNReal.tsum_le_tsum fun n ↦ ediam_dyadicCube_rpow_le hd _ _

end DyadicContent

end FalconerPacking
