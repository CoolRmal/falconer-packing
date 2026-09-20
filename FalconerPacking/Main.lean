/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Algebra

/-!
# Combining the branches

Section 4 of the manuscript.  Given `1 < d ≤ 5 / 4` and `dimP E < bound d`, either the packing
dimension is already below `2 * d - 1`, and the original branch applies, or an exponent `t`
strictly between the packing dimension and the curve satisfies the finite-profile exponent
condition `A d t < d - 1`, and the finite-profile branch applies.

Both branches enter as hypotheses: this is the conditional form of Theorem 1.1, and it is what
the curve algebra of this development actually proves.
-/

noncomputable section

open MeasureTheory

namespace FalconerPacking

/-- **The conditional target theorem.**  Assume the original-branch criterion and the
finite-profile criterion.  Then a planar Borel set of Hausdorff dimension `d ∈ (1, 5/4]` whose
packing dimension is below the curve `bound d` has a pin inside itself whose pinned distance set
has positive Lebesgue measure. -/
theorem main (hOrig : OriginalBranch) (hProfile : FiniteProfileBranch)
    (E : Set Plane) (d : ℝ) (hE : MeasurableSet E) (hdimH : dimH E = ENNReal.ofReal d)
    (hd_lt : 1 < d) (hd_le : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (bound d)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  by_cases hsmall : packingDim E < ENNReal.ofReal (2 * d - 1)
  · exact hOrig E d hE hdimH hd_lt hsmall
  · rw [not_lt] at hsmall
    have hfin : packingDim E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpack.le
    have hplt : (packingDim E).toReal < bound d :=
      (ENNReal.lt_ofReal_iff_toReal_lt hfin).1 hpack
    have hpge : 2 * d - 1 ≤ (packingDim E).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 hsmall
    have ht_pack : packingDim E < ENNReal.ofReal (((packingDim E).toReal + bound d) / 2) := by
      rw [ENNReal.lt_ofReal_iff_toReal_lt hfin]; linarith
    exact hProfile E d (((packingDim E).toReal + bound d) / 2) hE hdimH hd_lt (by linarith)
      ht_pack (by linarith) (le_trans (by linarith) (bound_le_two hd_lt hd_le))
      (A_lt_sub_one hd_lt hd_le (by linarith) (by linarith))

end FalconerPacking
