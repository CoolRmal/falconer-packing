/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking

/-!
# Theorem 1.1 and the historical conditional branch combination

The imported library proves `FalconerPacking.exists_pin_volume_pinnedDistances_pos`, the
unconditional `B_H` theorem specified independently in `Challenge.lean`. Its full proof is in
`FalconerPacking.HausdorffPackingTheorem` and uses only the three standard axioms.
The historical conditional result for the earlier curve is retained below.
-/

open MeasureTheory

namespace FalconerPacking

/-- The historical conditional theorem (Section 4 of the earlier manuscript). Assume the original-branch
criterion and the finite-profile criterion.  Then a planar Borel set of Hausdorff dimension
`d ∈ (1, 5/4]` whose packing dimension is below the curve `bound d` has a pin inside itself whose
pinned distance set has positive Lebesgue measure. -/
theorem exists_pin_of_branches (hOrig : OriginalBranch) (hProfile : FiniteProfileBranch)
    (E : Set (EuclideanSpace ℝ (Fin 2))) (d : ℝ) (hE : MeasurableSet E) (hdimH : dimH E = ENNReal.ofReal d)
    (hd_lt : 1 < d) (hd_le : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (bound d)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) :=
  main hOrig hProfile E d hE hdimH hd_lt hd_le hpack

end FalconerPacking
