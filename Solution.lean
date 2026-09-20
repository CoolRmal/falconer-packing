/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Main

/-!
# Solution: a Hausdorff–packing criterion for self-pinned distance sets

The target theorem, in the exact form of `Challenge.lean`.  Its proof is the branch combination
of Section 4, which consumes the two analytic branches of `FalconerPacking.Branches`.
-/

open MeasureTheory

namespace FalconerPacking

/-- **The target theorem.**  Let `E ⊆ ℝ²` be Borel with `d = dimH E`.  If `1 < d ≤ 5/4` and
`dimP E < B(d)`, then some pin `y ∈ E` has a pinned distance set of positive length. -/
theorem exists_pin_volume_pinnedDistances_pos (E : Set Plane) (d : ℝ)
    (hE : MeasurableSet E) (hdimH : dimH E = ENNReal.ofReal d)
    (hd_lt : 1 < d) (hd_le : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (bound d)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) :=
  main E d hE hdimH hd_lt hd_le hpack

end FalconerPacking
