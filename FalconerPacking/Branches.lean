/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Algebra

/-!
# The two analytic branches

The target theorem is the disjunction of two criteria, each proved in the manuscript by a
separate analytic argument.  This file records them as the interfaces the combination in
`FalconerPacking.Main` consumes; **neither is proved here**.

* `branch_original` is Proposition 2.5 of the manuscript, specialized to a pin set `F = E`:
  coherent positive linearizations on a nested spatial tree, with Orponen's radial-projection
  theorem and a fractional angular Sobolev estimate.  It covers `dimP E < 2 dimH E - 1`.
* `branch_finiteProfile` is Theorem 3.1: the finite-profile branch, through the profile
  optimization, finite regularization of the pin measure, truncated conditional energies, tube
  deletion, packet localization and the terminal wave-packet scale.  It covers `A d t < d - 1`.

Section 7 of the manuscript lists the sixteen modules a proof of these two statements needs.
The analytic inputs are Orponen, *Analysis & PDE* 12 (2019), Keleti–Shmerkin, *GAFA* 29 (2019)
and Guth–Iosevich–Ou–Wang, *Invent. Math.* 219 (2020); none is available in Mathlib.
-/

noncomputable section

open MeasureTheory

namespace FalconerPacking

/-- **Proposition 2.5** of the manuscript, with the pin set taken to be `E` itself: a planar
Borel set with `dimH E > 1` and `dimP E < 2 dimH E - 1` has a pin in itself whose pinned
distance set has positive length.  *Unproved analytic input.* -/
theorem branch_original {E : Set Plane} {d : ℝ} (hE : MeasurableSet E)
    (hdimH : dimH E = ENNReal.ofReal d) (hd : 1 < d)
    (hpack : packingDim E < ENNReal.ofReal (2 * d - 1)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  sorry

/-- **Theorem 3.1** of the manuscript, the finite-profile criterion, in the upper-bound form:
if `dimP E < t` with `d ≤ t ≤ 2` and the exponent `A d t` is below `d - 1`, then `E` has a pin in
itself whose pinned distance set has positive length.  The stated form follows from the
manuscript's `A (dimH E) (dimP E) < dimH E - 1` because `A d ·` is monotone.
*Unproved analytic input.* -/
theorem branch_finiteProfile {E : Set Plane} {d t : ℝ} (hE : MeasurableSet E)
    (hdimH : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd' : d < 3 / 2)
    (hpack : packingDim E < ENNReal.ofReal t) (hdt : d ≤ t) (ht2 : t ≤ 2)
    (hA : A d t < d - 1) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  sorry

end FalconerPacking
