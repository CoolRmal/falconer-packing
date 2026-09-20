/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# The statement definitions

The definitions of `Challenge.lean`, for the modular development.

The theorem is Theorem 1.1 of the manuscript *Self-pinned distance sets: a Hausdorff–packing
dimension criterion*: a planar Borel set whose Hausdorff dimension `d` lies in `(1, 5/4]` and
whose packing dimension is below the piecewise curve `bound d` has a pin `y` inside itself whose
pinned distance set has positive Lebesgue measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The pinned distance set `Δ_y(E) = {|x - y| : x ∈ E}`. -/
def pinnedDistances (E : Set (EuclideanSpace ℝ (Fin 2))) (y : EuclideanSpace ℝ (Fin 2)) : Set ℝ :=
  (fun x ↦ dist x y) '' E

/-- A polynomial covering bound at every dyadic radius, by open Euclidean balls. -/
def HasUpperBoxBound (E : Set (EuclideanSpace ℝ (Fin 2))) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ pts : Finset (EuclideanSpace ℝ (Fin 2)),
    E ⊆ ⋃ x ∈ pts, Metric.ball x ((2 : ℝ) ^ (-(n : ℝ))) ∧
      (pts.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) * s)

/-- The upper box dimension, as the infimum of the exponents with a polynomial covering
bound at the dyadic scales. -/
def upperBoxDim (E : Set (EuclideanSpace ℝ (Fin 2))) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : HasUpperBoxBound E s), ENNReal.ofReal s

/-- The packing dimension, in the standard bounded countable-cover characterization. -/
def packingDim (E : Set (EuclideanSpace ℝ (Fin 2))) : ℝ≥0∞ :=
  ⨅ (K : ℕ → Set (EuclideanSpace ℝ (Fin 2))) (_ : E ⊆ ⋃ n, K n) (_ : ∀ n, Bornology.IsBounded (K n)),
    ⨆ n, upperBoxDim (K n)

/-- The first transition point `(9 + √33) / 12`: the root above one of `3d² - 5d/2 = 2d - 1`. -/
def d0 : ℝ := (9 + Real.sqrt 33) / 12

/-- The second transition point `(5 + √97) / 12`: the positive root of `3d² - 5d/2 = 3/2`. -/
def d1 : ℝ := (5 + Real.sqrt 97) / 12

/-- The packing-dimension curve `B(d)` of the criterion, in its three branches. -/
def bound (d : ℝ) : ℝ :=
  if d ≤ d0 then 2 * d - 1
  else if d ≤ d1 then 3 * d ^ 2 - (5 / 2 : ℝ) * d
  else ((2 * d - 1) ^ 2 + Real.sqrt ((2 * d - 1) ^ 4 + 8 * d)) / 4

/-- The exponent `A(s, u)` of the finite-profile criterion. -/
def A (s u : ℝ) : ℝ :=
  (max u (3 / 2) - s) / (2 * max u (3 / 2) - 1) + (u - s) / (2 * s)

/-- **The original branch criterion** (Proposition 2.5 of the manuscript), as a hypothesis:
a planar Borel set with `dimH E > 1` and `dimP E < 2 dimH E - 1` has a pin in itself whose
pinned distance set has positive length. -/
def OriginalBranch : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin 2))) (d : ℝ), MeasurableSet E → dimH E = ENNReal.ofReal d → 1 < d →
    packingDim E < ENNReal.ofReal (2 * d - 1) →
      ∃ y ∈ E, 0 < volume (pinnedDistances E y)

/-- **The finite-profile criterion** (Theorem 3.1 of the manuscript), as a hypothesis, in the
upper-bound form: if `dimP E < t` with `d ≤ t ≤ 2` and `A d t < d - 1`, then `E` has a pin in
itself whose pinned distance set has positive length. -/
def FiniteProfileBranch : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin 2))) (d t : ℝ), MeasurableSet E → dimH E = ENNReal.ofReal d → 1 < d →
    d < 3 / 2 → packingDim E < ENNReal.ofReal t → d ≤ t → t ≤ 2 → A d t < d - 1 →
      ∃ y ∈ E, 0 < volume (pinnedDistances E y)

/-- Theorem 1.1 of the manuscript, recorded as a proposition.  It is **not** asserted here: the
challenge below is its conditional form, and the two analytic branches remain open. -/
def Target : Prop :=
  ∀ (E : Set (EuclideanSpace ℝ (Fin 2))) (d : ℝ), MeasurableSet E → dimH E = ENNReal.ofReal d →
    1 < d → d ≤ (5 / 4 : ℝ) → packingDim E < ENNReal.ofReal (bound d) →
      ∃ y ∈ E, 0 < volume (pinnedDistances E y)

end FalconerPacking
