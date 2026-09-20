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
# Challenge: a Hausdorff–packing criterion for self-pinned distance sets

Every transparent definition occurring in the theorem statement, and the statement itself.

The theorem is Theorem 1.1 of the manuscript *Self-pinned distance sets: a Hausdorff–packing
dimension criterion*: a planar Borel set whose Hausdorff dimension `d` lies in `(1, 5/4]` and
whose packing dimension is below the piecewise curve `bound d` has a pin `y` inside itself whose
pinned distance set has positive Lebesgue measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The Euclidean plane, with the Euclidean distance. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The pinned distance set `Δ_y(E) = {|x - y| : x ∈ E}`. -/
def pinnedDistances (E : Set Plane) (y : Plane) : Set ℝ :=
  (fun x ↦ dist x y) '' E

/-- A polynomial covering bound at every dyadic radius, by open Euclidean balls. -/
def HasUpperBoxBound (E : Set Plane) (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ pts : Finset Plane,
    E ⊆ ⋃ x ∈ pts, Metric.ball x ((2 : ℝ) ^ (-(n : ℝ))) ∧
      (pts.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) * s)

/-- The upper box dimension, as the infimum of the exponents with a polynomial covering
bound at the dyadic scales. -/
def upperBoxDim (E : Set Plane) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 ≤ s) (_ : HasUpperBoxBound E s), ENNReal.ofReal s

/-- The packing dimension, in the standard bounded countable-cover characterization. -/
def packingDim (E : Set Plane) : ℝ≥0∞ :=
  ⨅ (K : ℕ → Set Plane) (_ : E ⊆ ⋃ n, K n) (_ : ∀ n, Bornology.IsBounded (K n)),
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

/-- **The target theorem.**  Let `E ⊆ ℝ²` be Borel with `d = dimH E`.  If `1 < d ≤ 5/4` and
`dimP E < B(d)`, then some pin `y ∈ E` has a pinned distance set of positive length. -/
theorem exists_pin_volume_pinnedDistances_pos (E : Set Plane) (d : ℝ)
    (hE : MeasurableSet E) (hdimH : dimH E = ENNReal.ofReal d)
    (hd_lt : 1 < d) (hd_le : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (bound d)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  sorry

end FalconerPacking
