/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Energy

/-!
# Normalized restrictions

Module 4 of the implementation ledger, second half: *for a measure `σ` and a measurable set `Q`
with `0 < σ Q < ∞`, define its normalized restriction explicitly as `σ Q ⁻¹ • σ|Q`.  Every use
carries the positivity and finiteness hypotheses.*

The manuscript's two uses are recorded here: passing to a larger cube keeps the mass positive,
and a normalized restriction of a Frostman measure is again Frostman, with the constant divided
by the mass of the set.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The normalized restriction of `σ` to `Q`. -/
def normalizedRestrict (σ : Measure Plane) (Q : Set Plane) : Measure Plane :=
  (σ Q)⁻¹ • σ.restrict Q

theorem normalizedRestrict_apply (σ : Measure Plane) (Q s : Set Plane) (hs : MeasurableSet s) :
    normalizedRestrict σ Q s = (σ Q)⁻¹ * σ (s ∩ Q) := by
  rw [normalizedRestrict, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]

/-- A normalized restriction to a set of positive finite mass is a probability measure. -/
theorem isProbabilityMeasure_normalizedRestrict {σ : Measure Plane} {Q : Set Plane}
    (hQ : MeasurableSet Q) (h0 : σ Q ≠ 0) (hfin : σ Q ≠ ⊤) :
    IsProbabilityMeasure (normalizedRestrict σ Q) := by
  constructor
  rw [normalizedRestrict_apply σ Q univ MeasurableSet.univ, univ_inter,
    ENNReal.inv_mul_cancel h0 hfin]

/-- Enlarging the set keeps the mass positive: the enlarged parent of an occupied cube is
occupied. -/
theorem measure_pos_of_subset {σ : Measure Plane} {Q Q' : Set Plane} (hQQ' : Q ⊆ Q')
    (h : 0 < σ Q) : 0 < σ Q' :=
  h.trans_le (measure_mono hQQ')

/-- The conditional ball bound: a normalized restriction charges a ball by at most the original
measure of the ball, divided by the mass of the set. -/
theorem normalizedRestrict_ball_le (σ : Measure Plane) (Q : Set Plane) (x : Plane) (r : ℝ) :
    normalizedRestrict σ Q (Metric.ball x r) ≤ (σ Q)⁻¹ * σ (Metric.ball x r) := by
  rw [normalizedRestrict_apply σ Q _ Metric.isOpen_ball.measurableSet]
  exact mul_le_mul_left' (measure_mono inter_subset_left) _

/-- **The Frostman estimate survives normalization.**  A normalized restriction of an
`(s, C)`-Frostman measure to a set of positive finite mass is `(s, C / σ Q)`-Frostman. -/
theorem isFrostman_normalizedRestrict {σ : Measure Plane} {Q : Set Plane} {s C : ℝ}
    (hfr : IsFrostman σ s C) (h0 : σ Q ≠ 0) (hfin : σ Q ≠ ⊤) :
    IsFrostman (normalizedRestrict σ Q) s (C / (σ Q).toReal) := by
  intro x r hr hr1
  have hpos : 0 < (σ Q).toReal := ENNReal.toReal_pos h0 hfin
  refine (normalizedRestrict_ball_le σ Q x r).trans ?_
  refine (mul_le_mul_left' (hfr x r hr hr1) _).trans (le_of_eq ?_)
  rw [div_mul_eq_mul_div, ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hfin,
    ENNReal.div_eq_inv_mul]

end FalconerPacking
