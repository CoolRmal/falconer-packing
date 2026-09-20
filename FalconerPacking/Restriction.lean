/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dyadic
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

section CubeBridge

open scoped ENNReal

/-- A Frostman bound on balls gives a Frostman bound on dyadic cubes. -/
theorem measure_dyadicCube_le_of_isFrostman {μ : Measure Plane} {s C : ℝ} (hs : 0 ≤ s)
    (hfr : IsFrostman μ s C) {n : ℕ} (hn : 2 ≤ n) (k : Fin 2 → ℤ) :
    μ (dyadicCube n k) ≤ ENNReal.ofReal (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ s) := by
  rcases Set.eq_empty_or_nonempty (dyadicCube n k) with hempty | ⟨x, hx⟩
  · simp [hempty]
  set r : ℝ := 2 * Real.sqrt 2 / (2 : ℝ) ^ n with hr
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hsqrt : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hrpos : 0 < r := by positivity
  have hfour : (4 : ℝ) ≤ 2 ^ n := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := by
          exact pow_le_pow_right₀ (by norm_num) hn
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one hpow]
    linarith [hsqrt2, hfour]
  refine le_trans (measure_mono ?_) (hfr x r hrpos hr1)
  intro y hy
  refine Metric.mem_ball.2 (lt_of_le_of_lt (dist_le_of_mem_dyadicCube hy hx) ?_)
  rw [hr, div_lt_div_iff_of_pos_right hpow]
  linarith [hsqrt]

/-- A bound on the mass of the dyadic cubes of generation `n` gives a bound on the mass of balls
of radius at most `2⁻ⁿ⁻¹`: such a ball meets at most four cubes. -/
theorem measure_ball_le_of_cube_bound {μ : Measure Plane} {n : ℕ} {x : Plane} {r : ℝ}
    {M : ℝ≥0∞} (hr : 0 < r) (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1)))
    (hM : ∀ k, μ (dyadicCube n k) ≤ M) : μ (Metric.ball x r) ≤ 4 * M := by
  classical
  obtain ⟨k, hk⟩ := exists_cubeIndex_pair n x hr hrn
  have hsub : Metric.ball x r
      ⊆ ⋃ b : Fin 2 → Bool, dyadicCube n (fun i ↦ k i + if b i then 1 else 0) := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨fun i ↦ decide (cubeIndex n y i = k i + 1), ?_⟩
    refine mem_dyadicCube_iff.2 (funext fun i ↦ ?_)
    rcases hk y hy i with h | h
    · have hne : ¬ (cubeIndex n y i = k i + 1) := by omega
      simp [h, hne]
    · simp [h]
  calc μ (Metric.ball x r)
      ≤ μ (⋃ b : Fin 2 → Bool, dyadicCube n (fun i ↦ k i + if b i then 1 else 0)) :=
        measure_mono hsub
    _ ≤ ∑ b : Fin 2 → Bool, μ (dyadicCube n (fun i ↦ k i + if b i then 1 else 0)) :=
        measure_iUnion_fintype_le _ _
    _ ≤ (Finset.univ : Finset (Fin 2 → Bool)).card • M :=
        Finset.sum_le_card_nsmul _ _ _ fun b _ ↦ hM _
    _ = 4 * M := by
        simp [Finset.card_univ, nsmul_eq_mul]

end CubeBridge

end FalconerPacking
