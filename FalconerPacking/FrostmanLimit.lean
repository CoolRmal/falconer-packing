/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Energy
import FalconerPacking.WeakLimit

/-!
# From dyadic ball estimates to a Frostman measure

The finite tree construction and weak compactness produce a probability measure with estimates
at every dyadic scale.  This file compares an arbitrary radius with two consecutive powers of
`1 / 2` and packages the resulting estimate as `IsFrostman`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FalconerPacking

/-- The auxiliary covering radius is the next dyadic radius. -/
theorem dyadicCoverRadius_eq_dyadicRadius_succ (i : ℕ) :
    dyadicCoverRadius i = dyadicRadius (i + 1) := by
  simp only [dyadicCoverRadius, dyadicRadius]
  congr 1
  push_cast
  rfl

/-- The allowance is the `d`-th power of the corresponding dyadic radius. -/
theorem allowance_eq_dyadicRadius_rpow (i : ℕ) (d : ℝ) :
    allowance i d = dyadicRadius i ^ d := by
  simp only [allowance, dyadicRadius]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Every radius in `(0, 1]` lies between consecutive dyadic radii. -/
theorem exists_dyadicRadius_bracket {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ i : ℕ, dyadicRadius (i + 1) < r ∧ r ≤ dyadicRadius i := by
  obtain ⟨i, hi, hi'⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨i, ?_, ?_⟩
  · simpa only [dyadicRadius, two_rpow_neg_natCast] using hi
  · simpa only [dyadicRadius, two_rpow_neg_natCast] using hi'

/-- Moving two dyadic generations multiplies the radius by four. -/
theorem dyadicRadius_eq_four_mul_add_two (i : ℕ) :
    dyadicRadius i = 4 * dyadicRadius (i + 2) := by
  simp only [dyadicRadius, two_rpow_neg_natCast, pow_add]
  ring

/-- Dyadic ball estimates for a probability measure imply the usual all-radius Frostman bound.
The constant includes the harmless large-radius bound and the loss from comparing two nearby
dyadic scales. -/
theorem isFrostman_of_dyadic_ball_bound
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) {d : ℝ} (hd : 0 ≤ d)
    {A : ℝ≥0∞} (hA : A ≠ ∞)
    (hbound : ∀ i x r, 0 < r → r ≤ dyadicCoverRadius i →
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
        A * (4 * ENNReal.ofReal (allowance i d))) :
    IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) d
      (ENNReal.toReal
        (ENNReal.ofReal ((2 : ℝ) ^ d) +
          A * 4 * ENNReal.ofReal ((4 : ℝ) ^ d))) := by
  let Cinf : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ d) +
    A * 4 * ENNReal.ofReal ((4 : ℝ) ^ d)
  have hCinf : Cinf ≠ ∞ := by
    apply ENNReal.add_ne_top.2
    refine ⟨ENNReal.ofReal_ne_top, ?_⟩
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hA (by norm_num)) ENNReal.ofReal_ne_top
  intro x r hr hr1
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCinf]
  by_cases hrhalf : r ≤ 1 / 2
  · obtain ⟨i, hilow, hiup⟩ := exists_dyadicRadius_bracket hr hr1
    cases i with
    | zero =>
        have : (1 : ℝ) / 2 < r := by
          simpa only [Nat.zero_add, dyadicRadius, two_rpow_neg_natCast, pow_one] using hilow
        exact absurd hrhalf (not_le_of_gt this)
    | succ j =>
        have hrcover : r ≤ dyadicCoverRadius j := by
          rw [dyadicCoverRadius_eq_dyadicRadius_succ]
          simpa only [Nat.succ_eq_add_one] using hiup
        have hscale : dyadicRadius j < 4 * r := by
          rw [dyadicRadius_eq_four_mul_add_two]
          exact mul_lt_mul_of_pos_left (by simpa only [Nat.succ_eq_add_one,
            Nat.add_assoc] using hilow) (by norm_num)
        have hallow : allowance j d ≤ (4 * r) ^ d := by
          rw [allowance_eq_dyadicRadius_rpow]
          exact Real.rpow_le_rpow (dyadicRadius_pos j).le hscale.le hd
        refine (hbound j x r hr hrcover).trans ?_
        calc
          A * (4 * ENNReal.ofReal (allowance j d))
              ≤ A * (4 * ENNReal.ofReal ((4 * r) ^ d)) := by gcongr
          _ = (A * 4 * ENNReal.ofReal ((4 : ℝ) ^ d)) * ENNReal.ofReal (r ^ d) := by
            rw [Real.mul_rpow (by norm_num) hr.le,
              ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) d)]
            ring
          _ ≤ Cinf * ENNReal.ofReal (r ^ d) := by
            gcongr
            exact le_add_left le_rfl
  · have hrhalf' : 1 / 2 < r := lt_of_not_ge hrhalf
    refine prob_le_one.trans ?_
    have hbase : (1 : ℝ) ≤ 2 * r := by linarith
    have hrpow : (1 : ℝ) ≤ (2 * r) ^ d := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hbase hd
    calc
      (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by norm_num
      _ ≤ ENNReal.ofReal ((2 * r) ^ d) := ENNReal.ofReal_le_ofReal hrpow
      _ = ENNReal.ofReal ((2 : ℝ) ^ d) * ENNReal.ofReal (r ^ d) := by
        rw [Real.mul_rpow (by norm_num) hr.le,
          ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) d)]
      _ ≤ Cinf * ENNReal.ofReal (r ^ d) := by
        gcongr
        exact le_add_right le_rfl

/-- **Frostman's lemma for compact planar sets of positive Hausdorff content.**  A compact set
with positive `d`-dimensional Hausdorff content carries a probability measure satisfying a
genuine all-radius `d`-Frostman estimate. -/
theorem exists_isFrostman_probabilityMeasure_of_compact
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {d : ℝ} (hd : 0 ≤ d) (hcontent : 0 < hausdorffContent d K) :
    ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      μ ∈ probabilityMeasuresSupportedOn K ∧
      IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) d
        (ENNReal.toReal
          (ENNReal.ofReal ((2 : ℝ) ^ d) +
            (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) * 4 *
              ENNReal.ofReal ((4 : ℝ) ^ d))) := by
  obtain ⟨μ, hμK, hμ⟩ := exists_probabilityMeasure_dyadic_frostman hK hd hcontent
  refine ⟨μ, hμK, isFrostman_of_dyadic_ball_bound μ hd ?_ hμ⟩
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.2 (ne_of_gt hcontent))

/-- A compact set whose Hausdorff dimension is strictly larger than `d` carries a
`d`-Frostman probability measure. -/
theorem exists_isFrostman_probabilityMeasure_of_lt_dimH
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {d : ℝ} (hd : 0 < d) (hdim : ENNReal.ofReal d < dimH K) :
    ∃ (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C : ℝ),
      μ ∈ probabilityMeasuresSupportedOn K ∧
      IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) d C := by
  let dnn : ℝ≥0 := ⟨d, hd.le⟩
  have hdnncoe : (dnn : ℝ) = d := rfl
  have hdnn : (dnn : ℝ≥0∞) < dimH K := by
    calc
      (dnn : ℝ≥0∞) = ENNReal.ofReal (dnn : ℝ) := ENNReal.coe_nnreal_eq dnn
      _ = ENNReal.ofReal d := by rw [hdnncoe]
      _ < dimH K := hdim
  have hmeasure : μH[d] K = ∞ := by
    have hm := hausdorffMeasure_of_lt_dimH hdnn
    change μH[(dnn : ℝ)] K = ∞ at hm
    rwa [hdnncoe] at hm
  have hcontent : 0 < hausdorffContent d K :=
    hausdorffContent_pos hd (by rw [hmeasure]; exact ENNReal.top_ne_zero)
  obtain ⟨μ, hμK, hμ⟩ :=
    exists_isFrostman_probabilityMeasure_of_compact hK hd.le hcontent
  exact ⟨μ, _, hμK, hμ⟩

end FalconerPacking
