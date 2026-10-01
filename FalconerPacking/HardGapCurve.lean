/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.HardGapAlgebra
import FalconerPacking.Statement
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.OrderClosed

/-!
# The Hausdorff–packing cutoff from the hard-gap certificates

The definitions in `Statement` are the curve in Theorem 1.1 of the focused manuscript.
They do not replace the earlier `FalconerPacking.bound` API. The middle branch uses a
rationalized quadratic root, whose denominator is positive on the whole real line.
-/

noncomputable section

namespace FalconerPacking

theorem one_lt_hardGapTransition : 1 < hardGapTransition := by
  have h : Real.sqrt 7 < 3 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  unfold hardGapTransition
  linarith

theorem hardGapTransition_lt_eleven_tenths : hardGapTransition < 11 / 10 := by
  have h : (13 / 5 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  unfold hardGapTransition
  linarith

theorem eleven_tenths_lt_rationalTransition : 11 / 10 < rationalTransition := by
  have h : (12 / 5 : ℝ) < Real.sqrt 6 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  unfold rationalTransition
  linarith

theorem rationalTransition_lt_nine_eighths : rationalTransition < 9 / 8 := by
  have h : Real.sqrt 6 < 5 / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  unfold rationalTransition
  linarith

theorem hardGapTransition_lt_rationalTransition : hardGapTransition < rationalTransition :=
  hardGapTransition_lt_eleven_tenths.trans eleven_tenths_lt_rationalTransition

theorem hardGapRoot_denominator_pos (a : ℝ) :
    0 < 8 * a ^ 2 - a + 2 + Real.sqrt (hardGapDiscriminant a) := by
  have h := Real.sqrt_nonneg (hardGapDiscriminant a)
  nlinarith [sq_nonneg (4 * a - 1 / 4)]

theorem hardGapRoot_continuous : Continuous hardGapRoot := by
  unfold hardGapRoot hardGapDiscriminant
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun a ↦ ne_of_gt (hardGapRoot_denominator_pos a)

theorem hausdorffPackingBound_of_le_hardGapTransition {d : ℝ} (h : d ≤ hardGapTransition) :
    hausdorffPackingBound d = 2 * d - 1 := if_pos h

theorem hausdorffPackingBound_of_mem_Ioc {d : ℝ}
    (h₁ : hardGapTransition < d) (h₂ : d ≤ rationalTransition) :
    hausdorffPackingBound d = 1 + hardGapRoot (d - 1) := by
  rw [hausdorffPackingBound, if_neg h₁.not_ge, if_pos h₂]

theorem hausdorffPackingBound_of_rationalTransition_lt {d : ℝ}
    (h : rationalTransition < d) : hausdorffPackingBound d = 1 / (3 - 2 * d) := by
  rw [hausdorffPackingBound,
    if_neg (hardGapTransition_lt_rationalTransition.trans h).not_ge, if_neg h.not_ge]

/-- The first joining point satisfies the quadratic that determines the onset. -/
theorem hardGapTransition_equation :
    8 * (hardGapTransition - 1) ^ 2 - 12 * (hardGapTransition - 1) + 1 = 0 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)
  unfold hardGapTransition
  nlinarith only [h]

/-- The second joining point satisfies the equation where the two costs agree at the cutoff. -/
theorem rationalTransition_equation :
    8 * (rationalTransition - 1) ^ 2 + 8 * (rationalTransition - 1) - 1 = 0 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  unfold rationalTransition
  nlinarith only [h]

theorem hardGapRoot_hardGapTransition :
    hardGapRoot (hardGapTransition - 1) = 2 * (hardGapTransition - 1) := by
  let a := hardGapTransition - 1
  have he : 8 * a ^ 2 - 12 * a + 1 = 0 := hardGapTransition_equation
  have ha : a < 1 / 10 := by dsimp [a]; linarith [hardGapTransition_lt_eleven_tenths]
  have hd : hardGapDiscriminant a = (2 - 11 * a) ^ 2 := by
    unfold hardGapDiscriminant
    linear_combination (8 * a ^ 2 + 16 * a) * he
  have hs : Real.sqrt (hardGapDiscriminant a) = 2 - 11 * a := by
    rw [hd, Real.sqrt_sq (by linarith : 0 ≤ 2 - 11 * a)]
  change hardGapRoot a = 2 * a
  rw [hardGapRoot, hs, show 8 * a ^ 2 - a + 2 + (2 - 11 * a) = 3 by linarith]
  ring

theorem hardGapRoot_rationalTransition :
    hardGapRoot (rationalTransition - 1) = 2 * (rationalTransition - 1) /
      (1 - 2 * (rationalTransition - 1)) := by
  let a := rationalTransition - 1
  have he : 8 * a ^ 2 + 8 * a - 1 = 0 := rationalTransition_equation
  have ha : 0 ≤ a := by dsimp [a]; linarith [eleven_tenths_lt_rationalTransition]
  have ha' : a < 1 / 8 := by dsimp [a]; linarith [rationalTransition_lt_nine_eighths]
  have hd : hardGapDiscriminant a = (3 * a) ^ 2 := by
    unfold hardGapDiscriminant
    linear_combination (8 * a ^ 2 - 4 * a - 4) * he
  have hs : Real.sqrt (hardGapDiscriminant a) = 3 * a := by
    rw [hd, Real.sqrt_sq (by positivity : 0 ≤ 3 * a)]
  change hardGapRoot a = 2 * a / (1 - 2 * a)
  have hn : 1 - 2 * a ≠ 0 := ne_of_gt (by linarith)
  have hd' := ne_of_gt (hardGapRoot_denominator_pos a)
  rw [hardGapRoot, hs]
  rw [hs] at hd'
  apply (div_eq_div_iff hd' hn).2
  linear_combination -2 * a * he

theorem hausdorffPackingBound_first_join :
    2 * hardGapTransition - 1 = 1 + hardGapRoot (hardGapTransition - 1) := by
  rw [hardGapRoot_hardGapTransition]
  ring

theorem hausdorffPackingBound_second_join :
    1 + hardGapRoot (rationalTransition - 1) = 1 / (3 - 2 * rationalTransition) := by
  rw [hardGapRoot_rationalTransition]
  have h : 1 - 2 * (rationalTransition - 1) ≠ 0 :=
    ne_of_gt (by linarith [rationalTransition_lt_nine_eighths])
  have h' : 3 - 2 * rationalTransition = 1 - 2 * (rationalTransition - 1) := by ring
  rw [h']
  field_simp
  ring

theorem hardGapRoot_one_tenth : hardGapRoot (1 / 10) = 5 / 23 := by
  have hs : Real.sqrt (hardGapDiscriminant (1 / 10)) = 39 / 50 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num [hardGapDiscriminant]) (by norm_num)).2
    norm_num [hardGapDiscriminant]
  norm_num [hardGapRoot, hs]

theorem hausdorffPackingBound_eleven_tenths : hausdorffPackingBound (11 / 10) = 28 / 23 := by
  rw [hausdorffPackingBound_of_mem_Ioc hardGapTransition_lt_eleven_tenths
    eleven_tenths_lt_rationalTransition.le, show (11 / 10 : ℝ) - 1 = 1 / 10 by norm_num,
    hardGapRoot_one_tenth]
  norm_num

theorem hausdorffPackingBound_twenty_three_twentieths :
    hausdorffPackingBound (23 / 20) = 10 / 7 := by
  rw [hausdorffPackingBound_of_rationalTransition_lt
    (by linarith [rationalTransition_lt_nine_eighths])]
  norm_num

theorem hausdorffPackingBound_five_quarters : hausdorffPackingBound (5 / 4) = 2 := by
  rw [hausdorffPackingBound_of_rationalTransition_lt
    (by linarith [rationalTransition_lt_nine_eighths])]
  norm_num

/-- The cutoff is continuous throughout the interval preceding its rational pole. -/
theorem hausdorffPackingBound_continuousOn :
    ContinuousOn hausdorffPackingBound (Set.Iio (3 / 2)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hm : Continuous (fun x : Set.Iio (3 / 2 : ℝ) ↦ 1 + hardGapRoot (x.val - 1)) :=
    continuous_const.add (hardGapRoot_continuous.comp (continuous_subtype_val.sub continuous_const))
  have hr : Continuous (fun x : Set.Iio (3 / 2 : ℝ) ↦ 1 / (3 - 2 * x.val)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro x
    have hx : x.val < 3 / 2 := x.property
    exact ne_of_gt (by linarith)
  have hi : Continuous (fun x : Set.Iio (3 / 2 : ℝ) ↦
      if x.val ≤ rationalTransition then 1 + hardGapRoot (x.val - 1)
      else 1 / (3 - 2 * x.val)) := by
    apply hm.if_le hr continuous_subtype_val continuous_const
    intro x hx
    simpa only [hx] using hausdorffPackingBound_second_join
  change Continuous (fun x : Set.Iio (3 / 2 : ℝ) ↦
    if x.val ≤ hardGapTransition then 2 * x.val - 1
    else if x.val ≤ rationalTransition then 1 + hardGapRoot (x.val - 1)
    else 1 / (3 - 2 * x.val))
  apply Continuous.if_le (by fun_prop) hi continuous_subtype_val continuous_const
  intro x hx
  simpa only [hx, if_pos hardGapTransition_lt_rationalTransition.le] using
    hausdorffPackingBound_first_join

/-- A strict cutoff leaves room to lower the source exponent and raise the packing exponent. -/
theorem exists_strict_exponents {d D : ℝ} (hd : 1 < d) (hd' : d < 3 / 2)
    (hD : D < hausdorffPackingBound d) :
    ∃ s u : ℝ, 1 < s ∧ s < d ∧ D < u ∧ u < hausdorffPackingBound s := by
  obtain ⟨u, hDu, hu⟩ := exists_between hD
  have hc := hausdorffPackingBound_continuousOn.continuousAt (Iio_mem_nhds hd')
  have he : ∀ᶠ x in nhds d, u < hausdorffPackingBound x :=
    Filter.Tendsto.eventually_const_lt hu hc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨s, hs, hsd⟩ := exists_between (show max 1 (d - ε) < d by exact max_lt hd (by linarith))
  refine ⟨s, u, (le_max_left 1 (d - ε)).trans_lt hs, hsd, hDu, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr hsd)]
  have hsd' : d - ε < s := (le_max_right 1 (d - ε)).trans_lt hs
  linarith

/-- The discriminant stays nonnegative on the interval used for the middle branch. -/
theorem hardGapDiscriminant_nonneg {a : ℝ} (ha : 0 ≤ a)
    (ha' : a ≤ rationalTransition - 1) : 0 ≤ hardGapDiscriminant a := by
  have hc := rationalTransition_equation
  have hc' : rationalTransition - 1 < 1 / 8 := by
    linarith [rationalTransition_lt_nine_eighths]
  have hp : 8 * a ^ 2 + 8 * a - 1 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha')
      (show 0 ≤ 8 * (a + (rationalTransition - 1)) + 8 by linarith)]
  have hn : 8 * a ^ 2 - 4 * a - 4 ≤ 0 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 1 / 8 - a by linarith)]
  have hid : hardGapDiscriminant a = 9 * a ^ 2 +
      (8 * a ^ 2 - 4 * a - 4) * (8 * a ^ 2 + 8 * a - 1) := by
    unfold hardGapDiscriminant
    ring
  rw [hid]
  exact add_nonneg (by positivity) (mul_nonneg_of_nonpos_of_nonpos hn hp)

/-- Rationalization agrees with the smaller root in the usual quadratic formula. -/
theorem hardGapRoot_eq_quadratic_formula {a : ℝ} (hp : 0 < 1 + 4 * a - 2 * a ^ 2)
    (hd : 0 ≤ hardGapDiscriminant a) :
    hardGapRoot a = (8 * a ^ 2 - a + 2 - Real.sqrt (hardGapDiscriminant a)) /
      (4 * (1 + 4 * a - 2 * a ^ 2)) := by
  have hs := Real.sq_sqrt hd
  change Real.sqrt (hardGapDiscriminant a) ^ 2 =
    64 * a ^ 4 + 32 * a ^ 3 - 63 * a ^ 2 - 28 * a + 4 at hs
  rw [hardGapRoot]
  apply (div_eq_div_iff (ne_of_gt (hardGapRoot_denominator_pos a))
    (ne_of_gt (by positivity))).2
  nlinarith only [hs]

/-- The rationalized middle cutoff solves the two-gap cost level equation. -/
theorem hardGapRoot_equation {a : ℝ} (hd : 0 ≤ hardGapDiscriminant a) :
    (4 * a ^ 2 - 8 * a - 2) * hardGapRoot a ^ 2 +
      (8 * a ^ 2 - a + 2) * hardGapRoot a - 3 * a = 0 := by
  have hs := Real.sq_sqrt hd
  change Real.sqrt (hardGapDiscriminant a) ^ 2 =
    64 * a ^ 4 + 32 * a ^ 3 - 63 * a ^ 2 - 28 * a + 4 at hs
  have hn := ne_of_gt (hardGapRoot_denominator_pos a)
  set z := 8 * a ^ 2 - a + 2 + Real.sqrt (hardGapDiscriminant a) with hz
  change (4 * a ^ 2 - 8 * a - 2) * (6 * a / z) ^ 2 +
    (8 * a ^ 2 - a + 2) * (6 * a / z) - 3 * a = 0
  have hz' : z ≠ 0 := hn
  field_simp [hz']
  dsimp [z]
  linear_combination -3 * a * hs

/-- Every nonnegative exponent below the middle cutoff has strictly smaller two-gap cost. -/
theorem twoGapCost_lt_of_lt_hardGapRoot {a b : ℝ} (ha : 0 ≤ a)
    (ha' : a ≤ rationalTransition - 1) (hb : 0 ≤ b) (hbr : b < hardGapRoot a) :
    twoGapCost a b < a := by
  have hal : a < 1 / 8 := lt_of_le_of_lt ha' (by
    linarith [rationalTransition_lt_nine_eighths])
  have hp : 0 < 1 + 4 * a - 2 * a ^ 2 := by
    nlinarith [mul_nonneg ha (show 0 ≤ 1 / 8 - a by linarith)]
  have hd := hardGapDiscriminant_nonneg ha ha'
  have he := hardGapRoot_equation hd
  have hv : 4 * (1 + 4 * a - 2 * a ^ 2) * hardGapRoot a ≤ 8 * a ^ 2 - a + 2 := by
    rw [hardGapRoot_eq_quadratic_formula hp hd]
    have hn : 4 * (1 + 4 * a - 2 * a ^ 2) ≠ 0 := ne_of_gt (by positivity)
    rw [mul_div_cancel₀ _ hn]
    exact sub_le_self _ (Real.sqrt_nonneg _)
  have hf : 0 < 8 * a ^ 2 - a + 2 -
      2 * (1 + 4 * a - 2 * a ^ 2) * (b + hardGapRoot a) := by
    nlinarith [mul_pos hp (sub_pos.mpr hbr)]
  rw [twoGapCost_lt_iff (by linarith : a < 1) hb]
  nlinarith only [he, mul_neg_of_neg_of_pos (sub_neg.mpr hbr) hf]

end FalconerPacking
