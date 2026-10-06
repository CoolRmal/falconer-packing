/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.HardGapCurve

/-!
# The scalar bridge from the cutoff curve to a profile certificate

This file proves the parameter selection in Appendix A.7 of the focused manuscript.
The scalar upper barrier may be enlarged to the point where the two hard-gap costs agree.
No geometric or analytic assumption enters these inequalities.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- The upper-barrier exponent where the one-gap and two-gap certificates meet. -/
def hardGapBarrierTransition (a : ℝ) : ℝ := (1 + 2 * a) / (4 + 2 * a)

theorem hardGapBarrierTransition_pos {a : ℝ} (ha : 0 ≤ a) :
    0 < hardGapBarrierTransition a := by
  unfold hardGapBarrierTransition
  positivity

theorem hardGapBarrierTransition_lt_half {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) :
    hardGapBarrierTransition a < 1 / 2 := by
  rw [hardGapBarrierTransition, div_lt_iff₀ (by positivity : 0 < 4 + 2 * a)]
  linarith

theorem hardGapTransition_sub_one_lt_one_eleventh : hardGapTransition - 1 < 1 / 11 := by
  have h : (29 / 11 : ℝ) < Real.sqrt 7 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  unfold hardGapTransition
  linarith

theorem rationalTransition_polynomial_nonpos {a : ℝ} (ha : 0 ≤ a)
    (ha' : a ≤ rationalTransition - 1) : 8 * a ^ 2 + 8 * a - 1 ≤ 0 := by
  have hc := rationalTransition_equation
  have hc' : 0 ≤ rationalTransition - 1 := by
    linarith [eleven_tenths_lt_rationalTransition]
  nlinarith [mul_nonneg (sub_nonneg.mpr ha')
    (show 0 ≤ 8 * (a + (rationalTransition - 1)) + 8 by positivity)]

/-- The smaller quadratic root occurs before the switch of hard-gap certificates. -/
theorem hardGapRoot_le_barrierTransition {a : ℝ} (ha : 0 ≤ a)
    (ha' : a ≤ rationalTransition - 1) : hardGapRoot a ≤ hardGapBarrierTransition a := by
  have hal : a < 1 := by linarith [rationalTransition_lt_nine_eighths]
  have hp := rationalTransition_polynomial_nonpos ha ha'
  have hs := Real.sq_sqrt (hardGapDiscriminant_nonneg ha ha')
  have hs' := congrArg (fun z : ℝ ↦ (1 + 2 * a) ^ 2 * z) hs
  change (1 + 2 * a) ^ 2 * Real.sqrt (hardGapDiscriminant a) ^ 2 =
    (1 + 2 * a) ^ 2 * (64 * a ^ 4 + 32 * a ^ 3 - 63 * a ^ 2 - 28 * a + 4) at hs'
  have hp' : 0 ≤ 72 * a * (1 - a) * (1 + a) * -(8 * a ^ 2 + 8 * a - 1) := by
    apply mul_nonneg
    · positivity
    · linarith
  have hsq : (-16 * a ^ 3 + 6 * a ^ 2 + 21 * a - 2) ^ 2 ≤
      ((1 + 2 * a) * Real.sqrt (hardGapDiscriminant a)) ^ 2 := by
    nlinarith only [hs', hp']
  have hle := le_of_sq_le_sq hsq (show 0 ≤
    (1 + 2 * a) * Real.sqrt (hardGapDiscriminant a) by positivity)
  rw [hardGapRoot, hardGapBarrierTransition,
    div_le_div_iff₀ (hardGapRoot_denominator_pos a) (by positivity : 0 < 4 + 2 * a)]
  nlinarith only [hle]

theorem twoGapGuard_at_onset_neg :
    twoGapGuard (hardGapTransition - 1) (2 * (hardGapTransition - 1)) < 0 := by
  let a := hardGapTransition - 1
  have he : 8 * a ^ 2 - 12 * a + 1 = 0 := hardGapTransition_equation
  have hid : twoGapGuard a (2 * a) = 3 * (11 * a - 1) := by
    unfold twoGapGuard
    linear_combination (2 * a + 4) * he
  change twoGapGuard a (2 * a) < 0
  rw [hid]
  have ha : a < 1 / 11 := hardGapTransition_sub_one_lt_one_eleventh
  linarith

/-- The lower-edge guard decreases from its negative value at the onset. -/
theorem twoGapGuard_double_neg {a : ℝ} (ha : hardGapTransition - 1 ≤ a)
    (ha' : a ≤ 1 / 4) : twoGapGuard a (2 * a) < 0 := by
  let c := hardGapTransition - 1
  have hc : 0 ≤ c := by dsimp [c]; linarith [one_lt_hardGapTransition]
  have hc' : c ≤ 1 / 4 := by dsimp [c]; linarith [hardGapTransition_lt_eleven_tenths]
  have hac : c ≤ a := ha
  have ha₀ : 0 ≤ a := hc.trans hac
  have haa : a ^ 2 ≤ 1 / 16 := by nlinarith [mul_nonneg ha₀ (sub_nonneg.mpr ha')]
  have hcc : c ^ 2 ≤ 1 / 16 := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hc')]
  have hac' : a * c ≤ 1 / 16 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha') hc]
  have hf : 16 * (a ^ 2 + a * c + c ^ 2) + 8 * (a + c) - 13 ≤ 0 := by linarith
  have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hac) hf
  have h : twoGapGuard a (2 * a) ≤ twoGapGuard c (2 * c) := by
    unfold twoGapGuard
    nlinarith only [hh]
  exact h.trans_lt twoGapGuard_at_onset_neg

/-- Throughout the low-barrier range the extra two-gap guard is strictly satisfied. -/
theorem twoGapGuard_neg {a b : ℝ} (ha : hardGapTransition - 1 ≤ a)
    (ha' : a ≤ 1 / 4) (hb : 2 * a ≤ b) (hb' : b ≤ 1 / 2) : twoGapGuard a b < 0 := by
  have ha₀ : 0 ≤ a := by linarith [one_lt_hardGapTransition]
  have hsum : b + 2 * a ≤ 1 := by linarith
  have hf : 4 * (1 + a) * (b + 2 * a) - 4 * (a + 2) ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 + a by positivity) (sub_nonneg.mpr hsum)]
  have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb) hf
  have h : twoGapGuard a b ≤ twoGapGuard a (2 * a) := by
    unfold twoGapGuard
    nlinarith only [hh]
  exact h.trans_lt (twoGapGuard_double_neg ha ha')

/-- Above the second joining point, the switching barrier has strict one-gap cost slack. -/
theorem singleGapCost_barrierTransition_lt {a : ℝ}
    (ha : rationalTransition - 1 < a) (ha' : a < 1 / 2) :
    singleGapCost a (hardGapBarrierTransition a) < a := by
  let c := rationalTransition - 1
  have hc : 0 ≤ c := by dsimp [c]; linarith [eleven_tenths_lt_rationalTransition]
  have he : 8 * c ^ 2 + 8 * c - 1 = 0 := rationalTransition_equation
  have ha₀ : 0 ≤ a := by linarith
  have hp : 0 < 8 * a ^ 2 + 8 * a - 1 := by
    have hh := mul_pos (show 0 < a - c by linarith)
      (show 0 < 8 * (a + c) + 8 by positivity)
    nlinarith only [he, hh]
  rw [singleGapCost_lt_iff ha' (hardGapBarrierTransition_pos ha₀).le,
    hardGapBarrierTransition, div_lt_div_iff₀ (by positivity : 0 < 4 + 2 * a)
      (by linarith : 0 < 1 - 2 * a)]
  nlinarith only [hp]

/-- The middle curve selects the original packing barrier without enlarging it. -/
theorem hardGap_middle_certificate {s u : ℝ} (hs : hardGapTransition < s)
    (hs' : s ≤ rationalTransition) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) :
    0 < u - 1 ∧ u - 1 < 1 ∧
      u - 1 ≤ hardGapBarrierTransition (s - 1) ∧ u - 1 ≤ 1 / 2 ∧
      twoGapGuard (s - 1) (u - 1) ≤ 0 ∧ twoGapCost (s - 1) (u - 1) < s - 1 := by
  have ha : 0 ≤ s - 1 := by linarith [one_lt_hardGapTransition]
  have ha' : s - 1 ≤ rationalTransition - 1 := by linarith
  have hb : 0 < u - 1 := by linarith [one_lt_hardGapTransition]
  rw [hausdorffPackingBound_of_mem_Ioc hs hs'] at hu'
  have hroot : u - 1 < hardGapRoot (s - 1) := by linarith
  have htrans := hroot.trans_le (hardGapRoot_le_barrierTransition ha ha')
  have hhalf := htrans.trans (hardGapBarrierTransition_lt_half ha
    (by linarith [rationalTransition_lt_nine_eighths]))
  refine ⟨hb, by linarith, htrans.le, hhalf.le, ?_,
    twoGapCost_lt_of_lt_hardGapRoot ha ha' hb.le hroot⟩
  exact (twoGapGuard_neg (by linarith) (by linarith [rationalTransition_lt_nine_eighths])
    (by linarith) hhalf.le).le

/-- The last curve permits increasing the barrier to the switching point when necessary. -/
theorem hardGap_rational_certificate {s u : ℝ} (hs : rationalTransition < s)
    (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u) (hu' : u < hausdorffPackingBound s) :
    ∃ b : ℝ, u - 1 ≤ b ∧ 0 < b ∧ b < 1 ∧
      hardGapBarrierTransition (s - 1) ≤ b ∧ singleGapCost (s - 1) b < s - 1 := by
  let a := s - 1
  have ha : 0 ≤ a := by dsimp [a]; linarith [eleven_tenths_lt_rationalTransition]
  have ha' : a < 1 / 2 := by dsimp [a]; linarith
  have hb : 0 < u - 1 := by linarith [eleven_tenths_lt_rationalTransition]
  have hden : 0 < 1 - 2 * a := by linarith
  have huF : u - 1 < 2 * a / (1 - 2 * a) := by
    rw [hausdorffPackingBound_of_rationalTransition_lt hs] at hu'
    have hden' : 0 < 3 - 2 * s := by linarith
    rw [lt_div_iff₀ hden'] at hu'
    rw [lt_div_iff₀ hden]
    dsimp [a]
    nlinarith only [hu']
  have hbcF : hardGapBarrierTransition a < 2 * a / (1 - 2 * a) :=
    (singleGapCost_lt_iff ha' (hardGapBarrierTransition_pos ha).le).mp
      (singleGapCost_barrierTransition_lt (by dsimp [a]; linarith) ha')
  have hmax := max_lt huF hbcF
  have hF : 2 * a / (1 - 2 * a) ≤ 1 := by
    rw [div_le_iff₀ hden]
    dsimp [a]
    linarith
  refine ⟨max (u - 1) (hardGapBarrierTransition a), le_max_left _ _,
    hb.trans_le (le_max_left _ _), hmax.trans_le hF, le_max_right _ _, ?_⟩
  exact (singleGapCost_lt_iff ha' (le_trans ha (by
    have : a ≤ u - 1 := by dsimp [a]; linarith
    exact this.trans (le_max_left _ _)))).2 hmax

/-- The exact scalar bridge needed by the profile method, with an admissible upper barrier. -/
theorem exists_hardGap_barrier {s u : ℝ} (_hs : 1 < s) (hs' : s ≤ 5 / 4)
    (hu : 2 * s - 1 ≤ u) (hu' : u < hausdorffPackingBound s) :
    ∃ b : ℝ, u - 1 ≤ b ∧ 0 < b ∧ b < 1 ∧
      ((b ≤ hardGapBarrierTransition (s - 1) ∧ b ≤ 1 / 2 ∧
        twoGapGuard (s - 1) b ≤ 0 ∧ twoGapCost (s - 1) b < s - 1) ∨
       (hardGapBarrierTransition (s - 1) ≤ b ∧ singleGapCost (s - 1) b < s - 1)) := by
  have hfirst : hardGapTransition < s := by
    by_contra h
    rw [hausdorffPackingBound_of_le_hardGapTransition (le_of_not_gt h)] at hu'
    exact (not_lt_of_ge hu) hu'
  by_cases hmiddle : s ≤ rationalTransition
  · obtain ⟨hb, hb', htrans, hhalf, hguard, hcost⟩ :=
      hardGap_middle_certificate hfirst hmiddle hu hu'
    exact ⟨u - 1, le_rfl, hb, hb', Or.inl ⟨htrans, hhalf, hguard, hcost⟩⟩
  · obtain ⟨b, hub, hb, hb', htrans, hcost⟩ :=
      hardGap_rational_certificate (lt_of_not_ge hmiddle) hs' hu hu'
    exact ⟨b, hub, hb, hb', Or.inr ⟨htrans, hcost⟩⟩

end FalconerPacking
