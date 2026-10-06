/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

/-!
# The hard-gap weighted inequalities

These are the finite algebraic certificates in Sections 6.5 and 6.6 of the updated
packing manuscript. The hypotheses are the displayed endpoint, gap, and tail inequalities.
The geometric reduction to those hypotheses and the distance theorem are separate obligations.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- The single-collapse profile cost. -/
def singleGapCost (a b : ℝ) : ℝ := (b - a) / (1 + 2 * b)

/-- The two-collapse profile cost. -/
def twoGapCost (a b : ℝ) : ℝ :=
  (b - a) * (2 + a - 2 * b - 4 * a * b) / ((1 - a) * (1 + 2 * b) ^ 2)

/-- The guard for the blended tail in the two-collapse certificate. -/
def twoGapGuard (a b : ℝ) : ℝ := 4 * (1 + a) * b ^ 2 - 4 * (a + 2) * b + 1 + 3 * a

/-- The low-side weighted certificate, including both tail bounds. -/
theorem twoGapCost_bound {a b q₁ p₁ u₁ v₁ q₂ p₂ u₂ v₂ tail : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : b * (4 + 2 * a) ≤ 1 + 2 * a) (hguard : twoGapGuard a b ≤ 0)
    (h₁ : u₁ - b * q₁ ≤ 0) (h₂ : a * p₁ - v₁ ≤ 0)
    (h₃ : q₁ - 2 * p₁ + 2 * (u₁ - v₁) ≤ -1)
    (h₄ : u₂ - v₁ - q₂ + p₁ ≤ 0) (h₅ : u₂ - b * q₂ ≤ 0)
    (h₆ : q₂ - 2 * p₂ + 2 * (u₂ - v₂) ≤ -1) (h₇ : p₂ ≤ 1)
    (htail₁ : tail ≤ (1 - p₂) / 2) (htail₂ : tail ≤ (1 - p₂ + v₂ - a) / 2) :
    (u₁ - v₁) + (u₂ - v₂) + tail ≤ twoGapCost a b := by
  have hb₀ : 0 < b := lt_trans ha hab
  have ha₁ : 0 < 1 - a := by linarith
  have hs : 0 < 1 + 2 * b := by positivity
  have hden : 0 < (1 - a) * (1 + 2 * b) ^ 2 := by positivity
  let D := (1 - a) * (1 + 2 * b) ^ 2
  let N := 1 + a - 4 * a * b + 4 * b ^ 2 - 2 * b
  have hN : 0 ≤ N := by
    dsimp [N]
    nlinarith [mul_nonneg hb₀.le (sub_nonneg.mpr hab.le)]
  have hblend : 0 ≤ D - 2 * N := by
    dsimp [D, N]
    dsimp [twoGapGuard] at hguard
    nlinarith only [hguard]
  have hw₁ : 0 ≤ (1 - a) * (1 + 2 * b) := by positivity
  have hw₂ : 0 ≤ (1 - 2 * b) * (1 + 2 * b) :=
    mul_nonneg (by linarith) hs.le
  have hw₃ : 0 ≤ b * (1 - a) * (1 + 2 * b) := by positivity
  have hw₄ : 0 ≤ (2 * b - a) * (1 + 2 * b) :=
    mul_nonneg (by linarith) hs.le
  have hw₅ : 0 ≤ 1 + 2 * a - 4 * b - 2 * a * b := by nlinarith only [htransition]
  have hw₆ : 0 ≤ (D - N) / 2 := by linarith
  have hw₇ : 0 ≤ D / 2 - N := by linarith
  have e₁ := mul_le_mul_of_nonneg_left h₁ hw₁
  have e₂ := mul_le_mul_of_nonneg_left h₂ hw₂
  have e₃ := mul_le_mul_of_nonneg_left h₃ hw₃
  have e₄ := mul_le_mul_of_nonneg_left h₄ hw₄
  have e₅ := mul_le_mul_of_nonneg_left h₅ hw₅
  have e₆ := mul_le_mul_of_nonneg_left h₆ hw₆
  have e₇ := mul_le_mul_of_nonneg_left h₇ hw₇
  have e₈ := mul_le_mul_of_nonneg_left htail₁ hblend
  have e₉ := mul_le_mul_of_nonneg_left htail₂ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hN)
  rw [twoGapCost, le_div_iff₀ hden]
  dsimp [D, N] at e₆ e₇ e₈ e₉
  nlinarith only [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]

/-- The high-side weighted certificate, using the net increase between the positive gaps. -/
theorem singleGapCost_bound {a b q₁ p₁ u₁ v₁ q₂ p₂ u₂ v₂ tail : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : 1 + 2 * a ≤ b * (4 + 2 * a))
    (h₁ : u₁ - b * q₁ ≤ 0) (h₂ : u₁ - v₁ - p₁ + q₁ / 2 ≤ -1 / 2)
    (h₃ : a * p₁ - v₁ ≤ 0) (h₄ : u₂ - v₂ - p₂ + q₂ / 2 ≤ -1 / 2)
    (h₅ : a * p₂ - v₂ ≤ 0) (h₆ : u₂ - v₁ - q₂ + p₁ ≤ 0)
    (h₇ : p₂ ≤ 1) (h₈ : v₁ - u₂ ≤ 0) (htail : tail ≤ (1 - p₂) / 2) :
    (u₁ - v₁) + (u₂ - v₂) + tail ≤ singleGapCost a b := by
  have hb₀ : 0 < b := lt_trans ha hab
  have ha₂ : 0 < 1 - 2 * a := by linarith
  have hs : 0 < 1 + 2 * b := by positivity
  have hden : 0 < (1 + 2 * a) * (1 + 2 * b) := by positivity
  have hw₁ : 0 ≤ 1 + 2 * a := by positivity
  have hw₂ : 0 ≤ 2 * b * (1 + 2 * a) := by positivity
  have hw₃ : 0 ≤ 2 * b := by positivity
  have hw₄ : 0 ≤ 4 * b * (1 + a) := by positivity
  have hw₅ : 0 ≤ 1 + 2 * a - 2 * b := by linarith
  have hw₆ : 0 ≤ 2 * b * (1 + a) := by positivity
  have hw₇ : 0 ≤ ((6 + 8 * a) * b - (1 + 2 * a) ^ 2) / 2 := by
    have h := mul_nonneg (sub_nonneg.mpr htransition) (show 0 ≤ 6 + 8 * a by positivity)
    have h' := mul_nonneg (mul_nonneg (show 0 ≤ 1 + a by positivity) ha₂.le) hw₁
    have hid : ((6 + 8 * a) * b - (1 + 2 * a) ^ 2) * (a + 2) =
        (b * (4 + 2 * a) - (1 + 2 * a)) * (6 + 8 * a) / 2 +
        (1 + a) * (1 - 2 * a) * (1 + 2 * a) := by ring
    have hprod : 0 ≤ ((6 + 8 * a) * b - (1 + 2 * a) ^ 2) * (a + 2) := by
      rw [hid]
      positivity
    have : 0 ≤ (6 + 8 * a) * b - (1 + 2 * a) ^ 2 :=
      nonneg_of_mul_nonneg_left hprod (by positivity)
    positivity
  have hw₈ : 0 ≤ (2 * a + 4) * b - (2 * a + 1) := by nlinarith only [htransition]
  have e₁ := mul_le_mul_of_nonneg_left h₁ hw₁
  have e₂ := mul_le_mul_of_nonneg_left h₂ hw₂
  have e₃ := mul_le_mul_of_nonneg_left h₃ hw₃
  have e₄ := mul_le_mul_of_nonneg_left h₄ hw₄
  have e₅ := mul_le_mul_of_nonneg_left h₅ hw₅
  have e₆ := mul_le_mul_of_nonneg_left h₆ hw₆
  have e₇ := mul_le_mul_of_nonneg_left h₇ hw₇
  have e₈ := mul_le_mul_of_nonneg_left h₈ hw₈
  have e₉ := mul_le_mul_of_nonneg_left htail hden.le
  rw [singleGapCost, le_div_iff₀ hs]
  have hbound : ((u₁ - v₁) + (u₂ - v₂) + tail) * (1 + 2 * b) * (1 + 2 * a) ≤
      (b - a) * (1 + 2 * a) := by
    nlinarith only [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈, e₉]
  exact (mul_le_mul_iff_left₀ (show 0 < 1 + 2 * a by positivity)).mp (by
    simpa only [mul_comm] using hbound)

/-- The simple cost threshold is an exact rational inequality. -/
theorem singleGapCost_lt_iff {a b : ℝ} (ha : a < 1 / 2) (hb : 0 ≤ b) :
    singleGapCost a b < a ↔ b < 2 * a / (1 - 2 * a) := by
  rw [singleGapCost, div_lt_iff₀ (by positivity : 0 < 1 + 2 * b),
    lt_div_iff₀ (by linarith : 0 < 1 - 2 * a)]
  constructor <;> intro h <;> nlinarith only [h]

/-- The two costs agree exactly at the transition used by the weighted certificates. -/
theorem twoGapCost_sub_singleGapCost {a b : ℝ} (ha : a < 1) (hb : 0 ≤ b) :
    twoGapCost a b - singleGapCost a b =
      (b - a) * (1 + 2 * a - 4 * b - 2 * a * b) / ((1 - a) * (1 + 2 * b) ^ 2) := by
  have ha₀ : 1 - a ≠ 0 := ne_of_gt (by linarith)
  have hb₀ : 1 + 2 * b ≠ 0 := ne_of_gt (by positivity)
  unfold twoGapCost singleGapCost
  field_simp
  ring

/-- Clearing positive denominators gives the quadratic defining the improved middle branch. -/
theorem twoGapCost_lt_iff {a b : ℝ} (ha : a < 1) (hb : 0 ≤ b) :
    twoGapCost a b < a ↔
      (4 * a ^ 2 - 8 * a - 2) * b ^ 2 + (8 * a ^ 2 - a + 2) * b - 3 * a < 0 := by
  have hden : 0 < (1 - a) * (1 + 2 * b) ^ 2 :=
    mul_pos (by linarith) (sq_pos_of_pos (by positivity))
  rw [twoGapCost, div_lt_iff₀ hden]
  constructor <;> intro h <;> nlinarith only [h]

/-- The new low-dimensional example has a strictly positive exact margin. -/
theorem twoGapCost_example_margin :
    9 / 100 - twoGapCost (9 / 100) (181 / 1000) = 1861 / 5152900 := by
  norm_num [twoGapCost]

/-- The improved high-side example has a strictly positive exact margin. -/
theorem singleGapCost_example_margin :
    3 / 20 - singleGapCost (3 / 20) (2 / 5) = 1 / 90 := by
  norm_num [singleGapCost]

end FalconerPacking
