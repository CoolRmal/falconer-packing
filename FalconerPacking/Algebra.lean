/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Statement

/-!
# The curve algebra

Section 4 of the manuscript: the elementary inequalities that combine the original branch with
the finite-profile branch.  The exponent of the finite-profile branch is

`A s u = (U - s) / (2 * U - 1) + (u - s) / (2 * s)`,  `U = max u (3 / 2)`,

and the content of this file is that `A d t < d - 1` holds for every `t` with
`2 * d - 1 ≤ t < bound d`, when `1 < d ≤ 5 / 4`.  The two transition points `d0` and `d1` are
where the three branches of `bound` meet.
-/

noncomputable section

namespace FalconerPacking

/-- The exponent `A(s, u)` of the finite-profile criterion. -/
def A (s u : ℝ) : ℝ :=
  (max u (3 / 2) - s) / (2 * max u (3 / 2) - 1) + (u - s) / (2 * s)

/-- The middle branch `Q(d) = 3d² - 5d/2` of the curve. -/
def Q (d : ℝ) : ℝ := 3 * d ^ 2 - (5 / 2 : ℝ) * d

section Roots

theorem sq_sqrt33 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)

theorem sq_sqrt97 : Real.sqrt 97 ^ 2 = 97 := Real.sq_sqrt (by norm_num)

theorem five_lt_sqrt33 : 5 < Real.sqrt 33 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)

theorem sqrt33_lt : Real.sqrt 33 < 23 / 4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

theorem nine_lt_sqrt97 : 9 < Real.sqrt 97 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)

theorem sqrt97_lt_ten : Real.sqrt 97 < 10 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

theorem lt_sqrt97 : 49 / 5 < Real.sqrt 97 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)

/-- The first transition point lies above one. -/
theorem one_lt_d0 : 1 < d0 := by
  have := five_lt_sqrt33
  rw [d0]; linarith

/-- The two transition points are ordered. -/
theorem d0_lt_d1 : d0 < d1 := by
  have h33 := sq_sqrt33
  have h97 := sq_sqrt97
  have h33' := sqrt33_lt
  have h97' := lt_sqrt97
  rw [d0, d1]
  linarith

/-- The second transition point lies below the upper endpoint of the range. -/
theorem d1_lt_five_quarters : d1 < 5 / 4 := by
  have h97 := sq_sqrt97
  have h97' := sqrt97_lt_ten
  rw [d1]
  linarith

end Roots

section Branches

/-- Below the second transition point the middle branch stays below `3 / 2`. -/
theorem Q_le_three_halves {d : ℝ} (hd : 0 < d) (h : d ≤ d1) : Q d ≤ 3 / 2 := by
  have h97 := sq_sqrt97
  have h97' := nine_lt_sqrt97
  have hle : 12 * d - 5 ≤ Real.sqrt 97 := by rw [d1] at h; linarith
  have hpos : (0 : ℝ) < Real.sqrt 97 + (12 * d - 5) := by linarith
  have := mul_nonneg (sub_nonneg.2 hle) hpos.le
  rw [Q]
  nlinarith [this]

/-- Above the second transition point the middle branch exceeds `3 / 2`. -/
theorem three_halves_lt_Q {d : ℝ} (h : d1 < d) : 3 / 2 < Q d := by
  have h97 := sq_sqrt97
  have h97' := nine_lt_sqrt97
  have hlt : Real.sqrt 97 < 12 * d - 5 := by rw [d1] at h; linarith
  have hpos : (0 : ℝ) < Real.sqrt 97 + (12 * d - 5) := by linarith
  have := mul_pos (sub_pos.2 hlt) hpos
  rw [Q]
  nlinarith [this]

/-- The first branch of the curve. -/
theorem bound_of_le_d0 {d : ℝ} (h : d ≤ d0) : bound d = 2 * d - 1 := if_pos h

/-- The middle branch of the curve. -/
theorem bound_of_mem_Ioc {d : ℝ} (h0 : d0 < d) (h1 : d ≤ d1) : bound d = Q d := by
  rw [bound, if_neg (not_le.2 h0), if_pos h1, Q]

/-- The last branch of the curve. -/
theorem bound_of_d1_lt {d : ℝ} (h0 : d0 < d) (h1 : d1 < d) :
    bound d = ((2 * d - 1) ^ 2 + Real.sqrt ((2 * d - 1) ^ 4 + 8 * d)) / 4 := by
  rw [bound, if_neg (not_le.2 h0), if_neg (not_le.2 h1)]

end Branches

section Exponent

/-- Below `3 / 2` the exponent condition is the middle branch. -/
theorem A_lt_of_le_three_halves {d t : ℝ} (hd : 1 < d) (ht : t ≤ 3 / 2) (hQ : t < Q d) :
    A d t < d - 1 := by
  have hd0 : (0 : ℝ) < 2 * d := by linarith
  rw [A, max_eq_right ht, show (2 : ℝ) * (3 / 2) - 1 = 2 by norm_num,
    div_add_div _ _ (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hd0), div_lt_iff₀ (by positivity)]
  rw [Q] at hQ
  nlinarith [hQ]

/-- Above `3 / 2` the exponent condition is the quadratic branch. -/
theorem A_lt_of_three_halves_lt {d t : ℝ} (hd : 1 < d) (ht : 3 / 2 < t)
    (hq : 2 * t ^ 2 - (2 * d - 1) ^ 2 * t - d < 0) : A d t < d - 1 := by
  have hd0 : (0 : ℝ) < 2 * d := by linarith
  have ht0 : (0 : ℝ) < 2 * t - 1 := by linarith
  rw [A, max_eq_left ht.le, div_add_div _ _ (ne_of_gt ht0) (ne_of_gt hd0),
    div_lt_iff₀ (by positivity)]
  nlinarith [hq]

/-- The quadratic branch, from its closed-form positive root. -/
theorem quadratic_neg_of_lt_root {d t : ℝ} (hd : 1 < d) (ht : 0 < t)
    (h : t < ((2 * d - 1) ^ 2 + Real.sqrt ((2 * d - 1) ^ 4 + 8 * d)) / 4) :
    2 * t ^ 2 - (2 * d - 1) ^ 2 * t - d < 0 := by
  have hrad : (0 : ℝ) ≤ (2 * d - 1) ^ 4 + 8 * d := by positivity
  have hs2 : Real.sqrt ((2 * d - 1) ^ 4 + 8 * d) ^ 2 = (2 * d - 1) ^ 4 + 8 * d :=
    Real.sq_sqrt hrad
  have hs0 : 0 ≤ Real.sqrt ((2 * d - 1) ^ 4 + 8 * d) := Real.sqrt_nonneg _
  have ha0 : (0 : ℝ) ≤ (2 * d - 1) ^ 2 := by positivity
  have has : (2 * d - 1) ^ 2 < Real.sqrt ((2 * d - 1) ^ 4 + 8 * d) := by nlinarith [hs2, hs0]
  have hlow : ((2 * d - 1) ^ 2 - Real.sqrt ((2 * d - 1) ^ 4 + 8 * d)) / 4 < t := by linarith
  nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hlow), hs2]

end Exponent

/-- **The branch-combination lemma** (Section 4).  For `1 < d ≤ 5 / 4`, every exponent `t`
between `2 * d - 1` and the curve satisfies the finite-profile exponent condition. -/
theorem A_lt_sub_one {d t : ℝ} (hd : 1 < d) (hd' : d ≤ 5 / 4) (htlo : 2 * d - 1 ≤ t)
    (hthi : t < bound d) : A d t < d - 1 := by
  have ht0 : 0 < t := by linarith
  by_cases h0 : d ≤ d0
  · rw [bound_of_le_d0 h0] at hthi; linarith
  · rw [not_le] at h0
    by_cases h1 : d ≤ d1
    · rw [bound_of_mem_Ioc h0 h1] at hthi
      exact A_lt_of_le_three_halves hd
        (hthi.le.trans (Q_le_three_halves (by linarith) h1)) hthi
    · rw [not_le] at h1
      rw [bound_of_d1_lt h0 h1] at hthi
      rcases lt_or_ge (3 / 2 : ℝ) t with ht | ht
      · exact A_lt_of_three_halves_lt hd ht (quadratic_neg_of_lt_root hd ht0 hthi)
      · exact A_lt_of_le_three_halves hd ht (ht.trans_lt (three_halves_lt_Q h1))

/-- On the whole range the curve stays below `2`, the ambient dimension. -/
theorem bound_le_two {d : ℝ} (hd : 1 < d) (hd' : d ≤ 5 / 4) : bound d ≤ 2 := by
  by_cases h0 : d ≤ d0
  · rw [bound_of_le_d0 h0]; linarith
  · rw [not_le] at h0
    by_cases h1 : d ≤ d1
    · rw [bound_of_mem_Ioc h0 h1]
      have := Q_le_three_halves (by linarith) h1
      linarith
    · rw [not_le] at h1
      rw [bound_of_d1_lt h0 h1]
      have hx : (2 * d - 1) ^ 2 ≤ 9 / 4 := by nlinarith
      have hx0 : (0 : ℝ) ≤ (2 * d - 1) ^ 2 := sq_nonneg _
      have h4 : (2 * d - 1) ^ 4 = ((2 * d - 1) ^ 2) ^ 2 := by ring
      have hrad : (2 * d - 1) ^ 4 + 8 * d ≤ 16 := by nlinarith [hx, hx0, h4]
      have hsq : Real.sqrt ((2 * d - 1) ^ 4 + 8 * d) ≤ 4 := by
        have h := Real.sqrt_le_sqrt hrad
        rwa [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)] at h
      nlinarith [hsq, hx]

end FalconerPacking
