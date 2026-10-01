/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SlopeStripGeometry
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
# An explicit smooth partition on a uniform strip grid

Differences of consecutive smooth transitions give a nonnegative compact bump whose
integer translates sum exactly to one. Rescaling gives uniform derivative bounds.
-/

noncomputable section

open Set SchwartzMap
open scoped ContDiff

namespace FalconerPacking

/-- A fixed smooth bump whose integer translates form a partition of unity. -/
def stripPartitionBump (t : ℝ) : ℝ :=
  Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem stripPartitionBump_nonneg (t : ℝ) : 0 ≤ stripPartitionBump t :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem stripPartitionBump_le_one (t : ℝ) : stripPartitionBump t ≤ 1 := by
  have h₁ := Real.smoothTransition.le_one (t + 1)
  have h₂ := Real.smoothTransition.nonneg t
  unfold stripPartitionBump
  linarith

theorem contDiff_stripPartitionBump : ContDiff ℝ ∞ stripPartitionBump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem stripPartitionBump_eq_zero_of_le {t : ℝ} (ht : t ≤ -1) :
    stripPartitionBump t = 0 := by
  rw [stripPartitionBump, Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_self]

theorem stripPartitionBump_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    stripPartitionBump t = 0 := by
  rw [stripPartitionBump, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le ht, sub_self]

theorem support_stripPartitionBump : Function.support stripPartitionBump ⊆ Ioo (-1) 1 := by
  intro t ht
  constructor
  · by_contra h
    exact ht (stripPartitionBump_eq_zero_of_le (not_lt.mp h))
  · by_contra h
    exact ht (stripPartitionBump_eq_zero_of_one_le (not_lt.mp h))

theorem hasCompactSupport_stripPartitionBump : HasCompactSupport stripPartitionBump :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_stripPartitionBump.trans Ioo_subset_Icc_self)

/-- The finite sum is an exact telescoping difference, including both endpoints. -/
theorem sum_stripPartitionBump (M : ℕ) (t : ℝ) :
    (∑ j ∈ slopeNet M, stripPartitionBump (t - j)) =
      Real.smoothTransition (t + M + 1) - Real.smoothTransition (t - M) := by
  classical
  rw [slopeNet, Finset.sum_Icc_eq_sum_Ico_add _ (by omega : -(M : ℤ) ≤ M)]
  have he : ∀ j : ℤ, stripPartitionBump (t - j) =
      Real.smoothTransition (t - j + 1) - Real.smoothTransition (t - (j + 1 : ℤ) + 1) := by
    intro j
    simp only [stripPartitionBump, Int.cast_add, Int.cast_one]
    congr 1
    congr 1
    ring
  simp_rw [he]
  rw [Finset.sum_Ico_int_sub M (fun j : ℤ ↦ Real.smoothTransition (t - j + 1))]
  simp only [Int.cast_neg, Int.cast_natCast, Int.cast_add, Int.cast_one]
  have h₁ : t - -(M : ℝ) + 1 = t + M + 1 := by ring
  have h₂ : t - ((M : ℝ) + 1) + 1 = t - M := by ring
  rw [h₁, h₂]
  ring

/-- On the entire covered interval, the finite partition sums exactly to one. -/
theorem sum_stripPartitionBump_eq_one (M : ℕ) {t : ℝ} (ht : |t| ≤ M) :
    (∑ j ∈ slopeNet M, stripPartitionBump (t - j)) = 1 := by
  rw [sum_stripPartitionBump,
    Real.smoothTransition.one_of_one_le (by have := (abs_le.mp ht).1; linarith),
    Real.smoothTransition.zero_of_nonpos (by have := (abs_le.mp ht).2; linarith)]
  norm_num

/-- The explicit smooth bump on the strip of width `w` centered at integer index `j`. -/
def smoothStripWeight (w : ℝ) (j : ℤ) (t : ℝ) : ℝ := stripPartitionBump (t / w - j)

theorem smoothStripWeight_nonneg (w : ℝ) (j : ℤ) (t : ℝ) :
    0 ≤ smoothStripWeight w j t := stripPartitionBump_nonneg _

theorem smoothStripWeight_le_one (w : ℝ) (j : ℤ) (t : ℝ) :
    smoothStripWeight w j t ≤ 1 := stripPartitionBump_le_one _

theorem contDiff_smoothStripWeight (w : ℝ) (j : ℤ) :
    ContDiff ℝ ∞ (smoothStripWeight w j) :=
  contDiff_stripPartitionBump.comp ((contDiff_id.div_const w).sub contDiff_const)

theorem smoothStripWeight_support {w : ℝ} (hw : 0 < w) (j : ℤ) {t : ℝ}
    (ht : smoothStripWeight w j t ≠ 0) : |t - w * j| < w := by
  have hs := support_stripPartitionBump ht
  have hh : |t / w - j| < 1 := abs_lt.mpr hs
  have he : t - w * j = w * (t / w - j) := by field_simp
  rw [he, abs_mul, abs_of_pos hw]
  simpa using mul_lt_mul_of_pos_left hh hw

theorem sum_smoothStripWeight_eq_one {w : ℝ} (hw : 0 < w) (M : ℕ) {t : ℝ}
    (ht : |t| ≤ w * M) : (∑ j ∈ slopeNet M, smoothStripWeight w j t) = 1 := by
  apply sum_stripPartitionBump_eq_one M
  rw [abs_div, abs_of_pos hw, div_le_iff₀ hw]
  simpa only [mul_comm] using ht

/-- At most three of the explicit weights can be nonzero at any point. -/
theorem card_smoothStripWeight_support_le (w : ℝ)
    (I : Finset ℤ) (t : ℝ) :
    (I.filter (fun j ↦ smoothStripWeight w j t ≠ 0)).card ≤ 3 := by
  classical
  have h := int_finset_card_le_real_diameter
    (I.filter (fun j ↦ smoothStripWeight w j t ≠ 0)) (by norm_num : (0 : ℝ) ≤ 2) ?_
  · exact_mod_cast h
  intro j hj l hl
  have hj' := support_stripPartitionBump (Finset.mem_filter.mp hj).2
  have hl' := support_stripPartitionBump (Finset.mem_filter.mp hl).2
  exact abs_le.mpr ⟨by linarith [hj'.1, hj'.2, hl'.1, hl'.2],
    by linarith [hj'.1, hj'.2, hl'.1, hl'.2]⟩

/-- Exact derivative scaling, with no dependence on the strip index. -/
theorem iteratedDeriv_smoothStripWeight (n : ℕ) (w : ℝ)
    (j : ℤ) (t : ℝ) :
    iteratedDeriv n (smoothStripWeight w j) t =
      w⁻¹ ^ n * iteratedDeriv n stripPartitionBump (t / w - j) := by
  have hc : ContDiff ℝ n (fun x : ℝ ↦ stripPartitionBump (x - j)) :=
    (contDiff_stripPartitionBump.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)
  have he : smoothStripWeight w j =
      fun x : ℝ ↦ (fun z ↦ stripPartitionBump (z - j)) (w⁻¹ * x) := by
    funext x
    simp only [smoothStripWeight, div_eq_mul_inv, mul_comm]
  rw [he, iteratedDeriv_comp_const_mul hc, iteratedDeriv_comp_sub_const]
  simp only [div_eq_mul_inv, mul_comm]

/-- Every derivative has a uniform scale-correct bound. -/
theorem exists_smoothStripWeight_derivative_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : ℝ), 0 < w → ∀ (j : ℤ) (t : ℝ),
      ‖iteratedDeriv n (smoothStripWeight w j) t‖ ≤ C * w⁻¹ ^ n := by
  let f := hasCompactSupport_stripPartitionBump.toSchwartzMap contDiff_stripPartitionBump
  refine ⟨SchwartzMap.seminorm ℝ 0 n f, apply_nonneg _ _, ?_⟩
  intro w hw j t
  rw [iteratedDeriv_smoothStripWeight n w, norm_mul, norm_pow, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hw)]
  have h := SchwartzMap.le_seminorm' ℝ 0 n f (t / w - j)
  simp only [pow_zero, one_mul] at h
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (mul_comm _ _)

end FalconerPacking
