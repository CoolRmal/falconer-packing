/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Profile
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Piecewise linear interpolation of finite profiles

The interpolant is linear on each unit grid interval and constant outside the finite domain.
It preserves the endpoint values, the unit Lipschitz bound, and linear barriers. Minima and
edge costs on integer-ended intervals agree exactly with the discrete definitions.
-/

noncomputable section

open Finset Set

namespace FalconerPacking

/-- The unit ramp starting at the integer `j`. -/
def profileRamp (j : ℕ) (x : ℝ) : ℝ := min (max (x - j) 0) 1

/-- Linear interpolation on each unit interval, extended constantly outside `[0,N]`. -/
def profileInterpolation (g : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  g 0 + ∑ j ∈ range N, (g (j + 1) - g j) * profileRamp j x

private theorem profileRamp_eq_zero_aux {j : ℕ} {x : ℝ} (hx : x ≤ j) :
    profileRamp j x = 0 := by
  simp [profileRamp, max_eq_right (sub_nonpos.mpr hx)]

private theorem profileRamp_eq_one_aux {j : ℕ} {x : ℝ} (hx : (j : ℝ) + 1 ≤ x) :
    profileRamp j x = 1 := by
  rw [profileRamp, max_eq_left (by linarith), min_eq_right (by linarith)]

private theorem profileRamp_eq_sub_aux {j : ℕ} {x : ℝ} (hx : (j : ℝ) ≤ x)
    (hx' : x ≤ (j : ℝ) + 1) : profileRamp j x = x - j := by
  rw [profileRamp, max_eq_left (sub_nonneg.mpr hx), min_eq_left (by linarith)]

private theorem profileRamp_telescope_aux (j : ℕ) (x : ℝ) :
    profileRamp j x = min (max x 0) ((j : ℝ) + 1) - min (max x 0) j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_cases hx : x ≤ 0
  · rw [profileRamp_eq_zero_aux (hx.trans hj), max_eq_right hx,
      min_eq_left (by linarith), min_eq_left hj]
    ring
  · rw [max_eq_left (le_of_not_ge hx)]
    by_cases hxj : x ≤ j
    · rw [profileRamp_eq_zero_aux hxj, min_eq_left (by linarith), min_eq_left hxj]
      ring
    · by_cases hxj' : x ≤ (j : ℝ) + 1
      · rw [profileRamp_eq_sub_aux (le_of_not_ge hxj) hxj', min_eq_left hxj',
          min_eq_right (le_of_not_ge hxj)]
      · rw [profileRamp_eq_one_aux (le_of_not_ge hxj'),
          min_eq_right (le_of_not_ge hxj'), min_eq_right (le_of_not_ge hxj)]
        ring

/-- The unit ramps sum to the identity clipped to `[0,N]`. -/
theorem sum_profileRamp (N : ℕ) (x : ℝ) :
    ∑ j ∈ range N, profileRamp j x = min (max x 0) N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih, profileRamp_telescope_aux]
      push_cast
      ring

/-- The interpolant is unchanged to the left when a final cell is appended. -/
theorem profileInterpolation_succ_of_le {g : ℕ → ℝ} {N : ℕ} {x : ℝ} (hx : x ≤ N) :
    profileInterpolation g (N + 1) x = profileInterpolation g N x := by
  simp [profileInterpolation, sum_range_succ, profileRamp_eq_zero_aux hx]

/-- The interpolant is constant to the right of its final node. -/
theorem profileInterpolation_of_le (g : ℕ → ℝ) :
    ∀ (N : ℕ) (x : ℝ), (N : ℝ) ≤ x → profileInterpolation g N x = g N
  | 0, _, _ => by simp [profileInterpolation]
  | N + 1, x, hx => by
      have hx' : (N : ℝ) + 1 ≤ x := by exact_mod_cast hx
      have hprev := profileInterpolation_of_le g N x (by linarith)
      simp only [profileInterpolation, sum_range_succ,
        profileRamp_eq_one_aux hx', mul_one] at *
      linarith

/-- On every grid cell the interpolant is its affine endpoint interpolation. -/
theorem profileInterpolation_on_cell (g : ℕ → ℝ) :
    ∀ (N j : ℕ), j < N → ∀ x : ℝ, (j : ℝ) ≤ x → x ≤ (j : ℝ) + 1 →
      profileInterpolation g N x = g j + (x - j) * (g (j + 1) - g j)
  | 0, _, hj, _, _, _ => by omega
  | N + 1, j, hj, x, hx, hx' => by
      by_cases hjN : j < N
      · have hjN' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hjN
        rw [profileInterpolation_succ_of_le (hx'.trans hjN')]
        exact profileInterpolation_on_cell g N j hjN x hx hx'
      · have hjEq : j = N := by omega
        subst j
        have hprev := profileInterpolation_of_le g N x hx
        simp only [profileInterpolation, sum_range_succ,
          profileRamp_eq_sub_aux hx hx'] at *
        linarith

/-- Every original grid value is preserved. -/
theorem profileInterpolation_natCast (g : ℕ → ℝ) {N j : ℕ} (hj : j ≤ N) :
    profileInterpolation g N j = g j := by
  rcases lt_or_eq_of_le hj with hj | rfl
  · rw [profileInterpolation_on_cell g N j hj j le_rfl (by linarith)]
    simp
  · exact profileInterpolation_of_le g j j le_rfl

/-- Every finite interpolant is continuous on the entire real line. -/
theorem continuous_profileInterpolation (g : ℕ → ℝ) (N : ℕ) :
    Continuous (profileInterpolation g N) := by
  unfold profileInterpolation profileRamp
  fun_prop

private theorem profileRamp_mono_aux (j : ℕ) : Monotone (profileRamp j) := by
  intro x y hxy
  exact min_le_min (max_le_max (sub_le_sub_right hxy _) le_rfl) le_rfl

private theorem clipped_sub_le_aux (N : ℕ) (x y : ℝ) :
    min (max y 0) N - min (max x 0) N ≤ |y - x| := by
  have hmin : |min (max y 0) N - min (max x 0) N| ≤ |max y 0 - max x 0| := by
    simpa using abs_min_sub_min_le_max (max y 0) (N : ℝ) (max x 0) (N : ℝ)
  exact (le_abs_self _).trans (hmin.trans (abs_max_sub_max_le_abs y x 0))

private theorem profileInterpolation_dist_aux {g : ℕ → ℝ} {N : ℕ}
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    |profileInterpolation g N y - profileInterpolation g N x| ≤ |y - x| := by
  have hdiff : profileInterpolation g N y - profileInterpolation g N x =
      ∑ j ∈ range N, (g (j + 1) - g j) * (profileRamp j y - profileRamp j x) := by
    simp only [profileInterpolation, mul_sub, sum_sub_distrib]
    ring
  rw [hdiff]
  calc
    |∑ j ∈ range N, (g (j + 1) - g j) * (profileRamp j y - profileRamp j x)| ≤
        ∑ j ∈ range N, |(g (j + 1) - g j) * (profileRamp j y - profileRamp j x)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range N, (profileRamp j y - profileRamp j x) := by
      refine sum_le_sum fun j hj ↦ ?_
      have hnonneg := sub_nonneg.mpr (profileRamp_mono_aux j hxy)
      rw [abs_mul, abs_of_nonneg hnonneg]
      simpa using mul_le_mul_of_nonneg_right (hlip j (mem_range.mp hj)) hnonneg
    _ = min (max y 0) N - min (max x 0) N := by
      rw [sum_sub_distrib, sum_profileRamp, sum_profileRamp]
    _ ≤ |y - x| := clipped_sub_le_aux N x y

/-- The interpolant is globally 1-Lipschitz using only the finite grid increments. -/
theorem lipschitzWith_profileInterpolation {g : ℕ → ℝ} {N : ℕ}
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) :
    LipschitzWith 1 (profileInterpolation g N) := by
  apply LipschitzWith.mk_one
  intro x y
  simp only [Real.dist_eq]
  rcases le_total x y with hxy | hyx
  · simpa only [abs_sub_comm (profileInterpolation g N y) (profileInterpolation g N x),
      abs_sub_comm y x] using profileInterpolation_dist_aux hlip hxy
  · exact profileInterpolation_dist_aux hlip hyx

/-- The linear barriers at the grid nodes remain valid throughout the real interval. -/
theorem profileInterpolation_barriers {g : ℕ → ℝ} {N : ℕ} {a b : ℝ}
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) N) :
    a * x ≤ profileInterpolation g N x ∧ profileInterpolation g N x ≤ b * x := by
  rcases lt_or_eq_of_le hx.2 with hxN | rfl
  · let j := ⌊x⌋₊
    have hjx : (j : ℝ) ≤ x := Nat.floor_le hx.1
    have hxj : x ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    have hjN : j < N := by exact_mod_cast (hjx.trans_lt hxN)
    have hleft : 0 ≤ 1 - (x - j) := by linarith
    have hright : 0 ≤ x - j := sub_nonneg.mpr hjx
    have hlow₀ := mul_le_mul_of_nonneg_left (hlower j hjN.le) hleft
    have hlow₁ := mul_le_mul_of_nonneg_left (hlower (j + 1) hjN) hright
    have hup₀ := mul_le_mul_of_nonneg_left (hupper j hjN.le) hleft
    have hup₁ := mul_le_mul_of_nonneg_left (hupper (j + 1) hjN) hright
    rw [profileInterpolation_on_cell g N j hjN x hjx hxj]
    push_cast at hlow₁ hup₁
    constructor <;> nlinarith
  · rw [profileInterpolation_natCast g le_rfl]
    exact ⟨hlower N le_rfl, hupper N le_rfl⟩

/-- A grid minimum bounds the interpolation on the entire integer-ended interval. -/
theorem gMin_le_profileInterpolation {g : ℕ → ℝ} {N m n : ℕ}
    (hmn : m ≤ n) (hnN : n ≤ N) {x : ℝ} (hx : x ∈ Icc (m : ℝ) n) :
    gMin g m n ≤ profileInterpolation g N x := by
  rcases lt_or_eq_of_le hx.2 with hxn | rfl
  · have hx₀ : 0 ≤ x := (Nat.cast_nonneg m).trans hx.1
    let j := ⌊x⌋₊
    have hmj : m ≤ j := Nat.le_floor hx.1
    have hjx : (j : ℝ) ≤ x := Nat.floor_le hx₀
    have hxj : x ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one x).le
    have hjn : j < n := by exact_mod_cast hjx.trans_lt hxn
    have hleft : 0 ≤ 1 - (x - j) := by linarith
    have hright : 0 ≤ x - j := sub_nonneg.mpr hjx
    have hlow₀ := mul_le_mul_of_nonneg_left (gMin_le (g := g) hmj hjn.le) hleft
    have hlow₁ := mul_le_mul_of_nonneg_left
      (gMin_le (g := g) (by omega : m ≤ j + 1) hjn) hright
    rw [profileInterpolation_on_cell g N j (hjn.trans_le hnN) x hjx hxj]
    nlinarith
  · rw [profileInterpolation_natCast g hnN]
    exact gMin_le hmn le_rfl

/-- The minimum over an integer-ended interval is exactly the discrete grid minimum. -/
theorem isLeast_profileInterpolation_image {g : ℕ → ℝ} {N m n : ℕ}
    (hmn : m ≤ n) (hnN : n ≤ N) :
    IsLeast (profileInterpolation g N '' Icc (m : ℝ) n) (gMin g m n) := by
  obtain ⟨hmk, hkn, hvalue⟩ := argMinLeft_spec (g := g) hmn
  constructor
  · refine ⟨(argMinLeft g m n : ℝ), ?_, ?_⟩
    · constructor <;> exact_mod_cast ‹_›
    · rw [profileInterpolation_natCast g (hkn.trans hnN)]
      exact hvalue
  · rintro z ⟨x, hx, rfl⟩
    exact gMin_le_profileInterpolation hmn hnN hx

/-- Taking a real infimum of the interpolation recovers the discrete minimum. -/
theorem sInf_profileInterpolation_image {g : ℕ → ℝ} {N m n : ℕ}
    (hmn : m ≤ n) (hnN : n ≤ N) :
    sInf (profileInterpolation g N '' Icc (m : ℝ) n) = gMin g m n :=
  (isLeast_profileInterpolation_image hmn hnN).csInf_eq

/-- Discrete edge costs agree exactly with the continuous interval-drop expression. -/
theorem profileInterpolation_edgeCost {g : ℕ → ℝ} {N m n : ℕ}
    (hmn : m ≤ n) (hnN : n ≤ N) :
    profileInterpolation g N m - sInf (profileInterpolation g N '' Icc (m : ℝ) n) =
      edgeCost g m n := by
  rw [profileInterpolation_natCast g (hmn.trans hnN),
    sInf_profileInterpolation_image hmn hnN]
  rfl

/-- Simultaneous horizontal and vertical rescaling of a finite profile to the unit interval. -/
def normalizedProfileInterpolation (g : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  profileInterpolation g N (N * x) / N

/-- The normalized interpolation retains its grid values with the same vertical rescaling. -/
theorem normalizedProfileInterpolation_natCast (g : ℕ → ℝ) {N j : ℕ}
    (hN : 0 < N) (hj : j ≤ N) :
    normalizedProfileInterpolation g N (j / N) = g j / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [normalizedProfileInterpolation, mul_div_cancel₀ _ hN',
    profileInterpolation_natCast g hj]

/-- The normalized interpolation is continuous on the entire real line. -/
theorem continuous_normalizedProfileInterpolation (g : ℕ → ℝ) (N : ℕ) :
    Continuous (normalizedProfileInterpolation g N) := by
  unfold normalizedProfileInterpolation
  exact ((continuous_profileInterpolation g N).comp
    (continuous_const.mul continuous_id)).div_const _

/-- Equal horizontal and vertical rescaling preserves the unit Lipschitz constant. -/
theorem lipschitzWith_normalizedProfileInterpolation {g : ℕ → ℝ} {N : ℕ}
    (hN : 0 < N) (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) :
    LipschitzWith 1 (normalizedProfileInterpolation g N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply LipschitzWith.mk_one
  intro x y
  have hdist := (lipschitzWith_profileInterpolation hlip).dist_le_mul (N * x) (N * y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, ← mul_sub, abs_mul,
    abs_of_pos hN'] at hdist
  simp only [Real.dist_eq, normalizedProfileInterpolation, ← sub_div, abs_div,
    abs_of_pos hN']
  exact (div_le_iff₀ hN').mpr (by nlinarith [hdist])

/-- The normalized interpolation satisfies the same linear barriers on the unit interval. -/
theorem normalizedProfileInterpolation_barriers {g : ℕ → ℝ} {N : ℕ} {a b : ℝ}
    (hN : 0 < N) (hlower : ∀ j, j ≤ N → a * j ≤ g j)
    (hupper : ∀ j, j ≤ N → g j ≤ b * j) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    a * x ≤ normalizedProfileInterpolation g N x ∧
      normalizedProfileInterpolation g N x ≤ b * x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNx : (N : ℝ) * x ∈ Icc (0 : ℝ) N :=
    ⟨mul_nonneg hN'.le hx.1, by nlinarith [hx.2]⟩
  obtain ⟨hlow, hup⟩ := profileInterpolation_barriers hlower hupper hNx
  constructor
  · exact (le_div_iff₀ hN').mpr (by nlinarith [hlow])
  · exact (div_le_iff₀ hN').mpr (by nlinarith [hup])

/-- The rescaled real interval has precisely the rescaled discrete minimum. -/
theorem isLeast_normalizedProfileInterpolation_image {g : ℕ → ℝ} {N m n : ℕ}
    (hN : 0 < N) (hmn : m ≤ n) (hnN : n ≤ N) :
    IsLeast (normalizedProfileInterpolation g N '' Icc (m / N : ℝ) (n / N))
      (gMin g m n / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hmk, hkn, hvalue⟩ := argMinLeft_spec (g := g) hmn
  constructor
  · refine ⟨(argMinLeft g m n : ℝ) / N, ?_, ?_⟩
    · constructor <;> apply (div_le_div_iff_of_pos_right hN').mpr <;> exact_mod_cast ‹_›
    · rw [normalizedProfileInterpolation_natCast g hN (hkn.trans hnN), hvalue]
  · rintro z ⟨x, hx, rfl⟩
    apply (div_le_div_iff_of_pos_right hN').mpr
    apply gMin_le_profileInterpolation hmn hnN
    exact ⟨by nlinarith [(div_le_iff₀ hN').mp hx.1],
      by nlinarith [(le_div_iff₀ hN').mp hx.2]⟩

/-- Normalized continuous interval drops agree with the discrete edge cost divided by scale. -/
theorem normalizedProfileInterpolation_edgeCost {g : ℕ → ℝ} {N m n : ℕ}
    (hN : 0 < N) (hmn : m ≤ n) (hnN : n ≤ N) :
    normalizedProfileInterpolation g N (m / N) -
      sInf (normalizedProfileInterpolation g N '' Icc (m / N : ℝ) (n / N)) =
        edgeCost g m n / N := by
  rw [normalizedProfileInterpolation_natCast g hN (hmn.trans hnN),
    (isLeast_normalizedProfileInterpolation_image hN hmn hnN).csInf_eq, ← sub_div]
  rfl

end FalconerPacking
