/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summation of the scalar Fourier-band estimates

The quadratic low-frequency gain and the negative high-frequency power give a summable sequence
over every integer dyadic scale. The resulting constant is independent of the displacement.
-/

noncomputable section

namespace FalconerPacking

/-- The scalar coefficient of a dyadic frequency band. -/
def dyadicBandTerm (δ s : ℝ) (n : ℤ) : ℝ :=
  min 1 ((δ * (2 : ℝ) ^ n) ^ 2) * ((2 : ℝ) ^ n) ^ (1 - s)

theorem dyadicBandTerm_nonneg (δ s : ℝ) (n : ℤ) : 0 ≤ dyadicBandTerm δ s n := by
  unfold dyadicBandTerm
  positivity

private lemma dyadicBandTerm_le_high_aux (δ s : ℝ) (n : ℤ) :
    dyadicBandTerm δ s n ≤ ((2 : ℝ) ^ n) ^ (1 - s) := by
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans_eq (one_mul _)

private lemma dyadicBandTerm_le_low_aux (δ s : ℝ) (n : ℤ) :
    dyadicBandTerm δ s n ≤ δ ^ 2 * ((2 : ℝ) ^ n) ^ (3 - s) := by
  have hR : 0 < (2 : ℝ) ^ n := zpow_pos (by norm_num) _
  calc
    dyadicBandTerm δ s n ≤ (δ * (2 : ℝ) ^ n) ^ 2 * ((2 : ℝ) ^ n) ^ (1 - s) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = δ ^ 2 * ((2 : ℝ) ^ n) ^ (3 - s) := by
      rw [mul_pow, mul_assoc, ← Real.rpow_two ((2 : ℝ) ^ n), ← Real.rpow_add hR]
      congr 2
      ring

private lemma dyadic_rpow_add_nat_aux (k : ℤ) (n : ℕ) (z : ℝ) :
    ((2 : ℝ) ^ (k + n)) ^ z = ((2 : ℝ) ^ k) ^ z * ((2 : ℝ) ^ z) ^ n := by
  rw [zpow_add₀ (by norm_num), zpow_natCast, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num), mul_comm (n : ℝ),
    Real.rpow_mul_natCast (by norm_num)]

private lemma dyadic_rpow_sub_nat_aux (k : ℤ) (n : ℕ) (z : ℝ) :
    ((2 : ℝ) ^ (k - n)) ^ z = ((2 : ℝ) ^ k) ^ z * ((2 : ℝ) ^ (-z)) ^ n := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_neg, zpow_natCast,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
    ← Real.rpow_neg (by positivity), ← Real.rpow_natCast_mul (by norm_num),
    mul_comm (n : ℝ), Real.rpow_mul_natCast (by norm_num)]

private lemma exists_dyadic_displacement_bracket_aux {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℤ, 1 / 2 ≤ δ * (2 : ℝ) ^ k ∧ δ * (2 : ℝ) ^ k ≤ 1 := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow (inv_pos.2 hδ)
    (show (1 : ℝ) < 2 by norm_num)
  refine ⟨k, ?_, ?_⟩
  · rw [zpow_add₀ (by norm_num), zpow_one] at hk'
    have h := mul_lt_mul_of_pos_left hk' hδ
    rw [mul_inv_cancel₀ hδ.ne'] at h
    nlinarith
  · have h := mul_le_mul_of_nonneg_left hk hδ.le
    simpa only [mul_inv_cancel₀ hδ.ne'] using h

private lemma displacement_high_coefficient_aux {δ s a : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hs : 1 < s) (hlo : 1 / 2 ≤ δ * a) :
    a ^ (1 - s) ≤ (2 : ℝ) ^ (s - 1) * δ ^ (s - 1) := by
  have heq : δ ^ (s - 1) * (δ * a) ^ (1 - s) = a ^ (1 - s) := by
    rw [Real.mul_rpow hδ.le ha.le, ← mul_assoc, ← Real.rpow_add hδ]
    simp
  rw [← heq]
  have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2) hlo
    (show 1 - s ≤ 0 by linarith)
  have hp : (1 / 2 : ℝ) ^ (1 - s) = (2 : ℝ) ^ (s - 1) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hp] at h
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (by positivity)

private lemma displacement_low_coefficient_aux {δ s a : ℝ} (hδ : 0 < δ) (ha : 0 < a)
    (hs : s < 3) (hhi : δ * a ≤ 1) : δ ^ 2 * a ^ (3 - s) ≤ δ ^ (s - 1) := by
  have heq : δ ^ (s - 1) * (δ * a) ^ (3 - s) = δ ^ 2 * a ^ (3 - s) := by
    rw [Real.mul_rpow hδ.le ha.le, ← mul_assoc, ← Real.rpow_add hδ]
    have hexp : s - 1 + (3 - s) = 2 := by ring
    rw [hexp, Real.rpow_two]
  rw [← heq]
  exact mul_le_of_le_one_right (by positivity)
    (Real.rpow_le_one (by positivity) hhi (by linarith))

private lemma dyadicBandTerm_shifted_bounds_aux {δ s : ℝ} (hδ : 0 < δ)
    (hs : 1 < s) (hs' : s < 3) {k : ℤ}
    (hlo : 1 / 2 ≤ δ * (2 : ℝ) ^ k) (hhi : δ * (2 : ℝ) ^ k ≤ 1) (n : ℕ) :
    dyadicBandTerm δ s (k + n) ≤
        ((2 : ℝ) ^ (s - 1) * δ ^ (s - 1)) * ((2 : ℝ) ^ (1 - s)) ^ n ∧
      dyadicBandTerm δ s (k - (n + 1)) ≤
        δ ^ (s - 1) * ((2 : ℝ) ^ (s - 3)) ^ n := by
  have hkpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  constructor
  · calc
      dyadicBandTerm δ s (k + n) ≤ ((2 : ℝ) ^ (k + n)) ^ (1 - s) :=
        dyadicBandTerm_le_high_aux _ _ _
      _ = ((2 : ℝ) ^ k) ^ (1 - s) * ((2 : ℝ) ^ (1 - s)) ^ n :=
        dyadic_rpow_add_nat_aux _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (displacement_high_coefficient_aux hδ hkpos hs hlo) (by positivity)
  · have hr₀ : 0 ≤ (2 : ℝ) ^ (s - 3) := by positivity
    have hr₁ : (2 : ℝ) ^ (s - 3) ≤ 1 :=
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
    calc
      dyadicBandTerm δ s (k - (n + 1)) ≤
          δ ^ 2 * ((2 : ℝ) ^ (k - (n + 1))) ^ (3 - s) :=
        dyadicBandTerm_le_low_aux _ _ _
      _ = (δ ^ 2 * ((2 : ℝ) ^ k) ^ (3 - s)) *
          ((2 : ℝ) ^ (s - 3)) ^ (n + 1) := by
        rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
          dyadic_rpow_sub_nat_aux, neg_sub, mul_assoc]
      _ ≤ δ ^ (s - 1) * ((2 : ℝ) ^ (s - 3)) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right (displacement_low_coefficient_aux hδ hkpos hs' hhi)
          (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by rw [pow_succ]; exact mul_le_of_le_one_right (by positivity) hr₁) (by positivity)

private lemma summable_of_shifted_geometric_bounds_aux (f : ℤ → ℝ) (k : ℤ)
    {A B q r : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hf : ∀ j, 0 ≤ f j)
    (hhi : ∀ n : ℕ, f (k + n) ≤ A * q ^ n)
    (hlo : ∀ n : ℕ, f (k - (n + 1)) ≤ B * r ^ n) :
    Summable f ∧ (∑' j : ℤ, f j) ≤ A * (1 - q)⁻¹ + B * (1 - r)⁻¹ := by
  let g (j : ℤ) := f (k + j)
  have hq := (summable_geometric_of_lt_one hq₀ hq₁).mul_left A
  have hr := (summable_geometric_of_lt_one hr₀ hr₁).mul_left B
  have hg₁ : Summable (fun n : ℕ ↦ g n) :=
    hq.of_nonneg_of_le (fun n ↦ hf _) hhi
  have hg₂ : Summable (fun n : ℕ ↦ g (-(n + 1))) :=
    hr.of_nonneg_of_le (fun n ↦ hf _) (by simpa only [g, sub_eq_add_neg] using hlo)
  have hg : Summable g := hg₁.of_nat_of_neg_add_one hg₂
  have hf' : Summable f := (Equiv.addLeft k).summable_iff.1 hg
  refine ⟨hf', ?_⟩
  rw [← (Equiv.addLeft k).tsum_eq f]
  change (∑' j : ℤ, g j) ≤ A * (1 - q)⁻¹ + B * (1 - r)⁻¹
  rw [← tsum_nat_add_neg_add_one hg, hg₁.tsum_add hg₂]
  have hb₁ := hg₁.tsum_le_tsum hhi hq
  have hb₂ := hg₂.tsum_le_tsum (by simpa only [g, sub_eq_add_neg] using hlo) hr
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁] at hb₁
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr₁] at hb₂
  exact add_le_add hb₁ hb₂

/-- The constant in the dyadic band sum, depending only on the Frostman exponent. -/
def dyadicBandSumConstant (s : ℝ) : ℝ :=
  (2 : ℝ) ^ (s - 1) * (1 - (2 : ℝ) ^ (1 - s))⁻¹ +
    (1 - (2 : ℝ) ^ (s - 3))⁻¹

theorem dyadicBandSumConstant_pos {s : ℝ} (hs : 1 < s) (hs' : s < 3) :
    0 < dyadicBandSumConstant s := by
  have hq : (2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr : (2 : ℝ) ^ (s - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold dyadicBandSumConstant
  positivity

/-- The dyadic band series converges with the exact displacement power and no logarithmic loss. -/
theorem summable_dyadicBandTerm_and_tsum_le {s δ : ℝ}
    (hs : 1 < s) (hs' : s < 3) (hδ : 0 < δ) :
    Summable (dyadicBandTerm δ s) ∧
      (∑' n : ℤ, dyadicBandTerm δ s n) ≤ dyadicBandSumConstant s * δ ^ (s - 1) := by
  obtain ⟨k, hlo, hhi⟩ := exists_dyadic_displacement_bracket_aux hδ
  have hq : (2 : ℝ) ^ (1 - s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr : (2 : ℝ) ^ (s - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨hsm, hbound⟩ := summable_of_shifted_geometric_bounds_aux (dyadicBandTerm δ s) k
    (by positivity) hq (by positivity) hr (dyadicBandTerm_nonneg δ s)
    (fun n ↦ (dyadicBandTerm_shifted_bounds_aux hδ hs hs' hlo hhi n).1)
    (fun n ↦ (dyadicBandTerm_shifted_bounds_aux hδ hs hs' hlo hhi n).2)
  refine ⟨hsm, hbound.trans_eq ?_⟩
  unfold dyadicBandSumConstant
  ring

/-- Every finite selection of dyadic bands obeys the same uniform bound. -/
theorem sum_dyadicBandTerm_le {s δ : ℝ} (hs : 1 < s) (hs' : s < 3) (hδ : 0 < δ)
    (S : Finset ℤ) :
    (∑ n ∈ S, dyadicBandTerm δ s n) ≤ dyadicBandSumConstant s * δ ^ (s - 1) := by
  obtain ⟨hsm, hbound⟩ := summable_dyadicBandTerm_and_tsum_le hs hs' hδ
  exact (hsm.sum_le_tsum S (fun n _ ↦ dyadicBandTerm_nonneg δ s n)).trans hbound

end FalconerPacking
