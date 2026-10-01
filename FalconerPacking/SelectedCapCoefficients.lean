/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.EnlargedGridSquares
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Explicit coefficients for selected-cap inflation

The child area cancels the enlarged averaging area. This leaves the stated polynomial
inflation factor, while taking a sufficiently high kernel decay order makes both tails
smaller than any prescribed inverse power of the enlargement parameter.
-/

namespace FalconerPacking

/-- Cancellation of the child area and the transverse tube ratio in the main coefficient. -/
theorem selected_cap_main_coefficient_identity {a b s : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (L p Λ : ℝ) :
    (s ^ 2)⁻¹ * (a * b)⁻¹ * (Real.pi * (L * s) ^ 2) * Λ * (a / b) * p ^ 2 =
      Real.pi * Λ * L ^ 2 * (p / b) ^ 2 := by
  field_simp

/-- The prescribed parent size and the actual child overlap give the inflation exponent. -/
theorem selected_cap_main_coefficient_le {a b L Λ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (j : ℕ)
    (hΛ : Λ ≤ 49 * L ^ (4 * j + 4)) :
    ((L ^ (2 * j + 2) * a) ^ 2)⁻¹ * (a * b)⁻¹ *
        (Real.pi * (L * (L ^ (2 * j + 2) * a)) ^ 2) * Λ * (a / b) *
          (L ^ (2 * j + 4) * b) ^ 2 ≤ 49 * Real.pi * L ^ (8 * j + 14) := by
  rw [selected_cap_main_coefficient_identity ha.ne' hb.ne' (by positivity),
    mul_div_cancel_right₀ _ hb.ne']
  calc
    _ ≤ Real.pi * (49 * L ^ (4 * j + 4)) * L ^ 2 * (L ^ (2 * j + 4)) ^ 2 := by
      gcongr
    _ = _ := by
      simp only [pow_add, pow_mul]
      ring

/-- The enlarged averaging area also cancels the child area in the kernel tail. -/
theorem selected_cap_kernel_coefficient_identity {a b s : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) (L Λ : ℝ) (n : ℕ) :
    (s ^ 2)⁻¹ * (a * b)⁻¹ * (Real.pi * (L * s) ^ 2) * Λ /
        (1 + L / 2) ^ n = Real.pi * Λ * L ^ 2 / (a * b) / (1 + L / 2) ^ n := by
  congr 1
  field_simp

/-- A kernel decay order exceeding the geometric loss by p supplies the required tail. -/
theorem selected_cap_kernel_tail_le {a b L Λ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hL : 1 ≤ L)
    (j K p n : ℕ) (hj : j < K) (hn : p + 4 * K + 20 ≤ n)
    (hΛ : Λ ≤ 49 * L ^ (4 * j + 4)) :
    ((L ^ (2 * j + 2) * a) ^ 2)⁻¹ * (a * b)⁻¹ *
        (Real.pi * (L * (L ^ (2 * j + 2) * a)) ^ 2) * Λ / (1 + L / 2) ^ n ≤
      49 * Real.pi * 2 ^ n * (a ^ 2)⁻¹ * (L ^ p)⁻¹ := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hb : 0 < b := ha.trans_le hab
  rw [selected_cap_kernel_coefficient_identity ha.ne' hb.ne' (by positivity)]
  have hden : 0 < (1 + L / 2) ^ n := by positivity
  have hsq : a ^ 2 ≤ a * b := by nlinarith
  have hbase : Real.pi * Λ * L ^ 2 / (a * b) ≤
      49 * Real.pi * (a ^ 2)⁻¹ * L ^ (4 * j + 6) := by
    calc
      _ ≤ Real.pi * (49 * L ^ (4 * j + 4)) * L ^ 2 / (a ^ 2) := by
        gcongr
      _ = _ := by
        simp only [pow_add, pow_mul, div_eq_mul_inv]
        ring
  have hdecay : L ^ (4 * j + 6) / (1 + L / 2) ^ n ≤
      (2 : ℝ) ^ n * (L ^ p)⁻¹ := by
    have he : 4 * j + 6 + p ≤ n := by omega
    have hp : L ^ (4 * j + 6) * L ^ p ≤ L ^ n := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hL he
    have hl : L ^ n ≤ 2 ^ n * (1 + L / 2) ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hden (by positivity)]
    exact hp.trans hl
  calc
    _ ≤ (49 * Real.pi * (a ^ 2)⁻¹ * L ^ (4 * j + 6)) / (1 + L / 2) ^ n :=
      div_le_div_of_nonneg_right hbase hden.le
    _ = (49 * Real.pi * (a ^ 2)⁻¹) *
        (L ^ (4 * j + 6) / (1 + L / 2) ^ n) := by ring
    _ ≤ (49 * Real.pi * (a ^ 2)⁻¹) * ((2 : ℝ) ^ n * (L ^ p)⁻¹) := by
      gcongr
    _ = _ := by ring

/-- The local-orthogonality tail has at least the same arbitrary inverse-power decay. -/
theorem selected_cap_local_tail_le {a L Λ : ℝ}
    (ha : 0 < a) (hL : 1 ≤ L) (j p n : ℕ) (hp : p ≤ 2 * n)
    (hΛ : Λ ≤ 49 * L ^ (4 * j + 4)) :
    ((L ^ (2 * j + 2) * a) ^ 2)⁻¹ * Λ / (1 + L) ^ (2 * n) ≤
      49 * (a ^ 2)⁻¹ * (L ^ p)⁻¹ := by
  have hL₀ : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hbase : ((L ^ (2 * j + 2) * a) ^ 2)⁻¹ * Λ ≤ 49 * (a ^ 2)⁻¹ := by
    calc
      _ ≤ ((L ^ (2 * j + 2) * a) ^ 2)⁻¹ * (49 * L ^ (4 * j + 4)) := by
        gcongr
      _ = _ := by
        simp only [pow_add, pow_mul]
        field_simp
        ring
  have hdecay : L ^ p ≤ (1 + L) ^ (2 * n) :=
    (pow_le_pow_right₀ hL hp).trans (by gcongr; linarith)
  calc
    _ ≤ (49 * (a ^ 2)⁻¹) / (1 + L) ^ (2 * n) := by
      gcongr
    _ ≤ (49 * (a ^ 2)⁻¹) / L ^ p := by
      gcongr
    _ = _ := div_eq_mul_inv _ _

end FalconerPacking
