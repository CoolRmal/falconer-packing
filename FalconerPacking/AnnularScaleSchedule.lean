/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PaddedProfileChain
public import FalconerPacking.StrictShellParameters

/-!
# A scale schedule retaining every annulus

The width integer is chosen before the regularization block. Their product is the packet
parameter, while the packet index runs through every natural number. This gives exactly the
same frequency depth as the regular profile and preserves the full annular reconstruction.
-/

@[expose] public section

noncomputable section

open Filter

namespace FalconerPacking

/-- The full annular frequency depth equals the regularized physical profile depth. -/
theorem annular_profile_depth_eq (J T k : ℕ) :
    4 * (J * T) * k = T * (4 * J * k) := by ring

/-- The physical enlargement has the chosen exponent independently of the later block size. -/
theorem annular_enlargement_eq {J : ℕ} (hJ : 0 < J) (T k : ℕ) :
    (2 : ℝ) ^ (T * k) =
      (2 : ℝ) ^ ((1 / (4 * (J : ℝ))) * T * (4 * J * k : ℕ)) := by
  have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have he : (1 / (4 * (J : ℝ))) * T * (4 * J * k : ℕ) = (T * k : ℕ) := by
    push_cast
    field_simp
  rw [he, Real.rpow_natCast]

/-- The square-root frequency is exactly the standard packet scale before its fixed factor64. -/
theorem sqrt_annular_frequency_eq (J k : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (4 * J * k)) = ((2 : ℝ) ^ k) ^ (2 * J) := by
  have he : (2 : ℝ) ^ (4 * J * k) = (((2 : ℝ) ^ k) ^ (2 * J)) ^ 2 := by
    simp only [← pow_mul]
    congr 1
    ring
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]

/-- Packet width is bounded by the enlargement times the reciprocal square-root frequency. -/
theorem annular_packet_width_le {T : ℕ} (hT : 0 < T) (J k : ℕ) :
    (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * (J * T)) ≤
      (2 : ℝ) ^ (T * k) * (Real.sqrt ((2 : ℝ) ^ (4 * (J * T) * k)))⁻¹ := by
  rw [sqrt_annular_frequency_eq, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left k hT)

/-- The rounded initial profile depth satisfies both the strict starting-scale condition
and the needed localization-loss bound. -/
theorem initial_profile_depth_bounds {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1)
    (N T : ℕ) :
    let n := Nat.floor ((1 - ζ) * N)
    (n : ℝ) ≤ (1 - ζ) * N ∧ n ≤ N ∧
      (T : ℝ) * ((N : ℝ) - n) ≤ T + ζ * T * N := by
  dsimp only
  have hlo := Nat.floor_le (show 0 ≤ (1 - ζ) * N by positivity)
  have hup := Nat.lt_floor_add_one ((1 - ζ) * N)
  have hTN := mul_le_mul_of_nonneg_left (show (N : ℝ) - ⌊(1 - ζ) * N⌋₊ ≤
      1 + ζ * N by linarith) (Nat.cast_nonneg T)
  refine ⟨hlo, ?_, ?_⟩
  · have hn : (⌊(1 - ζ) * N⌋₊ : ℝ) ≤ N := by
      nlinarith [mul_nonneg hζ (Nat.cast_nonneg N)]
    exact_mod_cast hn
  · nlinarith

/-- The actual initial pin cubes are eventually smaller than the actual packet width. -/
theorem eventually_initial_profile_cube_le_packet_width
    {J T : ℕ} (hJ : 0 < J) (hT : 0 < T) {ζ : ℝ} (hζ : ζ ≤ 1 / 4) :
    ∀ᶠ k : ℕ in atTop,
      ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * (4 * J * k : ℕ))))⁻¹ ≤
        (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * (J * T)) := by
  filter_upwards [eventually_ge_atTop T] with k hk
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hJT : (1 : ℝ) ≤ (J : ℝ) * T := by exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos hJ hT))
  have hk' : (T : ℝ) ≤ k := by exact_mod_cast hk
  have hf := Nat.lt_floor_add_one ((1 - ζ) * (4 * J * k : ℕ))
  have hfm := mul_lt_mul_of_pos_left hf hT'
  have hζm := mul_le_mul_of_nonneg_right hζ
    (show 0 ≤ (4 : ℝ) * J * T * k by positivity)
  have hJTk := mul_le_mul_of_nonneg_right hJT (Nat.cast_nonneg k)
  have hexp : 2 * (J * T) * k ≤ T * Nat.floor ((1 - ζ) * (4 * J * k : ℕ)) + k := by
    have hh : (2 : ℝ) * (J * T) * k ≤
        (T : ℝ) * Nat.floor ((1 - ζ) * (4 * J * k : ℕ)) + k := by
      push_cast at hfm ⊢
      nlinarith
    exact_mod_cast hh
  have hp := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hexp
  rw [pow_add] at hp
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  simpa only [← pow_mul, Nat.mul_comm k (2 * (J * T)), mul_comm] using hp

end FalconerPacking
