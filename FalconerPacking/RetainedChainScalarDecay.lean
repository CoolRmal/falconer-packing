/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RegularShellParameters

/-!
# Scalar decay of the actual retained-circle energy coefficients

The floored initial depth is retained explicitly. These estimates keep the inverse
lower radial frequency supplied by polar integration, and absorb the fixed ratio between
the two annular radii only into constants.
-/

noncomputable section

open Filter

namespace FalconerPacking

/-- The exact initial-localization and chain factors have the claimed strict exponent,
including the fixed floor loss. -/
theorem retained_chain_main_scalar_le {h η ζ B s : ℝ} (hB : 0 < B)
    (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1) (T N : ℕ) :
    let R := (2 : ℝ) ^ (T * N)
    let U := B * R
    let L := (2 : ℝ) ^ (h * T * N)
    let a := ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹
    (4 * U) ^ 2 * (L ^ 2 * a) ^ 2 *
        R ^ (s - 1 - η / 2) * R⁻¹ * (2 * U) ^ (2 - s) ≤
      (16 * B ^ 2 * (2 * B) ^ (2 - s) * (2 : ℝ) ^ (2 * T)) *
        (2 : ℝ) ^ ((4 * h + 2 * ζ - η / 2) * T * N) := by
  dsimp only
  have hd := (initial_profile_depth_bounds hζ hζ₁ N T).2.2
  have hr : 0 < (2 : ℝ) ^ (T * N) := by positivity
  have he :
      (4 * (B * (2 : ℝ) ^ (T * N))) ^ 2 *
          (((2 : ℝ) ^ (h * T * N)) ^ 2 *
            ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹) ^ 2 *
          ((2 : ℝ) ^ (T * N)) ^ (s - 1 - η / 2) *
          ((2 : ℝ) ^ (T * N))⁻¹ *
          (2 * (B * (2 : ℝ) ^ (T * N))) ^ (2 - s) =
        (16 * B ^ 2 * (2 * B) ^ (2 - s)) *
          (2 : ℝ) ^ ((2 + 4 * h - η / 2) * T * N -
            2 * T * Nat.floor ((1 - ζ) * N)) := by
    rw [show 2 * (B * (2 : ℝ) ^ (T * N)) =
      (2 * B) * (2 : ℝ) ^ (T * N) by ring,
      Real.mul_rpow (by positivity) hr.le]
    simp only [mul_pow]
    rw [← Real.rpow_natCast 2 (T * N),
      ← Real.rpow_natCast 2 (T * Nat.floor ((1 - ζ) * N))]
    simp only [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    rw [show (4 : ℝ) ^ 2 = 16 by norm_num]
    rw [show (2 + 4 * h - η / 2) * (T : ℝ) * N -
        2 * T * Nat.floor ((1 - ζ) * N) =
      (T : ℝ) * N * 2 + h * T * N * 2 * 2 +
        (-(T * (Nat.floor ((1 - ζ) * N) : ℝ))) * 2 +
        T * N * (s - 1 - η / 2) + (-(T * (N : ℝ))) + T * N * (2 - s) by ring]
    simp only [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [he]
  calc
    _ ≤ (16 * B ^ 2 * (2 * B) ^ (2 - s)) *
        (2 : ℝ) ^ (2 * T + (4 * h + 2 * ζ - η / 2) * T * N) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith
    _ = _ := by
      rw [Real.rpow_add (by norm_num),
        show 2 * (T : ℝ) = ((2 * T : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      ring

/-- The actual floored initial depth gives the full positive localization denominator. -/
theorem retained_localization_denominator_lower {h ζ B : ℝ} (hB : 1 ≤ B)
    (hζ₁ : ζ ≤ 1) (T N : ℕ) (hL : 2 ≤ (2 : ℝ) ^ (h * T * N)) :
    let R := (2 : ℝ) ^ (T * N)
    let L := (2 : ℝ) ^ (h * T * N)
    let a := ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹
    (2 : ℝ) ^ ((2 * h + ζ) * T * N) ≤
      1 + 4 * (B * R) * (L ^ 2 * a / 2 - a) := by
  dsimp only
  have hf := Nat.floor_le (show 0 ≤ (1 - ζ) * N by positivity)
  have hfm := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg T)
  have ha : (2 : ℝ) ^ (-(1 - ζ) * T * N) ≤
      ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹ := by
    rw [← Real.rpow_natCast 2 (T * Nat.floor ((1 - ζ) * N)),
      ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith
  let L := (2 : ℝ) ^ (h * T * N)
  let a := ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹
  let R := (2 : ℝ) ^ (T * N)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have ha₀ : 0 ≤ a := by dsimp [a]; positivity
  have hspace : L ^ 2 * a / 4 ≤ L ^ 2 * a / 2 - a := by
    have hLs : 4 ≤ L ^ 2 := by dsimp [L]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hLs ha₀]
  calc
    _ = R * (L ^ 2 * (2 : ℝ) ^ (-(1 - ζ) * T * N)) := by
      dsimp [R, L]
      rw [← Real.rpow_natCast 2 (T * N),
        ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    _ ≤ R * (L ^ 2 * a) := by gcongr
    _ ≤ (B * R) * (L ^ 2 * a) := by
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hR hB) (by positivity)
    _ = 4 * (B * R) * (L ^ 2 * a / 4) := by ring
    _ ≤ 4 * (B * R) * (L ^ 2 * a / 2 - a) :=
      mul_le_mul_of_nonneg_left hspace (by positivity)
    _ ≤ _ := by dsimp [L, R, a]; linarith

/-- The literal localization remainder, including polar integration, has a negative
exponent once its derivative order is chosen. -/
theorem retained_chain_localization_scalar_le {h ζ B s C : ℝ} (hB : 1 ≤ B)
    (hζ₁ : ζ ≤ 1) (hC : 0 ≤ C) (T N m : ℕ)
    (hL : 2 ≤ (2 : ℝ) ^ (h * T * N)) :
    let R := (2 : ℝ) ^ (T * N)
    let U := B * R
    let L := (2 : ℝ) ^ (h * T * N)
    let a := ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹
    ((4 * U) ^ 2 * C / (1 + 4 * U * (L ^ 2 * a / 2 - a)) ^ m) *
        R⁻¹ * (2 * U) ^ (2 - s) ≤
      (16 * C * B ^ 2 * (2 * B) ^ (2 - s)) *
        (2 : ℝ) ^ ((3 - s - m * (2 * h + ζ)) * T * N) := by
  dsimp only
  have hB₀ : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hden := retained_localization_denominator_lower hB hζ₁ T N hL
  dsimp only at hden
  have hpow := pow_le_pow_left₀ (by positivity) hden m
  calc
    _ ≤ ((4 * (B * (2 : ℝ) ^ (T * N))) ^ 2 * C /
        ((2 : ℝ) ^ ((2 * h + ζ) * T * N)) ^ m) *
        ((2 : ℝ) ^ (T * N))⁻¹ *
        (2 * (B * (2 : ℝ) ^ (T * N))) ^ (2 - s) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by
      rw [show 2 * (B * (2 : ℝ) ^ (T * N)) =
        (2 * B) * (2 : ℝ) ^ (T * N) by ring,
        Real.mul_rpow (by positivity) (by positivity), div_eq_mul_inv]
      simp only [mul_pow]
      rw [← Real.rpow_natCast 2 (T * N)]
      simp only [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      rw [show (3 - s - (m : ℝ) * (2 * h + ζ)) * T * N =
        (T : ℝ) * N * 2 + (-((2 * h + ζ) * T * N * m)) +
          (-(T * (N : ℝ))) + T * N * (2 - s) by ring]
      simp only [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring

/-- The finite annular area times the actual reconstruction error keeps precisely the
complete packet parameter `J * T`. -/
theorem retained_reconstruction_scalar_eq (C B : ℝ) (J T k q : ℕ) :
    (C / ((2 : ℝ) ^ k) ^ q) ^ 2 *
        (2 * (B * (2 : ℝ) ^ (4 * (J * T) * k))) ^ 2 =
      4 * C ^ 2 * B ^ 2 * (2 : ℝ) ^ (((8 * (J * T) : ℝ) - 2 * q) * k) := by
  rw [div_pow, ← Real.rpow_natCast 2 k,
    ← Real.rpow_natCast 2 (4 * (J * T) * k)]
  simp only [mul_pow, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  rw [show ((8 * (J * T) : ℝ) - 2 * q) * k =
    (-(k * (q : ℝ) * 2)) + (4 * ((J : ℝ) * T) * k * 2) by ring,
    Real.rpow_add (by norm_num)]
  ring

/-- The three exact exponents and the omitted-tail power share one positive geometric
rate on the complete annular schedule. Fixed real prefactors may therefore be summed. -/
theorem exists_common_retained_scalar_rate {η h ζ s : ℝ} (hη : 0 < η)
    {J T m q : ℕ} (hJ : 0 < J) (hT : 0 < T)
    (hmain : 4 * h + 2 * ζ - η / 2 ≤ -η / 8)
    (hloc : 3 - s - m * (2 * h + ζ) ≤ -1)
    (hrec : (8 * (J * T) : ℝ) - 2 * q ≤ -1) (hq : 1 ≤ q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℕ,
      (2 : ℝ) ^ ((4 * h + 2 * ζ - η / 2) * T * (4 * J * k : ℕ)) ≤
          (2 : ℝ) ^ (-δ * k) ∧
      (2 : ℝ) ^ ((3 - s - m * (2 * h + ζ)) * T * (4 * J * k : ℕ)) ≤
          (2 : ℝ) ^ (-δ * k) ∧
      (2 : ℝ) ^ (((8 * (J * T) : ℝ) - 2 * q) * k) ≤
          (2 : ℝ) ^ (-δ * k) ∧
      1 / ((2 : ℝ) ^ k) ^ q ≤ (2 : ℝ) ^ (-δ * k) := by
  let γ := (η / 8) * 4 * (J : ℝ) * T
  have hγ : 0 < γ := by dsimp [γ]; positivity
  let δ := min γ 1
  have hδ : 0 < δ := lt_min hγ zero_lt_one
  have hδγ : δ ≤ γ := min_le_left _ _
  have hδ₁ : δ ≤ 1 := min_le_right _ _
  refine ⟨δ, hδ, fun k ↦ ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hδk := mul_le_mul_of_nonneg_right hδ₁ hk
  have hγk := mul_le_mul_of_nonneg_right hδγ hk
  have hscale : (k : ℝ) ≤ (T : ℝ) * (4 * J * k : ℕ) := by
    exact_mod_cast (show k ≤ T * (4 * J * k) from
      (Nat.le_mul_of_pos_left k (by omega : 0 < 4 * J)).trans
        (Nat.le_mul_of_pos_left _ hT))
  have hmk := mul_le_mul_of_nonneg_right hmain
    (show 0 ≤ (T : ℝ) * (4 * J * k : ℕ) by positivity)
  have hlk := mul_le_mul_of_nonneg_right hloc
    (show 0 ≤ (T : ℝ) * (4 * J * k : ℕ) by positivity)
  have hrk := mul_le_mul_of_nonneg_right hrec hk
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    dsimp [γ] at hγk
    push_cast at hmk ⊢
    nlinarith
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
  · rw [one_div, ← Real.rpow_natCast 2 k,
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [mul_le_mul_of_nonneg_right hq' hk]

end FalconerPacking
