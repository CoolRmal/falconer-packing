/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RetainedChainScalarDecay
public import FalconerPacking.RetainedChainConstantBound

/-!
# Nonnegative scalar decay of the complete retained energy

The finite-chain coefficient is converted to the literal main scalar expression.
The four terms then have a common summable geometric rate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The actual nonnegative chain coefficient has the main scalar power, with its factor50. -/
theorem retained_chain_main_ennreal_le {h η ζ B s : ℝ} (hB : 0 < B)
    (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1) (T N : ℕ) (E : ℝ≥0∞)
    (hE : E ≤ 50 * (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N)) :
    let R := (2 : ℝ) ^ (T * N)
    let U := B * R
    let L := (2 : ℝ) ^ (h * T * N)
    let a := ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹
    ENNReal.ofReal ((4 * U) ^ 2) * ENNReal.ofReal (L ^ 2 * a) ^ 2 * E *
        ENNReal.ofReal (1 / R) * ENNReal.ofReal ((2 * U) ^ (2 - s)) ≤
      ENNReal.ofReal (50 * (16 * B ^ 2 * (2 * B) ^ (2 - s) * (2 : ℝ) ^ (2 * T))) *
        (2 : ℝ≥0∞) ^ ((4 * h + 2 * ζ - η / 2) * T * N) := by
  dsimp only
  have hmain := retained_chain_main_scalar_le (h := h) (η := η) (s := s) hB hζ hζ₁ T N
  dsimp only at hmain
  have he : (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N) =
      ENNReal.ofReal (((2 : ℝ) ^ (T * N)) ^ (s - 1 - η / 2)) := by
    rw [← Real.rpow_natCast 2 (T * N), ← Real.rpow_mul (by norm_num)]
    push_cast
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
    congr 1
    ring
  have ht : (2 : ℝ≥0∞) ^ ((4 * h + 2 * ζ - η / 2) * T * N) =
      ENNReal.ofReal ((2 : ℝ) ^ ((4 * h + 2 * ζ - η / 2) * T * N)) := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [ht]
  apply le_trans (by gcongr : _ ≤
    ENNReal.ofReal ((4 * (B * (2 : ℝ) ^ (T * N))) ^ 2) *
      ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ 2 *
        ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹) ^ 2 *
      (50 * (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N)) *
      ENNReal.ofReal (1 / (2 : ℝ) ^ (T * N)) *
      ENNReal.ofReal ((2 * (B * (2 : ℝ) ^ (T * N))) ^ (2 - s)))
  rw [he]
  have hm := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 50))
  repeat rw [ENNReal.ofReal_mul (by positivity)] at hm
  rw [← ENNReal.ofReal_pow (show 0 ≤ ((2 : ℝ) ^ (h * T * N)) ^ 2 *
    ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹ by positivity)]
  repeat rw [ENNReal.ofReal_mul (by positivity)]
  convert hm using 1 <;> first | rfl | (simp only [one_div, ENNReal.ofReal_ofNat]; ring)

/-- The four literal retained-energy terms have one positive geometric rate. -/
theorem exists_retained_four_term_rate {η h ζ s B C₁ C₂ C₅ C : ℝ}
    (hη : 0 < η) (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1) (hB : 1 ≤ B)
    (hC₂ : 0 ≤ C₂) (hC₅ : 0 ≤ C₅) (hC : 0 ≤ C)
    {J T m q : ℕ} (hJ : 0 < J) (hT : 0 < T)
    (hmain : 4 * h + 2 * ζ - η / 2 ≤ -η / 8)
    (hloc : 3 - s - m * (2 * h + ζ) ≤ -1)
    (hrec : (8 * (J * T) : ℝ) - 2 * q ≤ -1) (hq : 1 ≤ q) :
    ∃ A α : ℝ, 0 < A ∧ 0 < α ∧ ∀ (k : ℕ) (E : ℝ≥0∞),
      let N := 4 * J * k
      let R := (2 : ℝ) ^ (T * N)
      let U := B * R
      let L := (2 : ℝ) ^ (h * T * N)
      let a := ((2 : ℝ) ^ (T * Nat.floor ((1 - ζ) * N)))⁻¹
      2 ≤ L → E ≤ 50 * (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N) →
      ENNReal.ofReal C *
        (ENNReal.ofReal ((4 * U) ^ 2) * ENNReal.ofReal (L ^ 2 * a) ^ 2 * E *
            ENNReal.ofReal (1 / R) * ENNReal.ofReal ((2 * U) ^ (2 - s)) +
          ENNReal.ofReal (((4 * U) ^ 2 * C₂ /
            (1 + 4 * U * (L ^ 2 * a / 2 - a)) ^ m) *
            (1 / R) * (2 * U) ^ (2 - s)) +
          ENNReal.ofReal ((C₁ / ((2 : ℝ) ^ k) ^ q) ^ 2 * (2 * U) ^ 2) +
          ENNReal.ofReal (C₅ / ((2 : ℝ) ^ k) ^ q)) ≤
        ENNReal.ofReal A * (2 : ℝ≥0∞) ^ (-α * k) := by
  obtain ⟨α, hα, hr⟩ := exists_common_retained_scalar_rate hη hJ hT hmain hloc hrec hq
  let M := 50 * (16 * B ^ 2 * (2 * B) ^ (2 - s) * (2 : ℝ) ^ (2 * T))
  let V := 16 * C₂ * B ^ 2 * (2 * B) ^ (2 - s)
  let Z := 4 * C₁ ^ 2 * B ^ 2
  have hB₀ : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let A := C * (M + V + Z + C₅) + 1
  refine ⟨A, α, by dsimp [A]; positivity, hα, ?_⟩
  intro k E
  dsimp only
  intro hL hE
  have hp (x : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ x) = (2 : ℝ≥0∞) ^ x := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hXm := retained_chain_main_ennreal_le (h := h) hB₀ hζ hζ₁ T (4 * J * k) E hE
  dsimp only at hXm
  have hrM : (2 : ℝ≥0∞) ^ ((4 * h + 2 * ζ - η / 2) * T * (4 * J * k : ℕ)) ≤
      (2 : ℝ≥0∞) ^ (-α * k) := by
    simpa only [hp] using ENNReal.ofReal_le_ofReal (hr k).1
  have hX := hXm.trans (mul_le_mul_right hrM (ENNReal.ofReal M))
  have hYreal := (retained_chain_localization_scalar_le
    (s := s) hB hζ₁ hC₂ T (4 * J * k) m hL).trans
      (mul_le_mul_of_nonneg_left (hr k).2.1 hV)
  have hY := ENNReal.ofReal_le_ofReal hYreal
  rw [ENNReal.ofReal_mul hV, hp] at hY
  have hZreal := mul_le_mul_of_nonneg_left (hr k).2.2.1 hZ
  have hZbound : (C₁ / ((2 : ℝ) ^ k) ^ q) ^ 2 *
      (2 * (B * (2 : ℝ) ^ (T * (4 * J * k)))) ^ 2 ≤ Z * (2 : ℝ) ^ (-α * k) := by
    rw [show T * (4 * J * k) = 4 * (J * T) * k by ring,
      retained_reconstruction_scalar_eq C₁ B J T k q]
    exact hZreal
  have hZenn := ENNReal.ofReal_le_ofReal hZbound
  rw [ENNReal.ofReal_mul hZ, hp] at hZenn
  have hW := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hr k).2.2.2 hC₅)
  rw [mul_one_div, ENNReal.ofReal_mul hC₅, hp] at hW
  calc
    _ ≤ ENNReal.ofReal C *
        (ENNReal.ofReal M * (2 : ℝ≥0∞) ^ (-α * k) +
          ENNReal.ofReal V * (2 : ℝ≥0∞) ^ (-α * k) +
          ENNReal.ofReal Z * (2 : ℝ≥0∞) ^ (-α * k) +
          ENNReal.ofReal C₅ * (2 : ℝ≥0∞) ^ (-α * k)) := by
      simpa only [one_div] using
        mul_le_mul_right (add_le_add (add_le_add (add_le_add hX hY) hZenn) hW) (ENNReal.ofReal C)
    _ = ENNReal.ofReal (C * (M + V + Z + C₅)) * (2 : ℝ≥0∞) ^ (-α * k) := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add (by positivity) hC₅,
        ENNReal.ofReal_add (add_nonneg hM hV) hZ, ENNReal.ofReal_add hM hV]
      ring
    _ ≤ _ := by
      gcongr
      dsimp [A]
      linarith

end FalconerPacking
