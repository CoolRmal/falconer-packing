/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicDeletionCoefficients

/-!
# Decay of the actual inherited-deletion coefficients

The source and pin marking thresholds overwhelm the proved geometric loss. The regularization
block controls enlargement independently of the packet integer, so every annulus is retained.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical Filter
open scoped ENNReal

namespace FalconerPacking

/-- The two marking losses combine with any prescribed geometric power. -/
theorem marking_threshold_power_le {x : ℝ≥0∞} (hx : 1 ≤ x) (hxt : x ≠ ∞)
    {a D₁ D₂ q : ℝ} (hsource : a - (q - 1) * D₁ ≤ -1)
    (hpin : a + D₁ - D₂ ≤ -1) (M : ℝ≥0∞) :
    x ^ a * (8 * (x ^ D₁) ^ (1 - q) * M + x ^ D₁ / x ^ D₂) ≤
      (8 * M + 1) * x ^ (-1 : ℝ) := by
  have hx₀ : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx)
  calc
    _ = (8 * M) * (x ^ a * x ^ (D₁ * (1 - q))) +
        x ^ a * x ^ (D₁ - D₂) := by
      rw [ENNReal.rpow_mul, ENNReal.rpow_sub _ _ hx₀ hxt]
      ring
    _ = (8 * M) * x ^ (a + D₁ * (1 - q)) + x ^ (a + (D₁ - D₂)) := by
      rw [← ENNReal.rpow_add _ _ hx₀ hxt, ← ENNReal.rpow_add _ _ hx₀ hxt]
    _ ≤ (8 * M) * x ^ (-1 : ℝ) + x ^ (-1 : ℝ) := by
      apply add_le_add
      · apply mul_le_mul' le_rfl
        apply ENNReal.rpow_le_rpow_of_exponent_le hx
        linarith
      · apply ENNReal.rpow_le_rpow_of_exponent_le hx
        linarith
    _ = _ := by ring

/-- The already constructed shell parameters imply strictly decaying actual marking powers. -/
theorem shell_threshold_parameters_marking_exponents {a A D₁ D₂ q h ρ : ℝ}
    (ha : a ≤ A) (hA : 0 ≤ A) (hh : 0 < h) (hρ : 0 ≤ ρ)
    (hsource : (A - (q - 1) * D₁) * h + A * ρ ≤ -2 * h)
    (hpin : (A + D₁ - D₂) * h + A * ρ ≤ -2 * h) :
    a - (q - 1) * D₁ ≤ -1 ∧ a + D₁ - D₂ ≤ -1 := by
  have hnonneg := mul_nonneg hA hρ
  constructor <;> nlinarith

/-- Enlarging by the regularization block preserves decay at every packet index. -/
theorem dyadic_marking_decay {B : ℕ} (hB : 0 < B) (n : ℕ)
    {a D₁ D₂ q : ℝ} (hsource : a - (q - 1) * D₁ ≤ -1)
    (hpin : a + D₁ - D₂ ≤ -1) (M : ℝ≥0∞) :
    let L := ((2 : ℝ) ^ n) ^ B
    (ENNReal.ofReal L) ^ a *
      (8 * ((ENNReal.ofReal L) ^ D₁) ^ (1 - q) * M +
        (ENNReal.ofReal L) ^ D₁ / (ENNReal.ofReal L) ^ D₂) ≤
      (8 * M + 1) * (2 : ℝ≥0∞) ^ (-(n : ℝ)) := by
  dsimp only
  have hx : (1 : ℝ) ≤ ((2 : ℝ) ^ n) ^ B := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hx' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (((2 : ℝ) ^ n) ^ B) := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hx
  apply (marking_threshold_power_le hx' ENNReal.ofReal_ne_top hsource hpin M).trans
  apply mul_le_mul' le_rfl
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- Finite scalar coefficients yield a genuine finite dyadic-decay constant. This theorem
keeps the actual radial moment explicit rather than bounding component moments uniformly. -/
theorem exists_finite_deletion_decay_constant {C₀ C₁ M : ℝ≥0∞}
    (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞) (hM : M ≠ ∞)
    {F : ℕ → ℝ≥0∞}
    (hF : ∀ᶠ n : ℕ in atTop, F n ≤
      C₀ * ((8 * M + 1) * (2 : ℝ≥0∞) ^ (-(n : ℝ))) +
      C₁ * (2 : ℝ≥0∞) ^ (-(n : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      F n ≤ ENNReal.ofReal C * (2 : ℝ≥0∞) ^ (-(n : ℝ)) := by
  let A := C₀ * (8 * M + 1) + C₁
  have hA : A ≠ ∞ := by
    dsimp [A]
    finiteness
  refine ⟨A.toReal + 1, by positivity, ?_⟩
  filter_upwards [hF] with n hn
  calc
    F n ≤ A * (2 : ℝ≥0∞) ^ (-(n : ℝ)) := by dsimp [A]; convert hn using 1; ring
    _ ≤ _ := by
      apply mul_le_mul' _ le_rfl
      calc
        A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
        _ ≤ ENNReal.ofReal (A.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)


/-- The complete literal right-hand side of the inherited-deletion theorem decays with the
base packet index, allowing an independent larger enlargement block. -/
theorem dyadic_inherited_deletion_rhs_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {T B : ℕ} (hT : 0 < T) (hB : 0 < B) (K n : ℕ)
    {δ C₀ C₁ D₁ D₂ q : ℝ} (hδ : 0 < δ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsource : (4 * K + 9 : ℝ) - (q - 1) * D₁ ≤ -1)
    (hpin : (4 * K + 9 : ℝ) + D₁ - D₂ ≤ -1) (M : ℝ≥0∞) :
    let x := (2 : ℝ) ^ n
    let L := x ^ B
    let N : ℕ := 2 ^ (6 + 2 * T * n)
    let w := x / x ^ (2 * T)
    let J := sourceWavePacketIndices χ hχ w
    let A := (ENNReal.ofReal L) ^ D₁
    let F := (ENNReal.ofReal L) ^ D₂
    ENNReal.ofReal C₀ *
      ((Nat.ceil (13 * (48 * w * N / δ + 4 * Real.pi)) : ℝ≥0∞) *
        ∑ j ∈ Finset.range K, ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) *
          (8 * A ^ (1 - q) * M + A / F)) +
      ENNReal.ofReal (C₁ / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) * w) ^ (4 * T + 1)) *
        (((Finset.range N) ×ˢ J).card : ℝ≥0∞) ≤
      (ENNReal.ofReal (C₀ * (13 * (3072 / δ + 4 * Real.pi) + 1) * 49 * K) *
        (8 * M + 1) + ENNReal.ofReal (C₁ * 64 * (2 * sourceCutoffRadius χ hχ + 3))) *
        (2 : ℝ≥0∞) ^ (-(n : ℝ)) := by
  dsimp only
  let x := (2 : ℝ) ^ n
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hxB : x ≤ x ^ B := by
    simpa only [pow_one] using pow_le_pow_right₀ hx (by omega : 1 ≤ B)
  have hcount : (2 : ℕ) ^ (6 + 2 * T * n) = 64 * 2 ^ (2 * T * n) := by
    rw [pow_add]
    norm_num
  have hcountR : ((2 ^ (6 + 2 * T * n) : ℕ) : ℝ) = 64 * x ^ (2 * T) := by
    rw [hcount]
    push_cast
    dsimp [x]
    rw [← pow_mul, show 2 * T * n = n * (2 * T) by ring]
  have hmain := inherited_deletion_main_coefficient_le hδ hx hxB hC₀ T K
    (8 * ((ENNReal.ofReal (x ^ B)) ^ D₁) ^ (1 - q) * M +
      (ENNReal.ofReal (x ^ B)) ^ D₁ / (ENNReal.ofReal (x ^ B)) ^ D₂)
  have hmark := dyadic_marking_decay hB n hsource hpin M
  have hmain' :
      ENNReal.ofReal C₀ *
        ((Nat.ceil (13 * (48 * (x / x ^ (2 * T)) * (64 * x ^ (2 * T)) / δ +
          4 * Real.pi)) : ℝ≥0∞) *
          ∑ j ∈ Finset.range K, ENNReal.ofReal (49 * ((x ^ B) ^
            (2 * (j + 1) + 2)) ^ 2) *
            (8 * ((ENNReal.ofReal (x ^ B)) ^ D₁) ^ (1 - q) * M +
              (ENNReal.ofReal (x ^ B)) ^ D₁ / (ENNReal.ofReal (x ^ B)) ^ D₂)) ≤
      ENNReal.ofReal (C₀ * (13 * (3072 / δ + 4 * Real.pi) + 1) * 49 * K) *
        ((8 * M + 1) * (2 : ℝ≥0∞) ^ (-(n : ℝ))) := by
    apply hmain.trans
    rw [mul_assoc]
    apply mul_le_mul' le_rfl
    rw [ENNReal.ofReal_pow (by positivity), ← ENNReal.rpow_natCast]
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hmark
  have htail := inherited_deletion_tail_coefficient_le χ hχ hT hC₁ 1 (4 * T + 1) n
    (by omega)
  have htail' : ENNReal.ofReal (C₁ / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) *
      (x / x ^ (2 * T))) ^ (4 * T + 1)) *
      (((Finset.range (64 * 2 ^ (2 * T * n))) ×ˢ
        sourceWavePacketIndices χ hχ (x / x ^ (2 * T))).card : ℝ≥0∞) ≤
      ENNReal.ofReal (C₁ * 64 * (2 * sourceCutoffRadius χ hχ + 3)) *
        (2 : ℝ≥0∞) ^ (-(n : ℝ)) := by
    apply htail.trans_eq
    rw [pow_one, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      div_eq_mul_inv, ENNReal.rpow_neg, ENNReal.rpow_natCast]
  rw [hcountR, hcount]
  exact (add_le_add hmain' htail').trans_eq (by ring)

end FalconerPacking
