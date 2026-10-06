/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.UniformInheritedPacketL1
public import FalconerPacking.DyadicInitialReconstruction
public import FalconerPacking.StrictShellParameters

/-!
# Explicit coefficients of actual inherited packet deletion

The complete packet count, literal multiplicity ceiling, parent overlap, and cap tail are
bounded on the same concrete dyadic grid used for initial reconstruction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- The literal packet multiplicity loses only one power of the base scale. -/
theorem physical_packet_multiplicity_le {δ x : ℝ} (hδ : 0 < δ) (hx : 1 ≤ x) (T : ℕ) :
    (Nat.ceil (13 * (48 * (x / x ^ (2 * T)) * (64 * x ^ (2 * T)) / δ +
      4 * Real.pi)) : ℝ) ≤ (13 * (3072 / δ + 4 * Real.pi) + 1) * x := by
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have he : 48 * (x / x ^ (2 * T)) * (64 * x ^ (2 * T)) / δ =
      3072 * x / δ := by field_simp; ring
  rw [he]
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ 13 * (3072 * x / δ + 4 * Real.pi))
  have hπ : 0 ≤ 13 * (4 * Real.pi) + 1 := by positivity
  have hm := mul_le_mul_of_nonneg_left hx hπ
  ring_nf at hc hm ⊢
  linarith

/-- The sum of all actual parent-enlargement overlap bounds has a fixed polynomial degree. -/
theorem sum_physical_parent_overlap_le {x : ℝ} (hx : 1 ≤ x) (K : ℕ) :
    ∑ j ∈ Finset.range K, (49 : ℝ) * (x ^ (2 * (j + 1) + 2)) ^ 2 ≤
      49 * K * x ^ (4 * K + 8) := by
  calc
    _ ≤ ∑ _j ∈ Finset.range K, (49 : ℝ) * x ^ (4 * K + 8) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← pow_mul]
      exact pow_le_pow_right₀ hx (by have := Finset.mem_range.mp hj; omega)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The actual finite source-packet family, including every cap and every spatial strip,
has degree at most four times the packet integer. -/
theorem card_dyadic_source_packets_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {T : ℕ} (hT : 0 < T) (n : ℕ) :
    let x := (2 : ℝ) ^ n
    let N := 64 * 2 ^ (2 * T * n)
    let J := sourceWavePacketIndices χ hχ (x / x ^ (2 * T))
    (((Finset.range N) ×ˢ J).card : ℝ) ≤
      64 * (2 * sourceCutoffRadius χ hχ + 3) * x ^ (4 * T) := by
  dsimp only
  have hx : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hc := card_initial_strip_grid_le χ hχ hT hx
  have hN : ((64 * 2 ^ (2 * T * n) : ℕ) : ℝ) = 64 * ((2 : ℝ) ^ n) ^ (2 * T) := by
    push_cast
    rw [← pow_mul]
    congr 2
    ring
  rw [Finset.card_product, Finset.card_range, Nat.cast_mul, hN]
  calc
    _ ≤ (64 * ((2 : ℝ) ^ n) ^ (2 * T)) *
        ((2 * sourceCutoffRadius χ hχ + 3) * ((2 : ℝ) ^ n) ^ (2 * T)) := by gcongr
    _ = _ := by rw [show 4 * T = 2 * T + 2 * T by omega, pow_add]; ring

/-- The kernel tail denominator is exactly the base dyadic scale, not just a comparable one. -/
theorem dyadic_cap_tail_denominator (T n : ℕ) :
    Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) *
      ((2 : ℝ) ^ n / ((2 : ℝ) ^ n) ^ (2 * T)) = (2 : ℝ) ^ n := by
  rw [show (4 * T) * n = 2 * (2 * T * n) by ring, sqrt_even_dyadic_frequency]
  have he : (2 : ℝ) ^ (2 * T * n) = ((2 : ℝ) ^ n) ^ (2 * T) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [he]
  field_simp

/-- Arbitrarily rapid cap tails survive the complete actual packet count. -/
theorem dyadic_packet_tail_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {T : ℕ} (hT : 0 < T) {C : ℝ} (hC : 0 ≤ C) (p m n : ℕ) (hm : 4 * T + p ≤ m) :
    let x := (2 : ℝ) ^ n
    let N := 64 * 2 ^ (2 * T * n)
    let J := sourceWavePacketIndices χ hχ (x / x ^ (2 * T))
    C / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) * (x / x ^ (2 * T))) ^ m *
      (((Finset.range N) ×ˢ J).card : ℝ) ≤
      (C * 64 * (2 * sourceCutoffRadius χ hχ + 3)) / x ^ p := by
  dsimp only
  rw [dyadic_cap_tail_denominator]
  have hc := card_dyadic_source_packets_le χ hχ hT n
  have hx : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  calc
    _ ≤ (C / ((2 : ℝ) ^ n) ^ m) *
        (64 * (2 * sourceCutoffRadius χ hχ + 3) * ((2 : ℝ) ^ n) ^ (4 * T)) := by
      gcongr
    _ = (C * 64 * (2 * sourceCutoffRadius χ hχ + 3)) *
        (((2 : ℝ) ^ n) ^ (4 * T) / ((2 : ℝ) ^ n) ^ m) := by ring
    _ ≤ (C * 64 * (2 * sourceCutoffRadius χ hχ + 3)) * (1 / ((2 : ℝ) ^ n) ^ p) := by
      exact mul_le_mul_of_nonneg_left (dyadic_initial_power_ratio hx hm)
        (by have := (sourceCutoffRadius_pos χ hχ).le; positivity)
    _ = _ := by ring


/-- All overlap and multiplicity losses are a single fixed power of the chosen enlargement
scale. The enlargement may be larger than the packet-width inflation. -/
theorem inherited_deletion_main_coefficient_le {δ x L C₀ : ℝ}
    (hδ : 0 < δ) (hx : 1 ≤ x) (hxL : x ≤ L) (hC₀ : 0 ≤ C₀)
    (T K : ℕ) (B : ℝ≥0∞) :
    ENNReal.ofReal C₀ *
      ((Nat.ceil (13 * (48 * (x / x ^ (2 * T)) * (64 * x ^ (2 * T)) / δ +
        4 * Real.pi)) : ℝ≥0∞) *
      ∑ j ∈ Finset.range K, ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) * B) ≤
    ENNReal.ofReal (C₀ * (13 * (3072 / δ + 4 * Real.pi) + 1) * 49 * K) *
      ENNReal.ofReal (L ^ (4 * K + 9)) * B := by
  have hL : 1 ≤ L := hx.trans hxL
  have hD : 0 ≤ 13 * (3072 / δ + 4 * Real.pi) + 1 := by positivity
  have hm := (physical_packet_multiplicity_le hδ hx T).trans
    (mul_le_mul_of_nonneg_left hxL hD)
  have hme := ENNReal.ofReal_le_ofReal hm
  simp only [ENNReal.ofReal_natCast] at hme
  have hs : (∑ j ∈ Finset.range K,
      ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2)) ≤
      ENNReal.ofReal (49 * K * L ^ (4 * K + 8)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
    exact ENNReal.ofReal_le_ofReal (sum_physical_parent_overlap_le hL K)
  rw [← Finset.sum_mul]
  calc
    _ ≤ ENNReal.ofReal C₀ *
        (ENNReal.ofReal ((13 * (3072 / δ + 4 * Real.pi) + 1) * L) *
          (ENNReal.ofReal (49 * K * L ^ (4 * K + 8)) * B)) := by gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC₀, ← mul_assoc,
        ← ENNReal.ofReal_mul (mul_nonneg hC₀ (mul_nonneg hD (by linarith))),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤
          C₀ * (13 * (3072 / δ + 4 * Real.pi) + 1) * 49 * K)]
      congr 2
      rw [show 4 * K + 9 = (4 * K + 8) + 1 by omega, pow_succ]
      ring

/-- The complete cap tail, as an extended nonnegative integral coefficient. -/
theorem inherited_deletion_tail_coefficient_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {T : ℕ} (hT : 0 < T) {C : ℝ} (hC : 0 ≤ C) (p m n : ℕ) (hm : 4 * T + p ≤ m) :
    let x := (2 : ℝ) ^ n
    let N := 64 * 2 ^ (2 * T * n)
    let J := sourceWavePacketIndices χ hχ (x / x ^ (2 * T))
    ENNReal.ofReal (C / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) *
      (x / x ^ (2 * T))) ^ m) * (((Finset.range N) ×ˢ J).card : ℝ≥0∞) ≤
      ENNReal.ofReal (C * 64 * (2 * sourceCutoffRadius χ hχ + 3)) /
        ENNReal.ofReal (x ^ p) := by
  dsimp only
  have h := ENNReal.ofReal_le_ofReal (dyadic_packet_tail_le χ hχ hT hC p m n hm)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast] at h
  exact h.trans_eq (ENNReal.ofReal_div_of_pos (by positivity))

end FalconerPacking
