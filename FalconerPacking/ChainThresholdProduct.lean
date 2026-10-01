/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ProfileChainSequences
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Products of the actual finite-chain threshold factors

Every edge threshold is retained. A uniform polynomial factor is separated from the
sum of profile costs before any asymptotic exponent is absorbed.
-/

noncomputable section

open Finset
open scoped ENNReal

namespace FalconerPacking

/-- Products of positive dyadic exponentials add their exponents, including negative exponents. -/
theorem prod_dyadic_ennreal_rpow {ι : Type*} (I : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ I, (2 : ℝ≥0∞) ^ f i) = (2 : ℝ≥0∞) ^ (∑ i ∈ I, f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]

/-- A uniform factor can be removed from a finite exponential product exactly. -/
theorem prod_common_dyadic_factor (P : ℝ≥0∞) (v T : ℝ) (c : ℕ → ℝ) (k : ℕ) :
    (∏ j ∈ Finset.range k, P * (2 : ℝ≥0∞) ^ (v + T * c j)) =
      P ^ k * (2 : ℝ≥0∞) ^ ((k : ℝ) * v + T * ∑ j ∈ Finset.range k, c j) := by
  rw [Finset.prod_mul_distrib, prod_dyadic_ennreal_rpow]
  simp only [Finset.prod_const, Finset.card_range, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]

/-- Every partial product is bounded by the full product when all edge factors are at least one. -/
theorem prod_range_le_prod_range_ennreal {A : ℕ → ℝ≥0∞} {j k : ℕ}
    (hjk : j ≤ k) (hA : ∀ i < k, 1 ≤ A i) :
    (∏ i ∈ Finset.range j, A i) ≤ ∏ i ∈ Finset.range k, A i := by
  exact Finset.prod_le_prod_of_subset_of_one_le (Finset.range_mono hjk) (fun _ _ ↦ bot_le)
    (fun i hi _ ↦ hA i (Finset.mem_range.mp hi))

/-- Actual edge thresholds give one explicit full-product bound. `v` is the per-edge
exponential inflation; `D` bounds the geometric deletion constant. -/
theorem marked_chain_threshold_product_le
    {C D L v S : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D) (hL : 1 ≤ L) (hv : 0 ≤ v)
    {K k T N : ℕ} (hk : k ≤ K) (c : ℕ → ℝ) (H : ℕ → ℝ≥0∞)
    (hH : ∀ j < k, H j ≤ ENNReal.ofReal (D * (N + 1)) *
      ENNReal.ofReal (L ^ (20 * K + 100)) *
      (2 : ℝ≥0∞) ^ (v + 3 * N + 3 * T + T * c j))
    (hcost : (∑ j ∈ Finset.range k, c j) ≤ S) :
    (∏ j ∈ Finset.range k, ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j) ≤
      ENNReal.ofReal ((C * D * (N + 1)) ^ K) *
        ENNReal.ofReal (L ^ (K * (28 * K + 114))) *
        (2 : ℝ≥0∞) ^ ((K : ℝ) * (v + 3 * N + 3 * T) + T * S) := by
  let P : ℝ := C * D * (N + 1) * L ^ (28 * K + 114)
  have hC₀ : 0 ≤ C := le_trans zero_le_one hC
  have hD₀ : 0 ≤ D := le_trans zero_le_one hD
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  have hP : 1 ≤ P := by
    dsimp [P]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hD)
        (by norm_num)) (one_le_pow₀ hL)
  have hstep (j : ℕ) (hj : j < k) :
      ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j ≤
        ENNReal.ofReal P * (2 : ℝ≥0∞) ^ ((v + 3 * N + 3 * T) + T * c j) := by
    refine (mul_le_mul_right (hH j hj) _).trans ?_
    have hpow : L ^ (8 * j + 14) ≤ L ^ (8 * K + 14) :=
      pow_le_pow_right₀ hL (by omega)
    calc
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * K + 14)) *
          (ENNReal.ofReal (D * (N + 1)) * ENNReal.ofReal (L ^ (20 * K + 100)) *
            (2 : ℝ≥0∞) ^ (v + 3 * N + 3 * T + T * c j)) := by
        gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul hC₀,
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        dsimp [P]
        rw [show 28 * K + 114 = (8 * K + 14) + (20 * K + 100) by omega, pow_add]
        ring
  have hprod := Finset.prod_le_prod (fun _ _ ↦ bot_le) (fun j hj ↦ hstep j (Finset.mem_range.mp hj))
  rw [prod_common_dyadic_factor] at hprod
  refine hprod.trans ?_
  have hPk : (ENNReal.ofReal P) ^ k ≤ (ENNReal.ofReal P) ^ K :=
    pow_le_pow_right₀ (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP) hk
  have hexp : (k : ℝ) * (v + 3 * N + 3 * T) + T * ∑ j ∈ Finset.range k, c j ≤
      (K : ℝ) * (v + 3 * N + 3 * T) + T * S := by
    have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
    exact add_le_add (mul_le_mul_of_nonneg_right hk' (by positivity))
      (mul_le_mul_of_nonneg_left hcost (Nat.cast_nonneg T))
  have hepow : (2 : ℝ≥0∞) ^ ((k : ℝ) * (v + 3 * N + 3 * T) +
      T * ∑ j ∈ Finset.range k, c j) ≤
      (2 : ℝ≥0∞) ^ ((K : ℝ) * (v + 3 * N + 3 * T) + T * S) :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hp := mul_le_mul hPk hepow bot_le bot_le
  apply hp.trans_eq
  rw [← ENNReal.ofReal_pow (le_trans zero_le_one hP), show P ^ K =
      (C * D * (N + 1)) ^ K * L ^ (K * (28 * K + 114)) by
        dsimp [P]; rw [mul_pow, ← pow_mul, Nat.mul_comm],
    ENNReal.ofReal_mul (by positivity), mul_assoc]

end FalconerPacking
