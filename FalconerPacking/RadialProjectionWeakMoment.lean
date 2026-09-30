/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjectionLevelSet
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Smaller moments from distribution bounds

Dyadic positive level sets turn a uniform weak power bound into a quantitative smaller
moment bound. The argument uses only positive integrals, so it also applies before
integrability has been established.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A real-valued function is dominated by its positive dyadic level sets. -/
theorem ofReal_rpow_le_one_add_tsum_levels {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    ENNReal.ofReal x ^ q ≤ 1 + ∑' n : ℕ,
      {y : ℝ | (2 : ℝ) ^ n ≤ y}.indicator
        (fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q) x := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one (by simpa using ENNReal.ofReal_le_ofReal hx) hq).trans
      (le_add_right le_rfl)
  · obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (le_of_not_ge hx) (by norm_num : (1 : ℝ) < 2)
    apply (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hn'.le) hq).trans
    apply le_trans _ (le_add_left le_rfl)
    have hh := ENNReal.le_tsum n (f := fun n : ℕ ↦
      {y : ℝ | (2 : ℝ) ^ n ≤ y}.indicator
        (fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q) x)
    rw [indicator_of_mem (show x ∈ {y : ℝ | (2 : ℝ) ^ n ≤ y} from hn)] at hh
    exact hh

/-- A dyadic level contribution decays geometrically under a stronger tail exponent. -/
theorem ennreal_dyadic_level_le {p q : ℝ} {K m : ℝ≥0∞} (n : ℕ)
    (h : ENNReal.ofReal ((2 : ℝ) ^ n) ^ p * m ≤ K) :
    ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q * m ≤
      (2 : ℝ≥0∞) ^ q * K * ((2 : ℝ≥0∞) ^ (q - p)) ^ n := by
  have hpow (j : ℕ) (z : ℝ) : ENNReal.ofReal ((2 : ℝ) ^ j) ^ z =
      (2 : ℝ≥0∞) ^ ((j : ℝ) * z) := by
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [hpow] at h
  rw [hpow]
  have h' := mul_le_mul_right h ((2 : ℝ≥0∞) ^ (q + (n : ℝ) * (q - p)))
  have hleft : (2 : ℝ≥0∞) ^ (q + (n : ℝ) * (q - p)) *
      ((2 : ℝ≥0∞) ^ ((n : ℝ) * p) * m) =
      (2 : ℝ≥0∞) ^ (((n + 1 : ℕ) : ℝ) * q) * m := by
    rw [← mul_assoc, ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
    congr 2
    push_cast
    ring
  have hright : (2 : ℝ≥0∞) ^ (q + (n : ℝ) * (q - p)) * K =
      (2 : ℝ≥0∞) ^ q * K * ((2 : ℝ≥0∞) ^ (q - p)) ^ n := by
    rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num),
      ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    rw [mul_comm (q - p) (n : ℝ)]
    ac_rfl
  rwa [hleft, hright] at h'

/-- Positive dyadic level sets control the smaller moment. -/
theorem lintegral_rpow_le_dyadic_levels {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : Measurable f) {q : ℝ} (hq : 0 ≤ q) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) ≤ μ univ + ∑' n : ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q * μ {x | (2 : ℝ) ^ n ≤ f x} := by
  have hmeas (n : ℕ) : Measurable (fun x ↦
      {y : ℝ | (2 : ℝ) ^ n ≤ y}.indicator
        (fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q) (f x)) := by
    exact (measurable_const.indicator measurableSet_Ici).comp hf
  apply (lintegral_mono (fun x ↦ ofReal_rpow_le_one_add_tsum_levels hq (f x))).trans_eq
  rw [lintegral_add_left measurable_const,
    lintegral_tsum (fun n ↦ (hmeas n).aemeasurable)]
  simp only [lintegral_one]
  congr 1
  apply tsum_congr
  intro n
  have heq : (fun x ↦ {y : ℝ | (2 : ℝ) ^ n ≤ y}.indicator
      (fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q) (f x)) =
      {x | (2 : ℝ) ^ n ≤ f x}.indicator
        (fun _ ↦ ENNReal.ofReal ((2 : ℝ) ^ (n + 1)) ^ q) := by
    funext x
    simp only [Set.indicator_apply]
    rfl
  rw [heq, lintegral_indicator (measurableSet_le measurable_const hf)]
  simp

/-- A weak power tail gives every strictly smaller positive moment, with a uniform constant. -/
theorem lintegral_rpow_le_of_dyadic_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    {p q : ℝ} (hq : 0 ≤ q) {K : ℝ≥0∞}
    (htail : ∀ n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ n) ^ p *
      μ {x | (2 : ℝ) ^ n ≤ f x} ≤ K) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) ≤
      μ univ + (2 : ℝ≥0∞) ^ q * K * (1 - (2 : ℝ≥0∞) ^ (q - p))⁻¹ := by
  apply (lintegral_rpow_le_dyadic_levels μ hf hq).trans
  apply add_le_add_right
  calc
    _ ≤ ∑' n : ℕ, (2 : ℝ≥0∞) ^ q * K * ((2 : ℝ≥0∞) ^ (q - p)) ^ n :=
      ENNReal.tsum_le_tsum (fun n ↦ ennreal_dyadic_level_le n (htail n))
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

/-- Finiteness follows for every nonnegative exponent below the tail exponent. -/
theorem lintegral_rpow_lt_top_of_dyadic_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {p q : ℝ} (hq : 0 ≤ q) (hqp : q < p) {K : ℝ≥0∞} (hK : K < ∞)
    (htail : ∀ n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ n) ^ p *
      μ {x | (2 : ℝ) ^ n ≤ f x} ≤ K) :
    (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂μ) < ∞ := by
  apply (lintegral_rpow_le_of_dyadic_tail μ hf hq htail).trans_lt
  apply ENNReal.add_lt_top.mpr
  refine ⟨measure_lt_top μ univ, ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq (by norm_num)) hK) ?_⟩
  apply lt_top_iff_ne_top.mpr
  apply ENNReal.inv_ne_top.mpr
  apply ne_of_gt (tsub_pos_iff_lt.mpr ?_)
  simpa only [ENNReal.rpow_zero] using
    ENNReal.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ≥0∞) < 2)
      (by norm_num) (show q - p < 0 by linarith)

/-- Interpolating a tail estimate with the probability bound lowers both exponents. -/
theorem ennreal_tail_bound_interpolate {T z K : ℝ≥0∞} {p r : ℝ}
    (hz : z ≤ 1) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1)
    (h : T ^ p * z ≤ K) : T ^ (p * r) * z ≤ K ^ r := by
  calc
    _ ≤ T ^ (p * r) * z ^ r := by
      apply mul_le_mul_right
      simpa only [ENNReal.rpow_one] using
        ENNReal.rpow_le_rpow_of_exponent_ge hz hr₁
    _ = (T ^ p * z) ^ r := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hr₀, ← ENNReal.rpow_mul]
    _ ≤ _ := ENNReal.rpow_le_rpow h hr₀

end FalconerPacking
