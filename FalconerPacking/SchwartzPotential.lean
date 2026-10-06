/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Schwartz potentials from local mass growth

Dyadic annuli turn quadratic mass growth into a uniform convolution-potential bound.
The only function constants are its zeroth and fourth Schwartz seminorms.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped NNReal ENNReal

namespace FalconerPacking

/-- Boundedness and fourth-order decay control integration against quadratic ball growth. -/
theorem lintegral_le_of_dyadic_ball_growth
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) {C : ℝ} (hC : 0 ≤ C) (M : ℝ≥0∞)
    (h₀ : ∀ y, f y ≤ C)
    (h₄ : ∀ y, dist y x ^ 4 * f y ≤ C)
    (hball : ∀ n : ℕ, μ (ball x ((2 : ℝ) ^ n)) ≤ M * (4 : ℝ≥0∞) ^ n) :
    ∫⁻ y, ENNReal.ofReal (f y) ∂μ ≤ 9 * ENNReal.ofReal C * M := by
  let A (n : ℕ) := {y : EuclideanSpace ℝ (Fin 2) |
    (2 : ℝ) ^ n ≤ dist y x ∧ dist y x < 2 ^ (n + 1)}
  have hAm (n : ℕ) : MeasurableSet (A n) := by
    change MeasurableSet ({y | (2 : ℝ) ^ n ≤ dist y x} ∩ {y | dist y x < 2 ^ (n + 1)})
    exact (measurableSet_le measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hcover : ball x 1 ∪ ⋃ n, A n = univ := by
    apply eq_univ_of_forall
    intro y
    by_cases h : dist y x < 1
    · exact Or.inl h
    · obtain ⟨n, hn⟩ := exists_nat_pow_near (le_of_not_gt h) (by norm_num : (1 : ℝ) < 2)
      exact Or.inr (mem_iUnion.mpr ⟨n, hn⟩)
  have hann (n : ℕ) : ∫⁻ y in A n, ENNReal.ofReal (f y) ∂μ ≤
      4 * ENNReal.ofReal C * M * (1 / 2 : ℝ≥0∞) ^ n := by
    have hdecay (y) (hy : y ∈ A n) : f y ≤ C * (1 / 16 : ℝ) ^ n := by
      by_cases hf : 0 ≤ f y
      · have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ n) hy.1 4
        have hb := (mul_le_mul_of_nonneg_right hpow hf).trans (h₄ y)
        have hpos : (0 : ℝ) < (2 ^ n) ^ 4 := by positivity
        have heq : (2 ^ n : ℝ) ^ 4 * (1 / 16 : ℝ) ^ n = 1 := by
          rw [← pow_mul, Nat.mul_comm n 4, pow_mul, ← mul_pow]
          norm_num
        apply (mul_le_mul_iff_right₀ hpos).mp
        calc
          (2 ^ n) ^ 4 * f y ≤ C := hb
          _ = (2 ^ n) ^ 4 * (C * (1 / 16 : ℝ) ^ n) := by nlinarith [heq]
      · exact (le_of_lt (lt_of_not_ge hf)).trans (by positivity)
    calc
      _ ≤ ∫⁻ _ in A n, ENNReal.ofReal (C * (1 / 16 : ℝ) ^ n) ∂μ :=
        setLIntegral_mono' (hAm n) (fun y hy ↦ ENNReal.ofReal_le_ofReal (hdecay y hy))
      _ = ENNReal.ofReal C * (1 / 16 : ℝ≥0∞) ^ n * μ (A n) := by
        rw [lintegral_const, Measure.restrict_apply_univ, ENNReal.ofReal_mul hC,
          ENNReal.ofReal_pow (by positivity)]
        norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
      _ ≤ ENNReal.ofReal C * (1 / 16 : ℝ≥0∞) ^ n * (M * 4 ^ (n + 1)) := by
        apply mul_le_mul_right
        exact (measure_mono (show A n ⊆ ball x (2 ^ (n + 1)) from fun _ hy ↦ hy.2)).trans
          (hball (n + 1))
      _ = 4 * ENNReal.ofReal C * M * (1 / 4 : ℝ≥0∞) ^ n := by
        rw [pow_succ]
        have heq : (1 / 16 : ℝ≥0∞) ^ n * 4 ^ n = (1 / 4 : ℝ≥0∞) ^ n := by
          rw [← mul_pow]
          congr 1
          have h := congrArg ENNReal.ofReal (show (1 / 16 : ℝ) * 4 = 1 / 4 by norm_num)
          simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 16),
            ENNReal.ofReal_div_of_pos] using h
        calc
          _ = 4 * ENNReal.ofReal C * M * ((1 / 16 : ℝ≥0∞) ^ n * 4 ^ n) := by ring
          _ = _ := by rw [heq]
      _ ≤ _ := by
        apply mul_le_mul_right
        apply pow_le_pow_left'
        simp only [one_div, ENNReal.inv_le_inv]
        norm_num
  calc
    _ = ∫⁻ y in ball x 1 ∪ ⋃ n, A n, ENNReal.ofReal (f y) ∂μ := by
      rw [hcover, Measure.restrict_univ]
    _ ≤ (∫⁻ y in ball x 1, ENNReal.ofReal (f y) ∂μ) +
        ∫⁻ y in ⋃ n, A n, ENNReal.ofReal (f y) ∂μ := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal C * M + ∑' n, 4 * ENNReal.ofReal C * M * (1 / 2 : ℝ≥0∞) ^ n := by
      apply add_le_add
      · calc
          _ ≤ ∫⁻ _ in ball x 1, ENNReal.ofReal C ∂μ :=
            lintegral_mono (fun y ↦ ENNReal.ofReal_le_ofReal (h₀ y))
          _ = ENNReal.ofReal C * μ (ball x 1) := by simp
          _ ≤ _ := mul_le_mul_right (by simpa using hball 0) _
      · exact (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hann)
    _ = _ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      have heq : (1 - (1 / 2 : ℝ≥0∞))⁻¹ = 2 := by
        rw [one_div, ENNReal.one_sub_inv_two, inv_inv]
      rw [heq]
      ring

/-- An actual Schwartz kernel has a uniform potential under the stated geometric mass bound. -/
theorem schwartz_potential_le_of_dyadic_ball_growth
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (x : EuclideanSpace ℝ (Fin 2))
    (M : ℝ≥0∞)
    (hball : ∀ n : ℕ, μ (ball x ((2 : ℝ) ^ n)) ≤ M * (4 : ℝ≥0∞) ^ n) :
    ∫⁻ y, ‖k (x - y)‖ₑ ∂μ ≤
      9 * ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 k + SchwartzMap.seminorm ℝ 4 0 k) * M := by
  have h₀ := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) k
  have h₄ := apply_nonneg (SchwartzMap.seminorm ℝ 4 0) k
  simpa only [ofReal_norm] using lintegral_le_of_dyadic_ball_growth μ x
    (fun y ↦ ‖k (x - y)‖) (add_nonneg h₀ h₄) M
    (fun y ↦ (SchwartzMap.norm_le_seminorm ℝ k (x - y)).trans (le_add_of_nonneg_right h₄))
    (fun y ↦ by
      rw [dist_comm y x, dist_eq_norm]
      exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ k 4 (x - y)).trans
        (le_add_of_nonneg_left h₀)) hball

end FalconerPacking
