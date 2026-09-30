/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Energy
import FalconerPacking.GaussianEnergy
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Gaussian potential bounds from Frostman growth

Spatial annuli of width `r` convert polynomial ball growth into a Gaussian potential bound
of order `r^s`. The scalar summation constant is finite uniformly for `0 ≤ s ≤ 2`.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- A fixed summable majorant for the planar Gaussian annuli. -/
theorem summable_gaussian_annulus_majorant :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ))) := by
  have h₂ := Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 1)
  have h₁ := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h₀ := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1)
  convert h₂.add ((h₁.mul_left 2).add h₀) using 1
  funext n
  simp only [neg_mul, one_mul, pow_one, pow_zero]
  ring

/-- A Frostman probability satisfies polynomial growth at all radii after increasing its
constant to at least one. -/
theorem isFrostman_all_radius_bound
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μ]
    {s C : ℝ} (hs : 0 ≤ s) (hfr : IsFrostman μ s C)
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    μ (Metric.ball x r) ≤ ENNReal.ofReal (max C 1 * r ^ s) := by
  by_cases hr₁ : r ≤ 1
  · exact (hfr x r hr hr₁).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le _)))
  · have hp : 1 ≤ r ^ s := Real.one_le_rpow (le_of_not_ge hr₁) hs
    have hbound : 1 ≤ max C 1 * r ^ s := by
      nlinarith [le_max_right C 1, mul_nonneg
        (sub_nonneg.mpr (le_max_right C 1)) (sub_nonneg.mpr hp)]
    exact (prob_le_one).trans (by exact_mod_cast ENNReal.ofReal_le_ofReal hbound)

/-- The finite numerical constant in the annular Gaussian estimate. -/
def gaussianAnnulusConstant : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ))

theorem gaussianAnnulusConstant_pos : 0 < gaussianAnnulusConstant := by
  have h := summable_gaussian_annulus_majorant.le_tsum 0 (fun n _ ↦ by positivity)
  norm_num at h
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) h

/-- Polynomial ball growth with exponent at most two controls every spatial Gaussian scale. -/
theorem lintegral_gaussian_le_of_ball_growth
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {s C : ℝ}
    (hs₂ : s ≤ 2) (hC : 0 ≤ C)
    (hball : ∀ x r, 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ s))
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (-((dist y x / r) ^ 2))) ∂μ ≤
      ENNReal.ofReal (C * r ^ s * gaussianAnnulusConstant) := by
  let A := fun n : ℕ ↦ {y : EuclideanSpace ℝ (Fin 2) |
    (n : ℝ) * r ≤ dist y x ∧ dist y x < ((n : ℝ) + 1) * r}
  have hAm (n : ℕ) : MeasurableSet (A n) := by
    change MeasurableSet ({y | (n : ℝ) * r ≤ dist y x} ∩
      {y | dist y x < ((n : ℝ) + 1) * r})
    exact (measurableSet_le measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hcover : (⋃ n, A n) = univ := by
    apply eq_univ_of_forall
    intro y
    refine mem_iUnion.mpr ⟨⌊dist y x / r⌋₊, ?_⟩
    exact ⟨(le_div_iff₀ hr).mp (Nat.floor_le (div_nonneg dist_nonneg hr.le)),
      (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one _)⟩
  have hann (n : ℕ) :
      ∫⁻ y in A n, ENNReal.ofReal (Real.exp (-((dist y x / r) ^ 2))) ∂μ ≤
        ENNReal.ofReal (C * r ^ s) *
          ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ))) := by
    have he (y) (hy : y ∈ A n) :
        Real.exp (-((dist y x / r) ^ 2)) ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hn : (n : ℝ) ≤ dist y x / r := (le_div_iff₀ hr).mpr hy.1
      have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with rfl | hn'
        · norm_num
        · have h₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn'
          nlinarith
      nlinarith [sq_le_sq₀ hn₀ (div_nonneg dist_nonneg hr.le) |>.mpr hn]
    have hm : μ (A n) ≤ ENNReal.ofReal (C * (((n : ℝ) + 1) * r) ^ s) :=
      (measure_mono (fun y hy ↦ hy.2)).trans (hball x _ (by positivity))
    have hpow : (((n : ℝ) + 1) * r) ^ s ≤ ((n : ℝ) + 1) ^ 2 * r ^ s := by
      rw [Real.mul_rpow (by positivity) hr.le]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
      exact (Real.rpow_le_rpow_of_exponent_le (by simp) hs₂).trans_eq
        (Real.rpow_natCast _ 2)
    calc
      ∫⁻ y in A n, ENNReal.ofReal (Real.exp (-((dist y x / r) ^ 2))) ∂μ ≤
          ∫⁻ _ in A n, ENNReal.ofReal (Real.exp (-(n : ℝ))) ∂μ := by
        exact setLIntegral_mono' (hAm n) fun y hy ↦ ENNReal.ofReal_le_ofReal (he y hy)
      _ = ENNReal.ofReal (Real.exp (-(n : ℝ))) * μ (A n) := by simp
      _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ))) *
          ENNReal.ofReal (C * (((n : ℝ) + 1) ^ 2 * r ^ s)) := by
        apply mul_le_mul_right
        exact hm.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hC))
      _ = ENNReal.ofReal (C * r ^ s) *
          ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
          ← ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg hr.le _))]
        congr 1
        ring
  calc
    ∫⁻ y, ENNReal.ofReal (Real.exp (-((dist y x / r) ^ 2))) ∂μ =
        ∫⁻ y in ⋃ n, A n, ENNReal.ofReal (Real.exp (-((dist y x / r) ^ 2))) ∂μ := by
      rw [hcover, Measure.restrict_univ]
    _ ≤ ∑' n, ∫⁻ y in A n, ENNReal.ofReal (Real.exp (-((dist y x / r) ^ 2))) ∂μ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C * r ^ s) *
        ENNReal.ofReal (((n : ℝ) + 1) ^ 2 * Real.exp (-(n : ℝ))) := ENNReal.tsum_le_tsum hann
    _ = ENNReal.ofReal (C * r ^ s * gaussianAnnulusConstant) := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity)
        summable_gaussian_annulus_majorant, ← ENNReal.ofReal_mul
        (mul_nonneg hC (Real.rpow_nonneg hr.le _))]
      rfl

/-- A spatial Gaussian is integrable for every finite source measure. -/
theorem integrable_spatial_gaussian
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    Integrable (fun y ↦ Real.exp (-((dist y x / r) ^ 2))) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  exact Eventually.of_forall fun y ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

/-- The real-valued form of the Gaussian potential estimate. -/
theorem integral_gaussian_le_of_ball_growth
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] {s C : ℝ}
    (hs₂ : s ≤ 2) (hC : 0 ≤ C)
    (hball : ∀ x r, 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ s))
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ∫ y, Real.exp (-((dist y x / r) ^ 2)) ∂μ ≤ C * r ^ s * gaussianAnnulusConstant := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity [gaussianAnnulusConstant_pos])).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_spatial_gaussian μ x r)
    (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)]
  exact lintegral_gaussian_le_of_ball_growth μ hs₂ hC hball x hr

/-- Gaussian Fourier energy has the sharp scale exponent supplied by Frostman ball growth. -/
theorem gaussian_fourier_energy_le_of_ball_growth
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs₂ : s ≤ 2) (hC : 0 ≤ C)
    (hball : ∀ x r, 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ s))
    {r : ℝ} (hr : 0 < r) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Real.exp (-(r ^ 2 / 4) * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 ≤
      Real.pi / (r ^ 2 / 4) * (C * r ^ s * gaussianAnnulusConstant) := by
  rw [integral_gaussian_charFun_norm_sq μ (by positivity : 0 < r ^ 2 / 4)]
  have hkernel (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * (r ^ 2 / 4)))) =
        Real.exp (-((dist p.2 p.1 / r) ^ 2)) := by
    congr 1
    rw [dist_comm p.2 p.1, dist_eq_norm, div_pow]
    congr 2
    ring
  simp_rw [hkernel]
  have hi : Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      Real.exp (-((dist p.2 p.1 / r) ^ 2))) (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    exact Eventually.of_forall fun p ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  rw [integral_prod _ hi]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ∫ x, ∫ y, Real.exp (-((dist y x / r) ^ 2)) ∂μ ∂μ ≤
        ∫ _x, C * r ^ s * gaussianAnnulusConstant ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const _) fun x ↦
        integral_gaussian_le_of_ball_growth μ hs₂ hC hball x hr
    _ = C * r ^ s * gaussianAnnulusConstant := by simp

/-- The project Frostman condition supplies the ball growth used by the Gaussian estimate. -/
theorem gaussian_fourier_energy_le_of_isFrostman
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) {r : ℝ} (hr : 0 < r) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Real.exp (-(r ^ 2 / 4) * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 ≤
      Real.pi / (r ^ 2 / 4) * (max C 1 * r ^ s * gaussianAnnulusConstant) := by
  apply gaussian_fourier_energy_le_of_ball_growth μ hs₂ (by positivity) _ hr
  exact fun x _ hr ↦ isFrostman_all_radius_bound hs hfr x hr

end FalconerPacking
