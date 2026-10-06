/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AnnularDensityLimit
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Numerical summation of decaying annular densities

An eventual negative dyadic exponent suffices: finitely many early shells need only have finite
norms. Squared second-norm estimates imply summability of the unsquared second norms, with half
the decay exponent. No reconstruction or positivity of an individual shell is assumed here.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- A negative real dyadic exponent gives a summable sequence. -/
theorem summable_dyadic_decay {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ ↦ (2 : ℝ) ^ (-ε * (n : ℝ))) := by
  have h := summable_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-ε))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hε))
  convert h using 1
  ext n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- Eventual squared dyadic decay already gives summability of the nonnegative original terms. -/
theorem summable_of_eventually_sq_le_dyadic {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ᶠ n in atTop, f n ^ 2 ≤ C * (2 : ℝ) ^ (-ε * (n : ℝ))) :
    Summable f := by
  have hsum := (summable_dyadic_decay (half_pos hε)).mul_left (C + 1)
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [hbound] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (hf n)]
  apply (sq_le_sq₀ (hf n) (by positivity)).mp
  have hp : ((2 : ℝ) ^ (-(ε / 2) * (n : ℝ))) ^ 2 =
      (2 : ℝ) ^ (-ε * (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [mul_pow, hp]
  apply hn.trans
  gcongr
  nlinarith

/-- Actual squared second-norm integrals control the real norms used in the density limit. -/
theorem summable_secondNorm_of_eventual_dyadic_integral
    {α : Type*} [MeasurableSpace α] (κ : Measure α) (f : ℕ → α → ℂ)
    (hf : ∀ n, MemLp (f n) 2 κ) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hbound : ∀ᶠ n in atTop,
      (∫⁻ x, ENNReal.ofReal (‖f n x‖ ^ 2) ∂κ) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ)))) :
    Summable (fun n ↦ (eLpNorm (f n) 2 κ).toReal) := by
  apply summable_of_eventually_sq_le_dyadic (fun _ ↦ ENNReal.toReal_nonneg) hC hε
  filter_upwards [hbound] with n hn
  have hi := (memLp_two_iff_integrable_sq_norm (hf n).aestronglyMeasurable).mp (hf n)
  have he : (∫ x, ‖f n x‖ ^ 2 ∂κ) = (eLpNorm (f n) 2 κ).toReal ^ 2 := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) (hf n),
      ENNReal.toReal_ofReal (by positivity)]
    norm_num
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun x ↦ sq_nonneg ‖f n x‖))]
  rw [← he, integral_eq_lintegral_of_nonneg_ae (ae_of_all κ fun _ ↦ sq_nonneg _)
    hi.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

/-- Eventual first-norm integral decay supplies the other summability hypothesis. -/
theorem summable_firstNorm_of_eventual_dyadic_integral
    {α : Type*} [MeasurableSpace α] (κ : Measure α) (f : ℕ → α → ℂ)
    {C ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ᶠ n in atTop,
      (∫⁻ x, ENNReal.ofReal ‖f n x‖ ∂κ) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ)))) :
    Summable (fun n ↦ ∫ x, ‖f n x‖ ∂κ) := by
  apply ((summable_dyadic_decay hε).mul_left (max C 0)).of_norm_bounded_eventually_nat
  filter_upwards [hbound] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
  by_cases hi : Integrable (fun x ↦ ‖f n x‖) κ
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all κ fun _ ↦ norm_nonneg _)
      hi.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn
    rw [ENNReal.toReal_ofReal'] at ht
    apply ht.trans
    exact max_le (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)) (by positivity)
  · rw [integral_undef hi]
    positivity

/-- Finite early norms and actual eventual shell integrals discharge every norm hypothesis in
 the annular density-limit theorem. -/
theorem annular_norms_summable_of_dyadic_bounds
    {α : Type*} [MeasurableSpace α] (κ : Measure α) (good bad : ℕ → α → ℂ)
    (hgm : ∀ n, Measurable (good n)) (hbm : ∀ n, Measurable (bad n))
    (n₀ : ℕ) (hearlyg : ∀ n < n₀, MemLp (good n) 2 κ)
    (hearlyb : ∀ n < n₀, Integrable (bad n) κ)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hgood : ∀ n, n₀ ≤ n →
      (∫⁻ x, ENNReal.ofReal (‖good n x‖ ^ 2) ∂κ) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ))))
    (hbad : ∀ n, n₀ ≤ n →
      (∫⁻ x, ENNReal.ofReal ‖bad n x‖ ∂κ) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ)))) :
    (∀ n, MemLp (good n) 2 κ) ∧ (∀ n, Integrable (bad n) κ) ∧
      Summable (fun n ↦ (eLpNorm (good n) 2 κ).toReal) ∧
      Summable (fun n ↦ ∫ x, ‖bad n x‖ ∂κ) := by
  have hg (n : ℕ) : MemLp (good n) 2 κ := by
    by_cases hn : n < n₀
    · exact hearlyg n hn
    apply (memLp_two_iff_integrable_sq_norm (hgm n).aestronglyMeasurable).mpr
    refine ⟨((hgm n).norm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    exact (hgood n (Nat.le_of_not_gt hn)).trans_lt ENNReal.ofReal_lt_top
  have hb (n : ℕ) : Integrable (bad n) κ := by
    by_cases hn : n < n₀
    · exact hearlyb n hn
    refine ⟨(hbm n).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact (hbad n (Nat.le_of_not_gt hn)).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hg, hb, summable_secondNorm_of_eventual_dyadic_integral κ good hg hC hε ?_,
    summable_firstNorm_of_eventual_dyadic_integral κ bad (C := C) hε ?_⟩
  · exact (eventually_ge_atTop n₀).mono (fun n hn ↦ hgood n hn)
  · exact (eventually_ge_atTop n₀).mono (fun n hn ↦ hbad n hn)

end FalconerPacking
