/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Energy
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite truncated conditional energies

Increasing the truncation depth costs only the mass of one dyadic ball. Summing this finite
recurrence includes the diagonal and needs neither nonatomicity nor finite Riesz energy.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The diagonal convention agrees with the extended nonnegative minimum kernel. -/
theorem truncKernel_eq_min_div (a : ℝ) {b : ℝ} (hb : 0 < b)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    truncKernel a b x y =
      min (ENNReal.ofReal (b / a)) (ENNReal.ofReal b / ENNReal.ofReal (dist x y)) := by
  by_cases hxy : x = y
  · simp [truncKernel, hxy, ENNReal.div_zero (ENNReal.ofReal_pos.mpr hb).ne']
  · rw [truncKernel, if_neg hxy, ENNReal.ofReal_min,
      ENNReal.ofReal_div_of_pos (dist_pos.mpr hxy)]

/-- The truncated kernel is measurable in its second spatial variable. -/
@[fun_prop]
theorem measurable_truncKernel_right (a b : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Measurable (truncKernel a b x) := by
  unfold truncKernel
  apply Measurable.ite (measurableSet_eq_fun measurable_const measurable_id)
  · exact measurable_const
  · fun_prop

/-- Passing to a finer truncation changes the kernel only inside the old inner ball. -/
theorem truncKernel_le_add_ball_indicator {a a' b : ℝ}
    (ha : 0 < a) (ha' : 0 < a') (haa : a' ≤ a) (hb : 0 ≤ b)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    truncKernel a' b x y ≤ truncKernel a b x y +
      (Metric.ball x a).indicator (fun _ ↦ ENNReal.ofReal (b / a')) y := by
  by_cases hy : y ∈ Metric.ball x a
  · rw [indicator_of_mem hy]
    exact (truncKernel_le a' b x y).trans (le_add_left le_rfl)
  · have hd : a ≤ dist x y := by
      simpa only [Metric.mem_ball, not_lt, dist_comm] using hy
    rw [indicator_of_notMem hy, add_zero,
      truncKernel_of_le_dist hb ha hd, truncKernel_of_le_dist hb ha' (haa.trans hd)]

/-- Integrating the one-step kernel bound retains its exact ball-mass cost. -/
theorem lintegral_truncKernel_le_add_ball_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) {a a' b : ℝ}
    (ha : 0 < a) (ha' : 0 < a') (haa : a' ≤ a) (hb : 0 ≤ b)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ y, truncKernel a' b x y ∂μ) ≤ (∫⁻ y, truncKernel a b x y ∂μ) +
      ENNReal.ofReal (b / a') * μ (Metric.ball x a) := by
  refine (lintegral_mono (truncKernel_le_add_ball_indicator ha ha' haa hb x)).trans_eq ?_
  rw [lintegral_add_left (measurable_truncKernel_right a b x),
    lintegral_indicator Metric.isOpen_ball.measurableSet, lintegral_const,
    Measure.restrict_apply_univ]

/-- The finite-scale potential bound, before inserting any regularity profile. -/
theorem lintegral_truncKernel_dyadic_le_sum_ball_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {m n : ℕ} (hmn : m ≤ n) (x : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ y, truncKernel (dyadicRadius n) (dyadicRadius m) x y ∂μ) ≤
      1 + ∑ k ∈ Finset.Ico m n,
        ENNReal.ofReal (dyadicRadius m / dyadicRadius (k + 1)) *
          μ (Metric.ball x (dyadicRadius k)) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
      refine (lintegral_mono fun y ↦ truncKernel_le _ _ x y).trans_eq ?_
      rw [div_self (dyadicRadius_pos m).ne', ENNReal.ofReal_one,
        lintegral_const, measure_univ, mul_one]
  | succ n hn ih =>
      refine (lintegral_truncKernel_le_add_ball_mass μ (dyadicRadius_pos n)
        (dyadicRadius_pos (n + 1)) (dyadicRadius_succ_lt n).le
        (dyadicRadius_pos m).le x).trans ?_
      rw [Finset.sum_Ico_succ_top hn]
      exact (add_le_add_left ih _).trans_eq (add_assoc _ _ _)

/-- A dyadic radius ratio is the corresponding positive power of two. -/
theorem ofReal_dyadicRadius_ratio (m k : ℕ) :
    ENNReal.ofReal (dyadicRadius m / dyadicRadius k) =
      (2 : ℝ≥0∞) ^ ((k : ℝ) - (m : ℝ)) := by
  rw [dyadicRadius, dyadicRadius,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  rw [show -(m : ℝ) - -(k : ℝ) = (k : ℝ) - (m : ℝ) by ring,
    ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

/-- At dyadic scales the kernel is exactly the requested finite minimum, even on the diagonal. -/
theorem truncKernel_dyadic_eq_min (m n : ℕ) (x y : EuclideanSpace ℝ (Fin 2)) :
    truncKernel (dyadicRadius n) (dyadicRadius m) x y =
      min ((2 : ℝ≥0∞) ^ ((n : ℝ) - (m : ℝ)))
        (ENNReal.ofReal (dyadicRadius m) / ENNReal.ofReal (dist x y)) := by
  rw [truncKernel_eq_min_div _ (dyadicRadius_pos m), ofReal_dyadicRadius_ratio]

/-- The annular coefficient records exactly the drop of the excess-dimension profile. -/
theorem dyadicRadius_profile_coefficient (f : ℕ → ℝ) (m k : ℕ) :
    ENNReal.ofReal (dyadicRadius m / dyadicRadius (k + 1)) *
        (2 : ℝ≥0∞) ^ (f m - f k) =
      2 * (2 : ℝ≥0∞) ^ ((k : ℝ) - (m : ℝ) + f m - f k) := by
  rw [ofReal_dyadicRadius_ratio,
    ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
  push_cast
  rw [show ((k : ℝ) + 1 - (m : ℝ)) + (f m - f k) =
      1 + ((k : ℝ) - (m : ℝ) + f m - f k) by ring,
    ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]

/-- Finite ball bounds control the truncated potential, including any diagonal mass. -/
theorem lintegral_truncKernel_dyadic_le_profile_sum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (f : ℕ → ℝ) (A : ℝ≥0∞) {m n : ℕ} (hmn : m ≤ n)
    (x : EuclideanSpace ℝ (Fin 2))
    (hball : ∀ k ∈ Finset.Ico m n, μ (Metric.ball x (dyadicRadius k)) ≤
      A * (2 : ℝ≥0∞) ^ (f m - f k)) :
    (∫⁻ y, truncKernel (dyadicRadius n) (dyadicRadius m) x y ∂μ) ≤
      1 + 2 * A * ∑ k ∈ Finset.Ico m n,
        (2 : ℝ≥0∞) ^ ((k : ℝ) - (m : ℝ) + f m - f k) := by
  refine (lintegral_truncKernel_dyadic_le_sum_ball_mass μ hmn x).trans ?_
  apply add_le_add_right
  calc
    _ ≤ ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (dyadicRadius m / dyadicRadius (k + 1)) *
        (A * (2 : ℝ≥0∞) ^ (f m - f k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_right (hball k hk) _
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = A * (ENNReal.ofReal (dyadicRadius m / dyadicRadius (k + 1)) *
            (2 : ℝ≥0∞) ^ (f m - f k)) := by ring
        _ = _ := by rw [dyadicRadius_profile_coefficient]; ring

/-- The finite ball-profile estimate for the double truncated energy. -/
theorem truncEnergy_dyadic_le_profile_sum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (f : ℕ → ℝ) (A : ℝ≥0∞) {m n : ℕ} (hmn : m ≤ n)
    (hball : ∀ x, ∀ k ∈ Finset.Ico m n, μ (Metric.ball x (dyadicRadius k)) ≤
      A * (2 : ℝ≥0∞) ^ (f m - f k)) :
    truncEnergy μ (dyadicRadius n) (dyadicRadius m) ≤
      1 + 2 * A * ∑ k ∈ Finset.Ico m n,
        (2 : ℝ≥0∞) ^ ((k : ℝ) - (m : ℝ) + f m - f k) := by
  refine (lintegral_mono fun x ↦
    lintegral_truncKernel_dyadic_le_profile_sum μ f A hmn x (hball x)).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]

/-- A bound for every profile drop gives the required polynomial-times-exponential energy. -/
theorem truncEnergy_dyadic_le_profile_cost
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (f : ℕ → ℝ) {A : ℝ≥0∞} (hA : 1 ≤ A) {m n : ℕ} (hmn : m ≤ n)
    {cost : ℝ}
    (hball : ∀ x, ∀ k ∈ Finset.Icc m n, μ (Metric.ball x (dyadicRadius k)) ≤
      A * (2 : ℝ≥0∞) ^ (f m - f k))
    (hcost : ∀ k ∈ Finset.Icc m n,
      (f m - (m : ℝ)) - (f k - (k : ℝ)) ≤ cost) :
    truncEnergy μ (dyadicRadius n) (dyadicRadius m) ≤
      3 * (n + 1 : ℝ≥0∞) * A * (2 : ℝ≥0∞) ^ cost := by
  have hsubset : Finset.Ico m n ⊆ Finset.Icc m n := fun k hk ↦
    Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩
  have hcost₀ : 0 ≤ cost := by
    simpa only [sub_self] using hcost m (Finset.mem_Icc.mpr ⟨le_rfl, hmn⟩)
  have hP : 1 ≤ (2 : ℝ≥0∞) ^ cost := by
    simpa only [ENNReal.rpow_zero] using
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2) hcost₀
  have hsum : (∑ k ∈ Finset.Ico m n,
      (2 : ℝ≥0∞) ^ ((k : ℝ) - (m : ℝ) + f m - f k)) ≤
        (n - m : ℕ) * (2 : ℝ≥0∞) ^ cost := by
    calc
      _ ≤ ∑ _k ∈ Finset.Ico m n, (2 : ℝ≥0∞) ^ cost := by
        apply Finset.sum_le_sum
        intro k hk
        apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
        convert hcost k (hsubset hk) using 1
        ring
      _ = _ := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  calc
    _ ≤ 1 + 2 * A * ∑ k ∈ Finset.Ico m n,
        (2 : ℝ≥0∞) ^ ((k : ℝ) - (m : ℝ) + f m - f k) :=
      truncEnergy_dyadic_le_profile_sum μ f A hmn (fun x k hk ↦ hball x k (hsubset hk))
    _ ≤ A * (2 : ℝ≥0∞) ^ cost +
        2 * A * ((n - m : ℕ) * (2 : ℝ≥0∞) ^ cost) :=
      add_le_add (one_le_mul hA hP) (mul_le_mul_right hsum _)
    _ ≤ A * (2 : ℝ≥0∞) ^ cost + 2 * A * ((n : ℝ≥0∞) * (2 : ℝ≥0∞) ^ cost) := by
      gcongr
      exact_mod_cast Nat.sub_le n m
    _ = (1 + 2 * (n : ℝ≥0∞)) * A * (2 : ℝ≥0∞) ^ cost := by ring
    _ ≤ _ := by
      gcongr
      exact_mod_cast (show 1 + 2 * n ≤ 3 * (n + 1) by omega)

end FalconerPacking
