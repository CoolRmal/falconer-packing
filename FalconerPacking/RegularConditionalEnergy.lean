/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RegularComponentBalls

/-!
# Truncated energies of actual regularized components

The finite kernel recurrence is summed on the regularization grid. Its radius ratio costs
one fixed block factor, and the existing edge cost controls every remaining profile drop.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The finite potential recurrence can be summed directly on a block grid. -/
theorem lintegral_truncKernel_block_le_sum_ball_mass
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (T : ℕ) {m n : ℕ} (hmn : m ≤ n) (x : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ y, truncKernel (dyadicRadius (T * n)) (dyadicRadius (T * m)) x y ∂μ) ≤
      1 + ∑ k ∈ Finset.Ico m n,
        ENNReal.ofReal (dyadicRadius (T * m) / dyadicRadius (T * (k + 1))) *
          μ (Metric.ball x (dyadicRadius (T * k))) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
      refine (lintegral_mono fun y ↦ truncKernel_le _ _ x y).trans_eq ?_
      rw [div_self (dyadicRadius_pos (T * m)).ne', ENNReal.ofReal_one,
        lintegral_const, measure_univ, mul_one]
  | succ n hn ih =>
      have hrad : dyadicRadius (T * (n + 1)) ≤ dyadicRadius (T * n) := by
        unfold dyadicRadius
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        apply neg_le_neg
        exact_mod_cast Nat.mul_le_mul_left T (Nat.le_succ n)
      refine (lintegral_truncKernel_le_add_ball_mass μ (dyadicRadius_pos (T * n))
        (dyadicRadius_pos (T * (n + 1))) hrad (dyadicRadius_pos (T * m)).le x).trans ?_
      rw [Finset.sum_Ico_succ_top hn]
      exact (add_le_add_left ih _).trans_eq (add_assoc _ _ _)

/-- Block-scale ball bounds yield a finite energy estimate with one block-factor loss. -/
theorem truncEnergy_block_le_profile_cost
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (T : ℕ) (f : ℕ → ℝ) {A : ℝ≥0∞} (hA : 1 ≤ A) {m n : ℕ} (hmn : m ≤ n)
    {cost : ℝ}
    (hball : ∀ x, ∀ k ∈ Finset.Icc m n, μ (Metric.ball x (dyadicRadius (T * k))) ≤
      A * (2 : ℝ≥0∞) ^ (f m - f k))
    (hcost : ∀ k ∈ Finset.Icc m n,
      (f m - T * m) - (f k - T * k) ≤ cost) :
    truncEnergy μ (dyadicRadius (T * n)) (dyadicRadius (T * m)) ≤
      (n + 1 : ℝ≥0∞) * A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost) := by
  have hcost₀ : 0 ≤ cost := by
    simpa only [sub_self] using hcost m (Finset.mem_Icc.mpr ⟨le_rfl, hmn⟩)
  have hpower : 1 ≤ (2 : ℝ≥0∞) ^ ((T : ℝ) + cost) := by
    simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by positivity : (0 : ℝ) ≤ (T : ℝ) + cost)
  have hpoint (x : EuclideanSpace ℝ (Fin 2)) :
      (∫⁻ y, truncKernel (dyadicRadius (T * n)) (dyadicRadius (T * m)) x y ∂μ) ≤
        (n + 1 : ℝ≥0∞) * A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost) := by
    refine (lintegral_truncKernel_block_le_sum_ball_mass μ T hmn x).trans ?_
    have hsummand (k : ℕ) (hk : k ∈ Finset.Ico m n) :
        ENNReal.ofReal (dyadicRadius (T * m) / dyadicRadius (T * (k + 1))) *
          μ (Metric.ball x (dyadicRadius (T * k))) ≤
            A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost) := by
      have hk' : k ∈ Finset.Icc m n :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩
      refine (mul_le_mul_right (hball x k hk') _).trans ?_
      rw [ofReal_dyadicRadius_ratio,
        show (2 : ℝ≥0∞) ^ (((T * (k + 1) : ℕ) : ℝ) - ((T * m : ℕ) : ℝ)) *
            (A * (2 : ℝ≥0∞) ^ (f m - f k)) =
          A * ((2 : ℝ≥0∞) ^ (((T * (k + 1) : ℕ) : ℝ) - ((T * m : ℕ) : ℝ)) *
            (2 : ℝ≥0∞) ^ (f m - f k)) by ring,
        ← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      apply mul_le_mul_right
      apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
      have h := hcost k hk'
      push_cast
      linarith
    calc
      _ ≤ 1 + ∑ _k ∈ Finset.Ico m n, A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost) :=
        add_le_add_right (Finset.sum_le_sum hsummand) _
      _ = 1 + (n - m : ℕ) * (A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost) +
          (n : ℝ≥0∞) * (A * (2 : ℝ≥0∞) ^ ((T : ℝ) + cost)) := by
        apply add_le_add (one_le_mul hA hpower)
        apply mul_le_mul_left
        exact_mod_cast Nat.sub_le n m
      _ = _ := by ring
  refine (lintegral_mono hpoint).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]

/-- An actual regularized component conditioned on an enlargement of an active cube has
energy controlled by the already formalized profile edge cost. -/
theorem normalized_regular_conditional_energy_le_edgeCost
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} (hT : 0 < T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (he : ∀ j < L, e j ≤ 2 * T)
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ L)
    {q : Fin 2 → ℤ}
    (hq : 0 < normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * m) q))
    {X : Set (EuclideanSpace ℝ (Fin 2))} (hXm : MeasurableSet X)
    (hX : dyadicCube (T * m) q ⊆ X) :
    truncEnergy (normalizedRestrict (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) X)
        (dyadicRadius (T * n)) (dyadicRadius (T * m)) ≤
      4 * (n + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
        (3 * (L : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T L e) m n) := by
  let σ := normalizedRestrict μ (finiteDyadicUnion (T * L) A)
  haveI := isProbabilityMeasure_normalizedRestrict
    (measurableSet_finiteDyadicUnion _ _) hA (measure_ne_top μ _)
  have hXpos : 0 < σ X := hq.trans_le (measure_mono hX)
  haveI := isProbabilityMeasure_normalizedRestrict hXm hXpos.ne' (measure_ne_top σ X)
  have hloss : 1 ≤ 4 * (2 : ℝ≥0∞) ^ (3 * (L : ℝ) + 2 * T) := by
    apply one_le_mul (by norm_num)
    simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by positivity : (0 : ℝ) ≤ 3 * (L : ℝ) + 2 * T)
  have h := truncEnergy_block_le_profile_cost (normalizedRestrict σ X) T
    (regularProfileExponent L e) hloss hmn
    (cost := T * edgeCost (regularBlockProfile T L e) m n)
    (fun x k hk ↦ normalized_regular_conditional_ball_bound μ hT he hA hreg hroot
      (hmn.trans hn) ((Finset.mem_Icc.mp hk).2.trans hn) hq hX x) ?_
  · refine h.trans_eq ?_
    calc
      _ = 4 * (n + 1 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * (L : ℝ) + 2 * T) *
          (2 : ℝ≥0∞) ^ (T + T * edgeCost (regularBlockProfile T L e) m n)) := by ring
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
        congr 2
        ring
  · intro k hk
    have hdrop : regularBlockProfile T L e m - regularBlockProfile T L e k ≤
        edgeCost (regularBlockProfile T L e) m n :=
      sub_le_sub_left (gMin_le (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2) _
    have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    have heq : (regularProfileExponent L e m - T * m) -
        (regularProfileExponent L e k - T * k) =
          (T : ℝ) * (regularBlockProfile T L e m - regularBlockProfile T L e k) := by
      unfold regularBlockProfile
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hdrop (Nat.cast_nonneg T)

end FalconerPacking
