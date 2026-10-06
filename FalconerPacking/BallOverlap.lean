/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Bounded overlap survives doubling planar balls

Integrating the original overlap bound shows that doubling equal-radius balls increases
multiplicity by at most nine. This is the geometric input to localized Fourier orthogonality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace FalconerPacking

attribute [local instance] Classical.propDecidable

/-- A finite family of measurable sets with bounded multiplicity has controlled total mass. -/
theorem sum_measure_le_mul_of_multiplicity
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (I : Finset ι)
    (S : ι → Set α) {U : Set α} (hU : MeasurableSet U)
    (hS : ∀ i ∈ I, MeasurableSet (S i)) (hsub : ∀ i ∈ I, S i ⊆ U)
    (B : ℕ) (hB : ∀ x, (I.filter (fun i ↦ x ∈ S i)).card ≤ B) :
    ∑ i ∈ I, μ (S i) ≤ (B : ℝ≥0∞) * μ U := by
  classical
  have hcount (x : α) : (∑ i ∈ I, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x) =
      ((I.filter (fun i ↦ x ∈ S i)).card : ℝ≥0∞) := by
    simp only [indicator_apply, Finset.sum_boole]
  calc
    _ = ∫⁻ x, ∑ i ∈ I, (S i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_finsetSum I (fun i hi ↦ measurable_const.indicator (hS i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_indicator (hS i hi)]
      simp
    _ ≤ ∫⁻ x, U.indicator (fun _ ↦ (B : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx, hcount]
        exact_mod_cast hB x
      · rw [indicator_of_notMem hx]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro i hi
        exact indicator_of_notMem (fun h ↦ hx (hsub i hi h)) _
    _ = _ := by rw [lintegral_indicator hU]; simp

/-- Doubling equal-radius balls in the plane costs at most a factor nine in overlap. -/
theorem card_doubled_planar_balls_le
    {ι : Type*} (I : Finset ι) (c : ι → EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) (B : ℕ)
    (hB : ∀ x, (I.filter (fun i ↦ x ∈ ball (c i) r)).card ≤ B)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (I.filter (fun i ↦ x ∈ ball (c i) (2 * r))).card ≤ 9 * B := by
  classical
  let J := I.filter (fun i ↦ x ∈ ball (c i) (2 * r))
  have hsub (i : ι) (hi : i ∈ J) : ball (c i) r ⊆ ball x (3 * r) := by
    intro y hy
    have hxi := (Finset.mem_filter.mp hi).2
    have hxy := dist_triangle y (c i) x
    rw [dist_comm (c i) x] at hxy
    exact (mem_ball.mpr (hxy.trans_lt (by
      have hy' := mem_ball.mp hy
      have hx' := mem_ball.mp hxi
      linarith)))
  have hJ (y : EuclideanSpace ℝ (Fin 2)) :
      (J.filter (fun i ↦ y ∈ ball (c i) r)).card ≤ B :=
    (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hB y)
  let a : ℝ≥0∞ := ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi
  have ha : a ≠ 0 := by dsimp only [a]; positivity
  have hat : a ≠ ∞ := by dsimp only [a]; finiteness
  have hvol : volume (ball x (3 * r)) = 9 * a := by
    rw [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_mul (by norm_num), mul_pow]
    norm_num
    dsimp only [a]
    ring
  have h' : (J.card : ℝ≥0∞) * a ≤ (9 * B : ℝ≥0∞) * a := by
    calc
      _ = ∑ i ∈ J, volume (ball (c i) r) := by
        simp only [EuclideanSpace.volume_ball_fin_two, Finset.sum_const, nsmul_eq_mul, a]
      _ ≤ (B : ℝ≥0∞) * volume (ball x (3 * r)) :=
        sum_measure_le_mul_of_multiplicity volume J (fun i ↦ ball (c i) r)
          measurableSet_ball (fun _ _ ↦ measurableSet_ball) hsub B hJ
      _ = _ := by rw [hvol]; ring
  have hcard := (ENNReal.mul_le_mul_iff_left ha hat).mp h'
  exact_mod_cast hcard

end FalconerPacking
