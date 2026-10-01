/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.BallOverlap
import FalconerPacking.FiniteFourierOrthogonality
import Mathlib.Analysis.Fourier.Convolution

/-!
# Local Fourier orthogonality

Multiplication by an actual Schwartz cutoff enlarges Fourier supports by its Fourier
radius. Doubling equal-radius balls and Plancherel then give uniform local orthogonality
for any selected subfamily.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap
open scoped Convolution Pointwise

namespace FalconerPacking

attribute [local instance] Classical.propDecidable

/-- Fourier transformation converts a pointwise Schwartz product to convolution. -/
theorem fourier_schwartz_pairing_mul
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (pairing (ContinuousLinearMap.mul ℂ ℂ) f g) ξ =
      ((fun x ↦ 𝓕 f x) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x ↦ 𝓕 g x)) ξ := by
  have hinv (u : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
      (x : EuclideanSpace ℝ (Fin 2)) : 𝓕⁻ u x = 𝓕 u (-x) := rfl
  have hdouble (u : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
      𝓕 (𝓕 u) ξ = u (-ξ) := by
    have heq : (𝓕⁻ (𝓕 u : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) = u :=
      fourierInv_fourier_eq u
    have h := congrArg (fun v : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ ↦ v (-ξ)) heq
    simpa only [hinv, neg_neg] using h
  have hpair :
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (𝓕⁻ f) (𝓕⁻ g)) =
        pairing (ContinuousLinearMap.mul ℂ ℂ) f g := by
    rw [fourier_convolution]
    simp
  rw [← hpair, hdouble, SchwartzMap.convolution_apply]
  simp only [convolution_def, ContinuousLinearMap.mul_apply', hinv]
  convert integral_neg_eq_self (fun y ↦ 𝓕 f y * 𝓕 g (ξ - y)) volume using 1
  congr 1
  ext y
  congr 2
  abel

/-- Product Fourier support lies in the sum of the two prescribed frequency balls. -/
theorem fourier_schwartz_product_support_ball
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {c : EuclideanSpace ℝ (Fin 2)} {r s : ℝ}
    (hf : Function.support (fun ξ ↦ 𝓕 f ξ) ⊆ ball c r)
    (hg : Function.support (fun ξ ↦ 𝓕 g ξ) ⊆ ball 0 s) :
    Function.support (fun ξ ↦ 𝓕 (pairing (ContinuousLinearMap.mul ℂ ℂ) f g) ξ) ⊆
      ball c (r + s) := by
  intro ξ hξ
  have hconv : ξ ∈ Function.support
      ((fun x ↦ 𝓕 f x) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x ↦ 𝓕 g x)) := by
    simpa only [Function.mem_support, fourier_schwartz_pairing_mul] using hξ
  obtain ⟨a, ha, b, hb, hab⟩ :=
    support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hconv
  subst ξ
  have ha' := mem_ball.mp (hf ha)
  have hb' := mem_ball.mp (hg hb)
  rw [mem_ball, dist_eq_norm]
  have hnorm := norm_add_le (a - c) b
  rw [dist_eq_norm] at ha'
  rw [dist_zero_right] at hb'
  simpa only [sub_zero, add_sub_right_comm] using hnorm.trans_lt (add_lt_add ha' hb')

/-- A small Fourier cutoff preserves selected orthogonality with constant nine times the overlap. -/
theorem schwartz_cutoff_selected_orthogonality
    {ι : Type*} (I J : Finset ι) (hJI : J ⊆ I)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (v : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (c : ι → EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (B : ℕ)
    (hf : ∀ i ∈ I, Function.support (fun ξ ↦ 𝓕 (f i) ξ) ⊆ ball (c i) r)
    (hv : Function.support (fun ξ ↦ 𝓕 v ξ) ⊆ ball 0 r)
    (hB : ∀ ξ, (I.filter (fun i ↦ ξ ∈ ball (c i) r)).card ≤ B) :
    (∫ x, ‖v x * ∑ i ∈ J, f i x‖ ^ 2) ≤
      (9 * B : ℝ) * ∑ i ∈ J, ∫ x, ‖v x * f i x‖ ^ 2 := by
  classical
  let g (i : ι) := pairing (ContinuousLinearMap.mul ℂ ℂ) (f i) v
  have hg : ∀ ξ, (I.filter (fun i ↦ 𝓕 (g i) ξ ≠ 0)).card ≤ 9 * B := by
    intro ξ
    refine (Finset.card_le_card ?_).trans (card_doubled_planar_balls_le I c hr B hB ξ)
    intro i hi
    obtain ⟨hi, hξ⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi, ?_⟩
    have h := fourier_schwartz_product_support_ball (f i) v (hf i hi) hv hξ
    simpa only [← two_mul] using h
  have h := schwartz_selected_sum_norm_sq_le_of_fourier_overlap I J hJI g (9 * B) hg
  simpa only [g, pairing_apply_apply, ContinuousLinearMap.mul_apply', mul_comm,
    Finset.mul_sum, Nat.cast_mul, Nat.cast_ofNat] using h

/-- A cutoff bounded below on a region controls the actual local selected Fourier sum. -/
theorem schwartz_local_selected_orthogonality
    {ι : Type*} (I J : Finset ι) (hJI : J ⊆ I)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (v : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (c : ι → EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (B : ℕ)
    (hf : ∀ i ∈ I, Function.support (fun ξ ↦ 𝓕 (f i) ξ) ⊆ ball (c i) r)
    (hv : Function.support (fun ξ ↦ 𝓕 v ξ) ⊆ ball 0 r)
    (hB : ∀ ξ, (I.filter (fun i ↦ ξ ∈ ball (c i) r)).card ≤ B)
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQ : MeasurableSet Q)
    (hvQ : ∀ x ∈ Q, 1 ≤ ‖v x‖) :
    (∫ x in Q, ‖∑ i ∈ J, f i x‖ ^ 2) ≤
      (9 * B : ℝ) * ∑ i ∈ J, ∫ x, ‖v x * f i x‖ ^ 2 := by
  classical
  have hsum₀ := ((∑ i ∈ J, f i).memLp 2 volume).integrable_norm_pow
    (p := 2) (by norm_num)
  have hsum : Integrable (fun x ↦ ‖∑ i ∈ J, f i x‖ ^ 2) volume := by
    simpa using hsum₀
  have hprod₀ := ((pairing (ContinuousLinearMap.mul ℂ ℂ) v
    (∑ i ∈ J, f i)).memLp 2 volume).integrable_norm_pow (p := 2) (by norm_num)
  have hprod : Integrable (fun x ↦ ‖v x * ∑ i ∈ J, f i x‖ ^ 2) volume := by
    simpa only [pairing_apply_apply, ContinuousLinearMap.mul_apply', sum_apply] using hprod₀
  calc
    _ ≤ ∫ x in Q, ‖v x * ∑ i ∈ J, f i x‖ ^ 2 := by
      apply setIntegral_mono_on hsum.integrableOn hprod.integrableOn hQ
      intro x hx
      rw [norm_mul, mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (hvQ x hx))
    _ ≤ ∫ x, ‖v x * ∑ i ∈ J, f i x‖ ^ 2 :=
      setIntegral_le_integral hprod (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    _ ≤ _ := schwartz_cutoff_selected_orthogonality I J hJI f v c hr B hf hv hB

end FalconerPacking
