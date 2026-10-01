/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MeanInequalities

/-!
# Orthogonality from bounded Fourier overlap

A pointwise overlap bound gives a quadratic estimate for every selected subfamily, with
no dependence on the number of labels. Plancherel transfers this to spatial Schwartz functions.
-/

noncomputable section

open MeasureTheory Set FourierTransform SchwartzMap
open scoped ENNReal

namespace FalconerPacking

/-- At most B nonzero summands cost at most B in the squared-norm estimate. -/
theorem norm_sum_sq_le_active_count
    {ι : Type*} (I : Finset ι) (f : ι → ℂ) (B : ℕ)
    (hB : (I.filter (fun i ↦ f i ≠ 0)).card ≤ B) :
    ‖∑ i ∈ I, f i‖ ^ 2 ≤ (B : ℝ) * ∑ i ∈ I, ‖f i‖ ^ 2 := by
  classical
  let J := I.filter (fun i ↦ f i ≠ 0)
  have hsum : ∑ i ∈ J, f i = ∑ i ∈ I, f i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hi, hn⟩)
  have hsq : ∑ i ∈ J, ‖f i‖ ^ 2 ≤ ∑ i ∈ I, ‖f i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq J (fun i ↦ ‖f i‖) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  rw [← hsum]
  calc
    _ ≤ (∑ i ∈ J, ‖f i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le J f) 2
    _ ≤ (∑ i ∈ J, ‖f i‖ ^ 2) * J.card := hCS
    _ ≤ (∑ i ∈ I, ‖f i‖ ^ 2) * B := by
      apply mul_le_mul hsq (Nat.cast_le.mpr hB) (by positivity)
      exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
    _ = _ := mul_comm _ _

/-- Bounded overlap of Fourier supports gives spatial L² orthogonality. -/
theorem schwartz_sum_norm_sq_le_of_fourier_overlap
    {ι : Type*} (I : Finset ι)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (B : ℕ)
    (hB : ∀ ξ, (I.filter (fun i ↦ 𝓕 (f i) ξ ≠ 0)).card ≤ B) :
    (∫ x, ‖∑ i ∈ I, f i x‖ ^ 2) ≤
      (B : ℝ) * ∑ i ∈ I, ∫ x, ‖f i x‖ ^ 2 := by
  classical
  have hint (i : ι) : Integrable (fun ξ ↦ ‖𝓕 (f i) ξ‖ ^ 2) volume :=
    ((𝓕 (f i)).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hsum : Integrable (fun ξ ↦ ‖∑ i ∈ I, 𝓕 (f i) ξ‖ ^ 2) volume := by
    have hsum₀ := ((∑ i ∈ I, 𝓕 (f i)).memLp 2 volume).integrable_norm_pow
      (p := 2) (by norm_num)
    simpa using hsum₀
  have h := integral_mono hsum ((integrable_finsetSum I (fun i _ ↦ hint i)).const_mul B)
    (fun ξ ↦ norm_sum_sq_le_active_count I (fun i ↦ 𝓕 (f i) ξ) B (hB ξ))
  rw [integral_const_mul, integral_finsetSum I (fun i _ ↦ hint i)] at h
  simp_rw [SchwartzMap.integral_norm_sq_fourier] at h
  have hleft : (∫ ξ, ‖∑ i ∈ I, 𝓕 (f i) ξ‖ ^ 2) = ∫ x, ‖∑ i ∈ I, f i x‖ ^ 2 := by
    simpa [fourier_sum] using
      SchwartzMap.integral_norm_sq_fourier (∑ i ∈ I, f i)
  rwa [hleft] at h

/-- The same constant works for every selected subfamily of the original labels. -/
theorem schwartz_selected_sum_norm_sq_le_of_fourier_overlap
    {ι : Type*} (I J : Finset ι) (hJI : J ⊆ I)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (B : ℕ)
    (hB : ∀ ξ, (I.filter (fun i ↦ 𝓕 (f i) ξ ≠ 0)).card ≤ B) :
    (∫ x, ‖∑ i ∈ J, f i x‖ ^ 2) ≤
      (B : ℝ) * ∑ i ∈ J, ∫ x, ‖f i x‖ ^ 2 := by
  classical
  apply schwartz_sum_norm_sq_le_of_fourier_overlap J f B
  intro ξ
  exact (Finset.card_le_card (Finset.filter_subset_filter _ hJI)).trans (hB ξ)

end FalconerPacking
