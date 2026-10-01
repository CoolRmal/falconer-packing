/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CutoffEnergyLocalization
import FalconerPacking.SelectedTubeWeights

/-!
# Selected local energies as nonnegative integrals

The local Fourier estimate is put in a form that can be summed with positive measure
weights and identified with the selected averaging measures.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- Quadratic Schwartz integrals agree with their extended nonnegative integrals on every set. -/
theorem ofReal_integral_schwartz_norm_sq
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    ENNReal.ofReal (∫ x in S, ‖f x‖ ^ 2) = ∫⁻ x in S, ‖f x‖ₑ ^ 2 := by
  have hi := (f.memLp 2 volume).integrable_norm_pow (p := 2) (by norm_num)
  rw [ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The selected local estimate permits arbitrary positive averaging weights. -/
theorem local_selected_fourier_lintegral (m : ℕ) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ {ι : Type*} (I J : Finset ι), J ⊆ I →
      ∀ (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (ξ : ι → EuclideanSpace ℝ (Fin 2)) (B : ℕ) (r s L : ℝ),
        0 < r → 0 < s → s⁻¹ ≤ r → 0 ≤ L →
        (∀ i ∈ I, Function.support (fun z ↦ 𝓕 (f i) z) ⊆ ball (ξ i) r) →
        (∀ z, (I.filter (fun i ↦ z ∈ ball (ξ i) r)).card ≤ B) →
        ∀ c : EuclideanSpace ℝ (Fin 2),
        (∫⁻ x in ball c s, ‖∑ i ∈ J, f i x‖ₑ ^ 2) ≤
          (9 * B : ℝ≥0∞) *
            (ENNReal.ofReal (C₀ ^ 2) * (∑ i ∈ J, ∫⁻ x in ball c (L * s), ‖f i x‖ₑ ^ 2) +
              ENNReal.ofReal ((C / (1 + L) ^ m) ^ 2) * ∑ i ∈ J, ∫⁻ x, ‖f i x‖ₑ ^ 2) := by
  obtain ⟨C₀, C, hC₀, hC, he⟩ := local_selected_fourier_energy m
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro ι I J hJI f ξ B r s L hr hs hsr hL hf hB c
  have h := ENNReal.ofReal_le_ofReal (he I J hJI f ξ B r s L hr hs hsr hL hf hB c)
  have hnonneg (S : Set (EuclideanSpace ℝ (Fin 2))) (i : ι) :
      0 ≤ ∫ x in S, ‖f i x‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hglobal (i : ι) : 0 ≤ ∫ x, ‖f i x‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 9 * B),
    ENNReal.ofReal_add
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hnonneg _ i))
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ ↦ hglobal i)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hnonneg _ i),
    ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hglobal i)] at h
  have hsum := ofReal_integral_schwartz_norm_sq (∑ i ∈ J, f i) (ball c s)
  simp only [sum_apply] at hsum
  rw [hsum] at h
  simp_rw [ofReal_integral_schwartz_norm_sq] at h
  have hg (i : ι) : ENNReal.ofReal (∫ x, ‖f i x‖ ^ 2) = ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
    simpa only [Measure.restrict_univ] using ofReal_integral_schwartz_norm_sq (f i) univ
  simp_rw [hg] at h
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast] using h

end FalconerPacking
