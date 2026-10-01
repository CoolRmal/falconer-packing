/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ScaledBandlimitedCutoff

/-!
# Spatial energy localization with a rapidly decreasing tail

The actual bandlimited cutoff localizes the squared norm to an enlarged ball. The
remaining global term decays to arbitrary polynomial order, uniformly in center and scale.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap
open Classical

namespace FalconerPacking

/-- The constructed cutoffs are globally bounded and rapidly small outside the enlarged ball. -/
theorem scaledFourierCutoff_uniform_bounds (m : ℕ) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧ ∀ s (hs : 0 < s) c L, 0 ≤ L →
      (∀ x, ‖scaledFourierCutoff s hs c x‖ ≤ C₀) ∧
      (∀ x ∉ ball c (L * s), ‖scaledFourierCutoff s hs c x‖ ≤ C / (1 + L) ^ m) := by
  obtain ⟨C₀, hC₀, hb⟩ := scaledFourierCutoff_decay 0
  obtain ⟨C, hC, hd⟩ := scaledFourierCutoff_decay m
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro s hs c L hL
  refine ⟨fun x ↦ by simpa only [pow_zero, div_one] using hb s hs c x, ?_⟩
  intro x hx
  have hdist : L ≤ ‖x - c‖ / s := by
    apply (le_div_iff₀ hs).mpr
    simpa only [mem_ball, dist_eq_norm, not_lt] using hx
  exact (hd s hs c x).trans (div_le_div_of_nonneg_left hC.le (by positivity)
    (pow_le_pow_left₀ (by positivity) (by linarith) m))

/-- The cutoff's local quadratic energy has a uniform, arbitrarily small global tail. -/
theorem scaledFourierCutoff_product_energy (m : ℕ) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ s (hs : 0 < s) (c : EuclideanSpace ℝ (Fin 2)) (L : ℝ), 0 ≤ L →
      ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ,
        (∫ x, ‖scaledFourierCutoff s hs c x * f x‖ ^ 2) ≤
          C₀ ^ 2 * (∫ x in ball c (L * s), ‖f x‖ ^ 2) +
            (C / (1 + L) ^ m) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  obtain ⟨C₀, C, hC₀, hC, hb⟩ := scaledFourierCutoff_uniform_bounds m
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro s hs c L hL f
  obtain ⟨hbound, htail⟩ := hb s hs c L hL
  have hf : Integrable (fun x ↦ ‖f x‖ ^ 2) volume :=
    (f.memLp 2 volume).integrable_norm_pow (by norm_num)
  have hp₀ := ((pairing (ContinuousLinearMap.mul ℂ ℂ)
    (scaledFourierCutoff s hs c) f).memLp 2 volume).integrable_norm_pow
      (p := 2) (by norm_num)
  have hp : Integrable (fun x ↦ ‖scaledFourierCutoff s hs c x * f x‖ ^ 2) volume := by
    simpa only [pairing_apply_apply, ContinuousLinearMap.mul_apply'] using hp₀
  rw [← integral_add_compl measurableSet_ball hp]
  apply add_le_add
  · calc
      _ ≤ ∫ x in ball c (L * s), C₀ ^ 2 * ‖f x‖ ^ 2 := by
        apply integral_mono hp.integrableOn (hf.const_mul _).integrableOn
        intro x
        dsimp only
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2) (sq_nonneg _)
      _ = _ := integral_const_mul _ _
  · calc
      _ ≤ ∫ x in (ball c (L * s))ᶜ, (C / (1 + L) ^ m) ^ 2 * ‖f x‖ ^ 2 := by
        apply setIntegral_mono_on hp.integrableOn (hf.const_mul _).integrableOn
          measurableSet_ball.compl
        intro x hx
        rw [norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (htail x hx) 2) (sq_nonneg _)
      _ = (C / (1 + L) ^ m) ^ 2 * ∫ x in (ball c (L * s))ᶜ, ‖f x‖ ^ 2 :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hf (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _))
        (sq_nonneg _)

/-- Every selected family has uniform local orthogonality with an explicit decaying tail. -/
theorem local_selected_fourier_energy (m : ℕ) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ {ι : Type*} (I J : Finset ι), J ⊆ I →
      ∀ (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (ξ : ι → EuclideanSpace ℝ (Fin 2)) (B : ℕ) (r s L : ℝ),
        0 < r → 0 < s → s⁻¹ ≤ r → 0 ≤ L →
        (∀ i ∈ I, Function.support (fun z ↦ 𝓕 (f i) z) ⊆ ball (ξ i) r) →
        (∀ z, (I.filter (fun i ↦ z ∈ ball (ξ i) r)).card ≤ B) →
        ∀ c : EuclideanSpace ℝ (Fin 2),
        (∫ x in ball c s, ‖∑ i ∈ J, f i x‖ ^ 2) ≤
          (9 * B : ℝ) *
            (C₀ ^ 2 * (∑ i ∈ J, ∫ x in ball c (L * s), ‖f i x‖ ^ 2) +
              (C / (1 + L) ^ m) ^ 2 * ∑ i ∈ J, ∫ x, ‖f i x‖ ^ 2) := by
  classical
  obtain ⟨C₀, C, hC₀, hC, he⟩ := scaledFourierCutoff_product_energy m
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro ι I J hJI f ξ B r s L hr hs hsr hL hf hB c
  have hv := (support_fourier_scaledFourierCutoff s hs c).trans (ball_subset_ball hsr)
  have hlocal := schwartz_local_selected_orthogonality I J hJI f
    (scaledFourierCutoff s hs c) ξ hr B hf hv hB measurableSet_ball
    (fun x hx ↦ one_le_norm_scaledFourierCutoff s hs c x
      (by simpa only [mem_ball, dist_eq_norm] using (mem_ball.mp hx).le))
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ i ∈ J, (C₀ ^ 2 * (∫ x in ball c (L * s), ‖f i x‖ ^ 2) +
        (C / (1 + L) ^ m) ^ 2 * ∫ x, ‖f i x‖ ^ 2) :=
      Finset.sum_le_sum (fun i _ ↦ he s hs c L hL (f i))
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end FalconerPacking
