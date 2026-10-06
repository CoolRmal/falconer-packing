/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedLocalEnergy

/-!
# Summation of child-dependent selected Fourier energies

The selected labels are rearranged exactly. The main term never restores labels omitted
at an individual child; only the harmless remote error is enlarged to all labels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- The weighted averaging measure for one label, retaining its actual child selections. -/
def selectedCapMeasure {α ι κ : Type*} [MeasurableSpace α]
    (I : Finset ι) (selection : ι → Finset κ) (w : ι → ℝ≥0∞)
    (μ : ι → Measure α) (θ : κ) : Measure α :=
  selectedAveragingMeasure (I.filter fun i ↦ θ ∈ selection i) w μ

/-- Exact interchange of the finite child and label sums. -/
theorem sum_selected_weights_eq {ι κ : Type*}
    (I : Finset ι) (J : Finset κ) (selection : ι → Finset κ)
    (hselection : ∀ i ∈ I, selection i ⊆ J)
    (w : ι → ℝ≥0∞) (F : κ → ι → ℝ≥0∞) :
    ∑ i ∈ I, w i * ∑ θ ∈ selection i, F θ i =
      ∑ θ ∈ J, ∑ i ∈ I with θ ∈ selection i, w i * F θ i := by
  classical
  have hfilter (i : ι) (hi : i ∈ I) :
      J.filter (fun θ ↦ θ ∈ selection i) = selection i := by
    ext θ
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h ↦ ⟨hselection i hi h, h⟩⟩
  calc
    _ = ∑ i ∈ I, ∑ θ ∈ J, if θ ∈ selection i then w i * F θ i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, hfilter i hi, Finset.mul_sum]
    _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_filter]

/-- The rearranged main term is the actual integral against the selected cap measure. -/
theorem sum_selected_integrals_eq {α ι κ : Type*} [MeasurableSpace α]
    (I : Finset ι) (J : Finset κ) (selection : ι → Finset κ)
    (hselection : ∀ i ∈ I, selection i ⊆ J)
    (w : ι → ℝ≥0∞) (μ : ι → Measure α) (F : κ → α → ℝ≥0∞) :
    ∑ i ∈ I, w i * ∑ θ ∈ selection i, ∫⁻ x, F θ x ∂μ i =
      ∑ θ ∈ J, ∫⁻ x, F θ x ∂selectedCapMeasure I selection w μ θ := by
  rw [sum_selected_weights_eq I J selection hselection]
  apply Finset.sum_congr rfl
  intro θ hθ
  simp only [selectedCapMeasure, selectedAveragingMeasure,
    lintegral_finsetSum_measure, lintegral_smul_measure, smul_eq_mul]

/-- Summed local orthogonality has one selected measure for each Fourier label, with
an explicit total-weight loss only in the remote term. -/
theorem weighted_selected_fourier_ball_sum (m : ℕ) :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧
      ∀ {ι κ : Type*} (I : Finset ι) (J : Finset κ) (selection : ι → Finset κ),
        (∀ i ∈ I, selection i ⊆ J) →
      ∀ (f : κ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
        (ξ : κ → EuclideanSpace ℝ (Fin 2))
        (q : ι → EuclideanSpace ℝ (Fin 2)) (w : ι → ℝ≥0∞)
        (B : ℕ) (r s L : ℝ), 0 < r → 0 < s → s⁻¹ ≤ r → 0 ≤ L →
        (∀ θ ∈ J, Function.support (fun z ↦ 𝓕 (f θ) z) ⊆ ball (ξ θ) r) →
        (∀ z, (J.filter (fun θ ↦ z ∈ ball (ξ θ) r)).card ≤ B) →
        (∑ i ∈ I, w i *
          ∫⁻ x in ball (q i) s, ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2) ≤
          (9 * B : ℝ≥0∞) *
            (ENNReal.ofReal (C₀ ^ 2) *
                (∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2 ∂selectedCapMeasure I selection w
                  (fun i ↦ volume.restrict (ball (q i) (L * s))) θ) +
              ENNReal.ofReal ((C / (1 + L) ^ m) ^ 2) *
                (∑ i ∈ I, w i) * ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  obtain ⟨C₀, C, hC₀, hC, he⟩ := local_selected_fourier_lintegral m
  refine ⟨C₀, C, hC₀, hC, ?_⟩
  intro ι κ I J selection hselection f ξ q w B r s L hr hs hsr hL hf hB
  calc
    _ ≤ ∑ i ∈ I, w i * ((9 * B : ℝ≥0∞) *
        (ENNReal.ofReal (C₀ ^ 2) *
            (∑ θ ∈ selection i, ∫⁻ x in ball (q i) (L * s), ‖f θ x‖ₑ ^ 2) +
          ENNReal.ofReal ((C / (1 + L) ^ m) ^ 2) *
            ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_right
      apply (he J (selection i) (hselection i hi) f ξ B r s L hr hs hsr hL hf hB (q i)).trans
      apply mul_le_mul_right
      apply add_le_add le_rfl
      apply mul_le_mul_right
      exact Finset.sum_le_sum_of_subset (hselection i hi)
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hmain := sum_selected_integrals_eq I J selection hselection w
        (fun i ↦ volume.restrict (ball (q i) (L * s))) (fun θ x ↦ ‖f θ x‖ₑ ^ 2)
      congr 1
      · simp_rw [show ∀ i, w i * ((9 * B : ℝ≥0∞) *
            (ENNReal.ofReal (C₀ ^ 2) *
              (∑ θ ∈ selection i, ∫⁻ x in ball (q i) (L * s), ‖f θ x‖ₑ ^ 2))) =
            ((9 * B : ℝ≥0∞) * ENNReal.ofReal (C₀ ^ 2)) *
              (w i * ∑ θ ∈ selection i, ∫⁻ x in ball (q i) (L * s), ‖f θ x‖ₑ ^ 2)
          from fun i ↦ by ring]
        rw [← Finset.mul_sum, hmain]
        ring
      · rw [← Finset.sum_mul]
        ring

end FalconerPacking
