/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedCapSpectralNormalized
public import FalconerPacking.InheritedEnergyPartition

/-!
# Selected-cap embedding summed over angular parents

The parent masks are exact zero-or-original Schwartz functions. Summation removes them
from the local and error energies, rather than multiplying either term by the number
of angular parents.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- Summing parent masks preserves the actual nonnegative Lebesgue energy exactly. -/
theorem sum_parent_masked_schwartz_energy {κ α : Type*}
    (J : Finset κ) (A : Finset α) (parent : κ → α) (hparent : ∀ θ ∈ J, parent θ ∈ A)
    (f : κ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) :
    (∑ a ∈ A, ∑ θ ∈ J, ∫⁻ x, ‖(if parent θ = a then f θ else 0) x‖ₑ ^ 2 ∂ν) =
      ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2 ∂ν := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [Finset.sum_eq_single_of_mem (parent θ) (hparent θ hθ)]
  · simp only [↓reduceIte]
  · intro a _ ha
    simp only [if_neg (Ne.symm ha), zero_apply, enorm_zero,
      zero_pow (by decide : 2 ≠ 0), lintegral_zero]

/-- The spectral-width estimate summed over every angular parent, without a parent-count loss. -/
theorem selected_cap_parent_grid_embedding_spectral_width
    (F : ℝ) (hF : 1 ≤ F) (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {κ α : Type*} (I : Finset (Fin 2 → ℤ)) (J : Finset κ) (A : Finset α)
        (parent : κ → α), (∀ θ ∈ J, parent θ ∈ A) →
      ∀ (selection : (Fin 2 → ℤ) → Finset κ), (∀ i ∈ I, selection i ⊆ J) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (O V : κ → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (p : EuclideanSpace ℝ (Fin 2)) (a b L C₀ : ℝ) (j : ℕ),
        0 < a → a ≤ b → 8 ≤ L → 0 ≤ C₀ → 2 * (5 + 7 * C₀) ≤ L → j < K →
      ∀ (B : ℕ) (H : ℝ≥0∞) (ξ : κ → EuclideanSpace ℝ (Fin 2))
        (f : κ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
        (∀ θ ∈ J, ∀ y i, |(V θ y) i - (O θ y) i| ≤ C₀ * (a / b) * ‖y‖) →
        (∀ k ∈ I, ∀ i, |(gridSquareCenter a k) i - p i| ≤ b / 2) →
        let E := enlargedGridSquare a (L ^ (2 * j + 2))
        let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
          (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
        (∀ i ∈ I, ∀ θ ∈ selection i,
          σ (frameRectangle (V θ) (gridSquareCenter a i)
            (L ^ (4 * K + 20) * a / 2) (L ^ (4 * K + 20) * b / 2) ∩ P) ≤
              H * ENNReal.ofReal (a / b) * σ P) →
        (∀ θ ∈ J, Function.support (fun z ↦ 𝓕 (f θ) z) ⊆ ball (ξ θ) (F / a)) →
        (∀ z, (J.filter (fun θ ↦ z ∈ ball (ξ θ) (F / a))).card ≤ B) →
        (∀ θ ∈ J, ∀ z ∈ Function.support
          (𝓕 (f θ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          |(O θ (z - ξ θ)) 0| ≤ F / a ∧ |(O θ (z - ξ θ)) 1| ≤ F / b) →
        (∑ α ∈ A, ∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ (selection i).filter (fun θ ↦ parent θ = α), f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
          ENNReal.ofReal C * B *
            (ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P *
                (∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2
                  ∂((volume P)⁻¹ • volume.restrict P)) +
              ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P *
                ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ :=
    selected_cap_normalized_grid_embedding_spectral_width F hF pwr K
  refine ⟨C, hC, ?_⟩
  intro κ α I J A parent hparent selection hselection σ _ O V p a b L C₀ j
    ha hab hL hC₀ hsize hj B H ξ f hframe hcenters
  dsimp only
  intro htest hballs hB hrect
  let E := enlargedGridSquare a (L ^ (2 * j + 2))
  let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
    (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
  have hm (α : α) := hbound I J selection hselection σ O V p a b L C₀ j
    ha hab hL hC₀ hsize hj B H ξ (fun θ ↦ if parent θ = α then f θ else 0)
    hframe hcenters htest
    (fun θ hθ ↦ by
      split_ifs with h
      · exact hballs θ hθ
      · change Function.support (fun z ↦ ((SchwartzMap.fourierTransformCLM ℂ) 0) z) ⊆ _
        intro z hz
        exact (hz (by simp only [map_zero, zero_apply])).elim) hB
    (fun θ hθ z hz ↦ by
      split_ifs at hz with h
      · exact hrect θ hθ z hz
      · change z ∈ Function.support ((SchwartzMap.fourierTransformCLM ℂ) 0 :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) at hz
        simp only [map_zero, FunLike.coe_zero, Function.support_zero, mem_empty_iff_false] at hz)
  have hpoint (α : α) (i : Fin 2 → ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
      (∑ θ ∈ selection i, (if parent θ = α then f θ else 0) x) =
      ∑ θ ∈ (selection i).filter (fun θ ↦ parent θ = α), f θ x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro θ _
    split_ifs <;> rfl
  simp_rw [hpoint] at hm
  have hsum := Finset.sum_le_sum (fun α (_ : α ∈ A) ↦ hm α)
  apply hsum.trans_eq
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_parent_masked_schwartz_energy J A parent hparent f,
    sum_parent_masked_schwartz_energy J A parent hparent f]

end FalconerPacking
