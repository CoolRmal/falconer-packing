/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SelectedCapSpectralWidth

/-!
# Normalized selected-cap embedding for thickened Fourier rectangles

The spectral enlargement affects the uniform constant only. Physical grid squares,
source measures, selected tests, and all scale exponents remain unchanged.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Classical
open scoped ENNReal

namespace FalconerPacking

/-- The selected-cap inflation bound for an arbitrary fixed spectral-width constant. -/
theorem selected_cap_normalized_grid_embedding_spectral_width
    (F : ℝ) (hF : 1 ≤ F) (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {κ : Type*} (I : Finset (Fin 2 → ℤ)) (J : Finset κ)
        (selection : (Fin 2 → ℤ) → Finset κ), (∀ i ∈ I, selection i ⊆ J) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (O V : κ → EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
        (p : EuclideanSpace ℝ (Fin 2)) (a b L C₀ : ℝ) (j : ℕ),
        0 < a → a ≤ b → 8 ≤ L → 0 ≤ C₀ → 2 * (5 + 7 * C₀) ≤ L → j < K →
      ∀ (B : ℕ) (H : ℝ≥0∞)
        (ξ : κ → EuclideanSpace ℝ (Fin 2))
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
          |(O θ (z - ξ θ)) 0| ≤ (F / a) ∧ |(O θ (z - ξ θ)) 1| ≤ F / b) →
        (∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
          ENNReal.ofReal C * B *
            (ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P *
                (∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2
                  ∂((volume P)⁻¹ • volume.restrict P)) +
              ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P *
                ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  let n := pwr + 4 * K + 20
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, he⟩ := selected_cap_grid_embedding_spectral_width F hF n
  let k := ∫ x, ‖unitReproducingKernel x‖
  let S := SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
    SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel
  have hk : 0 ≤ k := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hS : 0 ≤ S := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  let Cm := 9 * C₁ ^ 2 * k * 81 * S * 49 * Real.pi
  let Ct := 9 * (C₁ ^ 2 * k * C₃ * 49 * Real.pi * 2 ^ n + C₂ ^ 2 * 49)
  let C := 1 + Cm + Ct
  have hm : 0 ≤ Cm := by dsimp [Cm]; positivity
  have ht : 0 ≤ Ct := by dsimp [Ct]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hmC : ENNReal.ofReal Cm ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  have htC : ENNReal.ofReal Ct ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  refine ⟨C, hC, ?_⟩
  intro κ I J selection hselection σ hσ O V p a b L C₀ j
    ha hab hL hC₀ hsize hj B H ξ f hframe hcenters
  dsimp only
  intro htest hballs hB hrect
  let E := enlargedGridSquare a (L ^ (2 * j + 2))
  let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
    (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
  let X := ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2 ∂((volume P)⁻¹ • volume.restrict P)
  let Y := ∑ θ ∈ J, ∫⁻ x, ‖f θ x‖ₑ ^ 2
  have h := he I J selection hselection σ O V p a b L C₀ j K
    ha hab hL hC₀ hsize hj B H ξ f hframe hcenters htest hballs hB hrect
  have hkernel : ENNReal.ofReal k = ∫⁻ x, ‖unitReproducingKernel x‖ₑ :=
    ofReal_integral_norm_eq_lintegral_enorm unitReproducingKernel.integrable
  dsimp only at h
  rw [← hkernel] at h
  have hc := selected_cap_normalized_coefficient_bound ha hab (by linarith : 1 ≤ L)
    hC₁.le hC₂.le hC₃.le hk hS j K pwr n hj le_rfl
    (selected_cap_grid_overlap_constant_le (by linarith) j) B H (σ P) X Y
  apply h.trans (hc.trans ?_)
  change ENNReal.ofReal Cm * B * ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P * X +
      ENNReal.ofReal Ct * B * ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P * Y ≤ _
  calc
    _ ≤ ENNReal.ofReal C * B * ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P * X +
        ENNReal.ofReal C * B * ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P * Y := by
      gcongr
    _ = _ := by ring

end FalconerPacking
