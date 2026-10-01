/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SelectedCapParentEmbedding
import FalconerPacking.SelectedFineCapEmbedding
import FalconerPacking.SelectedCoarseCapEmbedding

/-!
# Actual circle edges summed over angular parents

The actual circle geometry discharges all spectral hypotheses. Both the retained main
term and the global error are summed over parent angular labels without a counting loss.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Filter Classical
open scoped ENNReal Topology

namespace FalconerPacking

/-- Selected-cap inflation instantiated for actual fine descendants and actual inherited frames.
The constant is independent of the source, circle radius, grids, marks, and spatial scales. -/
theorem selected_inheritedFineCapCircle_parents_embedding (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (S M F : ℕ) (hS : 0 < S), 0 < M → S ≤ F →
      ∀ (R r a b L : ℝ), 0 < R → R ≤ r → r ≤ 2 * R →
        0 < a → a ≤ b → b ≤ 1 → b ≤ R * a ^ 2 →
        R * a ≤ F → (F : ℝ) ≤ 2 * (R * a) → (S : ℝ)⁻¹ ≤ a / b → 346 ≤ L →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → ℂ)
        (hg : Integrable g (normalizedCircleMeasure r))
        (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k),
        Function.support k ⊆ closedBall 0 1 →
      ∀ {α : Type*} (A : Finset α) (parent : ℕ × ℕ → α),
        (∀ θ ∈ fineCapLabels S F, parent θ ∈ A) →
      ∀ (keep : ℕ × ℕ → Prop) (I : Finset (Fin 2 → ℤ))
        (selection : (Fin 2 → ℤ) → Finset (ℕ × ℕ)),
        (∀ i ∈ I, selection i ⊆ fineCapLabels S F) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (p : EuclideanSpace ℝ (Fin 2)) (j : ℕ), j < K →
        (∀ i ∈ I, ∀ t, |(gridSquareCenter a i) t - p t| ≤ b / 2) →
      ∀ (H : ℝ≥0∞),
        let E := enlargedGridSquare a (L ^ (2 * j + 2))
        let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
          (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
        let f := inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep
        (∀ i ∈ I, ∀ θ ∈ selection i,
          σ (frameRectangle (circleCapFrame (angularGridPoint S θ.1)) (gridSquareCenter a i)
            (L ^ (4 * K + 20) * a / 2) (L ^ (4 * K + 20) * b / 2) ∩ P) ≤
              H * ENNReal.ofReal (a / b) * σ P) →
        (∑ α ∈ A, ∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ (selection i).filter (fun θ ↦ parent θ = α), f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P *
                (∑ θ ∈ fineCapLabels S F, ∫⁻ x, ‖f θ x‖ₑ ^ 2
                  ∂((volume P)⁻¹ • volume.restrict P)) +
              ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P *
                ∑ θ ∈ fineCapLabels S F, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  let B := Nat.ceil (200 + 8 * Real.pi) * Nat.ceil (200 + 2 * Real.pi)
  have hB : (0 : ℝ) < B := by dsimp [B]; positivity
  obtain ⟨C, hC, hbound⟩ :=
    selected_cap_parent_grid_embedding_spectral_width 100 (by norm_num) pwr K
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro ψ hψ hzero S M F hS hM hSF R r a b L hR hrR hr₂ ha hab hb₁ hcurv
    hscale₀ hscale₁ hframe Llarge g hg k hk hkball α A parent hparent keep I selection hselection
    σ hσ p j hj hcenters H
  dsimp only
  intro htest
  have hF : 0 < F := hS.trans_le hSF
  have hr : 0 < r := hR.trans_le hrR
  have hb : 0 < b := ha.trans_le hab
  let f := inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep
  have hf := hbound I (fineCapLabels S F) A parent hparent selection hselection σ
    (fun θ ↦ circleCapFrame (angularGridPoint F θ.2))
    (fun θ ↦ circleCapFrame (angularGridPoint S θ.1)) p a b L 24 j
    ha hab (by linarith) (by norm_num) (by norm_num; exact Llarge) hj B H
    (fun θ ↦ r • angularDirection (angularGridPoint F θ.2)) f
    (fun θ hθ y t ↦ fineCapLabels_frame_perturbation hS hSF hframe hθ y t)
    hcenters htest
    (fun θ _ ↦ inheritedFineCapCircle_fourier_ball ψ hψ hzero S hS r hg k hk
      hR hr hr₂ ha (hab.trans hb₁) hM hF hscale₀ keep θ hkball)
    (fun z ↦ inheritedFineCapCircle_ball_overlap hS hSF hR hrR ha hscale₁ z)
    (fun θ _ z hz ↦ inheritedFineCapCircle_fourier_rectangle ψ hψ hzero S hS r hg k hk
      hR hr hr₂ ha (hab.trans hb₁) hb hb₁ hcurv hM hF hscale₀ keep θ hkball hz)
  simpa only [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_natCast] using hf


/-- Selected-cap inflation instantiated for actual coarse ancestors of arbitrary surviving terminal descendants.
The constant is independent of the source, circle radius, grids, marks, and spatial scales. -/
theorem selected_inheritedCoarseCapCircle_parents_embedding (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (S M N T : ℕ) (hS : 0 < S), 0 < M → 0 < N → S = M * N →
      ∀ (R r a b L : ℝ), 0 < R → R ≤ r → r ≤ 2 * R →
        0 < a → a ≤ b → b ≤ 1 → b ≤ R * a ^ 2 →
        R * a ≤ N → (N : ℝ) ≤ 2 * (R * a) → 10 ≤ L →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → ℂ)
        (hg : Integrable g (normalizedCircleMeasure r))
        (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k),
        Function.support k ⊆ closedBall 0 1 →
      ∀ {α : Type*} (A : Finset α) (parent : ℕ → α),
        (∀ θ ∈ Finset.range N, parent θ ∈ A) →
      ∀ (keep : ℕ × ℕ → Prop) (I : Finset (Fin 2 → ℤ))
        (selection : (Fin 2 → ℤ) → Finset ℕ),
        (∀ i ∈ I, selection i ⊆ Finset.range N) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (p : EuclideanSpace ℝ (Fin 2)) (j : ℕ), j < K →
        (∀ i ∈ I, ∀ t, |(gridSquareCenter a i) t - p t| ≤ b / 2) →
      ∀ (H : ℝ≥0∞),
        let E := enlargedGridSquare a (L ^ (2 * j + 2))
        let P := frameRectangle (LinearIsometryEquiv.refl ℝ _) p
          (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)
        let f := inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M T keep
        (∀ i ∈ I, ∀ θ ∈ selection i,
          σ (frameRectangle (circleCapFrame (angularGridPoint N θ)) (gridSquareCenter a i)
            (L ^ (4 * K + 20) * a / 2) (L ^ (4 * K + 20) * b / 2) ∩ P) ≤
              H * ENNReal.ofReal (a / b) * σ P) →
        (∑ α ∈ A, ∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ (selection i).filter (fun θ ↦ parent θ = α), f θ x‖ₑ ^ 2
            ∂((volume (E i))⁻¹ • volume.restrict (E i))) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ P *
                (∑ θ ∈ Finset.range N, ∫⁻ x, ‖f θ x‖ₑ ^ 2
                  ∂((volume P)⁻¹ • volume.restrict P)) +
              ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ P *
                ∑ θ ∈ Finset.range N, ∫⁻ x, ‖f θ x‖ₑ ^ 2) := by
  let B := Nat.ceil (2000 + 2 * Real.pi)
  have hB : (0 : ℝ) < B := by dsimp [B]; positivity
  obtain ⟨C, hC, hbound⟩ :=
    selected_cap_parent_grid_embedding_spectral_width 1000 (by norm_num) pwr K
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro ψ hψ hzero S M N T hS hM hN hsize R r a b L hR hrR hr₂ ha hab hb₁ hcurv
    hscale₀ hscale₁ Llarge g hg k hk hkball α A parent hparent keep I selection hselection
    σ hσ p j hj hcenters H
  dsimp only
  intro htest
  have hr : 0 < r := hR.trans_le hrR
  have hb : 0 < b := ha.trans_le hab
  let f := inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M T keep
  have hf := hbound I (Finset.range N) A parent hparent selection hselection σ
    (fun θ ↦ circleCapFrame (angularGridPoint N θ))
    (fun θ ↦ circleCapFrame (angularGridPoint N θ)) p a b L 0 j
    ha hab (by linarith) (by norm_num) (by norm_num; exact Llarge) hj B H
    (fun θ ↦ r • angularDirection (angularGridPoint N θ)) f
    (fun _ _ _ _ ↦ by simp)
    hcenters htest
    (fun θ _ ↦ inheritedCoarseCapCircle_fourier_ball ψ hψ hzero S hS r hg k hk
      hR hr hr₂ ha (hab.trans hb₁) hM hN hsize hscale₀ keep θ hkball)
    (fun z ↦ inheritedCoarseCapCircle_ball_overlap hN hR hrR ha hscale₁ z)
    (fun θ _ z hz ↦ inheritedCoarseCapCircle_fourier_rectangle ψ hψ hzero S hS r hg k hk
      hR hr hr₂ ha (hab.trans hb₁) hb hb₁ hcurv hM hN hsize hscale₀ keep θ hkball hz)
  simpa only [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_natCast] using hf

end FalconerPacking
