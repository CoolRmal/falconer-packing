/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InheritedFineCapSupport
import FalconerPacking.SelectedCapSpectralNormalized

/-!
# One spatial edge for actual surviving circle labels

All Fourier support, frame perturbation, and frequency-overlap hypotheses are derived
from the actual standard-cap/auxiliary-cell construction. Only the physical good-tube
mass tests remain explicit. The inherited functions are common to all spatial children;
the child-dependent choices enter solely through their selected ancestor sets. For source
Fourier data, `integrable_circle_planarMeasureFourier` supplies the integrability input.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap Filter Classical
open scoped ENNReal Topology

namespace FalconerPacking

/-- Selected-cap inflation instantiated for actual fine descendants and actual inherited frames.
The constant is independent of the source, circle radius, grids, marks, and spatial scales. -/
theorem selected_inheritedFineCapCircle_embedding (pwr K : ℕ) :
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
        (∑ i ∈ I, σ (E i) *
          ∫⁻ x, ‖∑ θ ∈ selection i, f θ x‖ₑ ^ 2
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
    selected_cap_normalized_grid_embedding_spectral_width 100 (by norm_num) pwr K
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  intro ψ hψ hzero S M F hS hM hSF R r a b L hR hrR hr₂ ha hab hb₁ hcurv
    hscale₀ hscale₁ hframe Llarge g hg k hk hkball keep I selection hselection
    σ hσ p j hj hcenters H
  dsimp only
  intro htest
  have hF : 0 < F := hS.trans_le hSF
  have hr : 0 < r := hR.trans_le hrR
  have hb : 0 < b := ha.trans_le hab
  let f := inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep
  have hf := hbound I (fineCapLabels S F) selection hselection σ
    (fun θ ↦ circleCapFrame (angularGridPoint F θ.2))
    (fun θ ↦ circleCapFrame (angularGridPoint S θ.1)) p a b L 24 j
    ha hab (by linarith) (by norm_num) (by norm_num at *; linarith) hj B H
    (fun θ ↦ r • angularDirection (angularGridPoint F θ.2)) f
    (fun θ hθ y t ↦ fineCapLabels_frame_perturbation hS hSF hframe hθ y t)
    hcenters htest
    (fun θ _ ↦ inheritedFineCapCircle_fourier_ball ψ hψ hzero S hS r hg k hk
      hR hr hr₂ ha (hab.trans hb₁) hM hF hscale₀ keep θ hkball)
    (fun z ↦ inheritedFineCapCircle_ball_overlap hS hSF hR hrR ha hscale₁ z)
    (fun θ _ z hz ↦ inheritedFineCapCircle_fourier_rectangle ψ hψ hzero S hS r hg k hk
      hR hr hr₂ ha (hab.trans hb₁) hb hb₁ hcurv hM hF hscale₀ keep θ hkball hz)
  simpa only [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_natCast] using hf

end FalconerPacking
