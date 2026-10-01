/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RetainedPinFamily
import FalconerPacking.PacketAnnularIdentity
import FalconerPacking.InheritedShellDecay

/-!
# The exact annular remainder is the inherited deleted packet density

This identifies the literal full annular source minus the measurable retained source. The
identity holds on the covered pin support and therefore also under the joint first norm.
-/

noncomputable section

open MeasureTheory Set Classical FourierTransform
open scoped ENNReal

namespace FalconerPacking

variable (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
  {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
  (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
  (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (s t K : ℕ)
  (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
  (Y : Set (EuclideanSpace ℝ (Fin 2))) {w : ℝ} (hw : 0 < w) (T k : ℕ)

include hw

/-- The full-minus-retained annular density is exactly the constructed deleted density. -/
theorem compactAnnularDensity_sub_retained_eq_deleted
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ finiteDyadicUnion (n 0) I) (hyY : y ∈ Y)
    (r : ℝ) :
    let ψ := 𝓕 (dyadicAnnularKernel T k)
    let hψ := hasCompactSupport_fourier_dyadicAnnularKernel T k
    let hzero := fourier_dyadicAnnularKernel_eventually_zero T k
    complexDistanceDensity
        (compactAnnularSource μ hμ (χ.postcompCLM Complex.ofRealCLM)
          (hasCompactSupport_complex_source_cutoff χ hχ) T (k + 1)) y r -
      complexDistanceDensity
        (retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y) y r =
      complexDistanceDensity
        (deletedPacketSum ((Finset.range (2 ^ s)) ×ˢ sourceWavePacketIndices χ hχ w)
          (inheritedPacketDeletionPins σ n e s t K L H I Y w 4)
          (fun i ↦ sourceWavePacket μ hμ ψ hψ hzero χ hχ
            (2 ^ s) (by positivity) w i.1 i.2) y) y r := by
  dsimp only
  have hQ := mem_finiteDyadicUnion_iff.mp hy
  have hyQ : y ∈ dyadicCube (n 0) (cubeIndex (n 0) y) := mem_dyadicCube_iff.mpr rfl
  apply complexDistanceDensity_sub_eq_of_source_add
  unfold retainedPinSource
  rw [dyadicSchwartzFamily_of_mem _ hQ hyQ]
  exact (initialRetainedSource_add_deletedPacketSum μ hμ
    (𝓕 (dyadicAnnularKernel T k)) (hasCompactSupport_fourier_dyadicAnnularKernel T k)
    (fourier_dyadicAnnularKernel_eventually_zero T k) χ hχ σ n e s t K L H I Y w
    hQ hyQ hyY).trans
      (sum_dyadic_sourceWavePacket_eq_compactAnnularSource μ hμ χ hχ T k
        (2 ^ s) (by positivity) hw)

/-- On a conull covered pin support, the actual annular remainder has exactly the already
bounded inherited deleted-packet first norm. No new analytic estimate is assumed. -/
theorem lintegral_compactAnnularDensity_sub_retained_eq_deleted
    (hσY : σ Yᶜ = 0) (hcover : σ (finiteDyadicUnion (n 0) I)ᶜ = 0) :
    let ψ := 𝓕 (dyadicAnnularKernel T k)
    let hψ := hasCompactSupport_fourier_dyadicAnnularKernel T k
    let hzero := fourier_dyadicAnnularKernel_eventually_zero T k
    (∫⁻ y, ∫⁻ r, ‖complexDistanceDensity
        (compactAnnularSource μ hμ (χ.postcompCLM Complex.ofRealCLM)
          (hasCompactSupport_complex_source_cutoff χ hχ) T (k + 1)) y r -
      complexDistanceDensity
        (retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y) y r‖ₑ
        ∂volume ∂σ) =
      ∫⁻ y, ∫⁻ r, ‖complexDistanceDensity
        (deletedPacketSum ((Finset.range (2 ^ s)) ×ˢ sourceWavePacketIndices χ hχ w)
          (inheritedPacketDeletionPins σ n e s t K L H I Y w 4)
          (fun i ↦ sourceWavePacket μ hμ ψ hψ hzero χ hχ
            (2 ^ s) (by positivity) w i.1 i.2) y) y r‖ₑ ∂volume ∂σ := by
  dsimp only
  apply lintegral_congr_ae
  filter_upwards [ae_iff.mpr hσY, ae_iff.mpr hcover] with y hyY hy
  apply lintegral_congr
  intro r
  rw [compactAnnularDensity_sub_retained_eq_deleted μ hμ χ hχ σ n e s t K L H I
    Y hw T k hy hyY r]

end FalconerPacking
