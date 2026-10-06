/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourceWavePackets
public import FalconerPacking.LocalizedPacketMass
public import FalconerPacking.ComplexDistancePushforward

/-!
# First norms of the constructed source packets

The exact source wave packet construction satisfies the geometric convolution bound.
Its actual pinned distance density obeys the same bound by the proved first-norm contraction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- The actual complex pinned density contracts the extended first norm as well. -/
theorem lintegral_enorm_complexDistanceDensity_le
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (hf : Measurable f) (hi : Integrable f volume)
    (y : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ t, ‖complexDistanceDensity f y t‖ₑ) ≤ ∫⁻ x, ‖f x‖ₑ := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_complexDistanceDensity hf hi y),
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  exact ENNReal.ofReal_le_ofReal (integral_norm_complexDistanceDensity_le hf hi y)

/-- The exact constructed packet, with its actual inverse cap kernel, has the source-strip
mass bound. No localization estimate is included as a hypothesis. -/
theorem lintegral_enorm_sourceWavePacket_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w)
    (j : ℕ) (k : ℤ) :
    (∫⁻ x, ‖sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x‖ₑ) ≤
      (∫⁻ z, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖ₑ) *
        μ (packetSourceStrip (sourceWavePacketNormal N j) (w * k) (2 * w)) +
      (∫⁻ z in {z | w ≤ |⟪sourceWavePacketNormal N j, z⟫|},
        ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖ₑ) * μ univ := by
  have hbound (x) : |smoothStripPacket χ w (sourceWavePacketNormal N j) k x| ≤ 1 := by
    rw [smoothStripPacket, abs_mul,
      abs_of_nonneg (smoothStripWeight_nonneg w k _)]
    exact mul_le_one₀ (hχone x) (smoothStripWeight_nonneg w k _)
      (smoothStripWeight_le_one w k _)
  have hs : Function.support (smoothStripPacket χ w (sourceWavePacketNormal N j) k) ⊆
      packetSourceStrip (sourceWavePacketNormal N j) (w * k) w := by
    intro x hx
    have h : |⟪sourceWavePacketNormal N j, x⟫ - w * k| < w :=
      (support_smoothStripPacket χ hw (sourceWavePacketNormal N j) k hx).2
    exact h.le
  simpa only [sourceWavePacket_apply, schwartzMeasureDensity, Complex.real_smul] using
    lintegral_enorm_strip_packet_le μ (𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j))
      (smoothStripPacket χ w (sourceWavePacketNormal N j) k)
      (contDiff_smoothStripPacket χ w (sourceWavePacketNormal N j) k).continuous
      hbound (sourceWavePacketNormal N j) (w * k) w hs

/-- The same source-strip and tail bound holds for the actual pinned distance density
of every constructed packet, at every pin. -/
theorem lintegral_enorm_pinned_sourceWavePacket_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w)
    (j : ℕ) (k : ℤ) (y : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ t, ‖complexDistanceDensity
      (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y t‖ₑ) ≤
      (∫⁻ z, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖ₑ) *
        μ (packetSourceStrip (sourceWavePacketNormal N j) (w * k) (2 * w)) +
      (∫⁻ z in {z | w ≤ |⟪sourceWavePacketNormal N j, z⟫|},
        ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) z‖ₑ) * μ univ :=
  (lintegral_enorm_complexDistanceDensity_le
    (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k).continuous.measurable
    (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k).integrable y).trans
      (lintegral_enorm_sourceWavePacket_le μ hμ ψ hψ hzero χ hχ hχone N hN hw j k)

end FalconerPacking
