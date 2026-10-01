/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.StandardCapKernelBounds
import FalconerPacking.PacketDeletionMass

/-!
# Deletion bounds for the actual standard dyadic packets

The kernel first norms and transverse tails are discharged for the concrete cap construction.
The remaining mass is exactly that of the source-pin pairs selected for deletion.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Actual packet deletion with uniform constants and no assumed cap-kernel bounds. -/
theorem exists_standard_dyadic_packet_deletion_bound
    (T m : ℕ) (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))} (hX : MeasurableSet X) (hμX : μ Xᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ ‖y - x‖) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ n : ℕ,
      let N := 64 * 2 ^ (2 * T * n)
      let hN : 0 < N := by dsimp only [N]; positivity
      ∀ (J : Finset ℤ) (w C : ℝ), 0 < w → 2 ≤ C →
      ∀ (P : ℕ × ℤ → Set (EuclideanSpace ℝ (Fin 2))),
      (∀ i ∈ (Finset.range N) ×ˢ J, MeasurableSet (P i)) →
      (∀ i ∈ (Finset.range N) ×ˢ J, P i ⊆ Y) →
      (∀ i ∈ (Finset.range N) ×ˢ J, P i ⊆
        packetSourceStrip (sourceWavePacketNormal N i.1) (w * i.2) (C * w)) →
      (∫⁻ y, ∫⁻ t, ‖complexDistanceDensity
        (deletedPacketSum ((Finset.range N) ×ˢ J) P
          (fun i ↦ sourceWavePacket μ hμ (𝓕 (dyadicAnnularKernel (4 * T) n))
            (hasCompactSupport_fourier_dyadicAnnularKernel (4 * T) n)
            (fourier_dyadicAnnularKernel_eventually_zero (4 * T) n)
            χ hχ N hN w i.1 i.2) y) y t‖ₑ ∂volume ∂ν) ≤
        ENNReal.ofReal C₀ *
          ((Nat.ceil ((2 * C + 1) * (8 * C * w * N / δ + 4 * Real.pi)) : ℝ≥0∞) *
            (ν.prod μ) (⋃ i ∈ (Finset.range N) ×ˢ J,
              P i ×ˢ (X ∩ packetSourceStrip
                (sourceWavePacketNormal N i.1) (w * i.2) (2 * w)))) +
        ENNReal.ofReal (C₁ / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) * w) ^ m) *
          μ univ * (((Finset.range N) ×ˢ J).card * ν univ) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hkernel⟩ := exists_uniform_standardCapKernel_bounds T m
  refine ⟨C₀, C₁, hC₀, hC₁, fun n ↦ ?_⟩
  dsimp only
  intro J w C hw hC P hP hPY hPT
  apply lintegral_enorm_deleted_sourceWavePackets_le μ ν hμ
    (𝓕 (dyadicAnnularKernel (4 * T) n))
    (hasCompactSupport_fourier_dyadicAnnularKernel (4 * T) n)
    (fourier_dyadicAnnularKernel_eventually_zero (4 * T) n)
    χ hχ hχone hX hμX (by positivity) J hw hC hδ hsep P hP hPY hPT
  · intro j _
    exact (hkernel n j).1
  · intro j _
    exact (hkernel n j).2 w hw

end FalconerPacking
