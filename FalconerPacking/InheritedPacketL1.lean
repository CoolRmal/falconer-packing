/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InheritedPacketDeletion

/-!
# The actual first-norm bound for inherited packet deletion

The source packets are the constructed dyadic annular packets. Their kernel estimates,
measurable pin sets, standard-strip containment, bad-ancestor pair coverage, and weighted
parent summation are all discharged. Only the explicit conditional parent deletion
inequality is an input to this final summation step.
-/

noncomputable section

open MeasureTheory Set Classical FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The actual deleted dyadic shell has the weighted bad-parent bound plus the proved cap
kernel tail. In particular, there is no factor counting initial pin cells or fine labels. -/
theorem exists_inherited_standard_packet_deletion_bound
    (T m : ℕ) (μ σ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hμX : μ Xᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ ‖y - x‖) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ k : ℕ,
      let s := 6 + 2 * T * k
      let N := 2 ^ s
      let hN : 0 < N := by dsimp only [N]; positivity
      ∀ (n e : ℕ → ℕ), Antitone n → ∀ (t K : ℕ) (L : ℝ), 1 ≤ L →
      ∀ (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (J : Finset ℤ)
        (w C D q : ℝ) (c d energy : ℕ → ℝ≥0∞),
      0 < w → 0 ≤ C → ((2 : ℝ) ^ n 0)⁻¹ ≤ w →
      (∀ y ∈ Y, ∀ x ∈ X, ‖x - y‖ ≤ D) →
      (∀ j < K, ∀ P ∈ I.image (ancestor (n 0 - n (j + 1))),
        σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P) ≠ 0 →
        ((normalizedRestrict σ
          (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
            (L ^ (2 * (j + 1) + 2)) P)).prod μ)
          (physicalBadPacketPairs σ n e s t K L H X j P w (C + 2) D) ≤
        c j * (∫⁻ y, ∫⁻ θ, radialProjectionDensity μ y θ ^ q ∂radialAngularMeasure
          ∂normalizedRestrict σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
            (L ^ (2 * (j + 1) + 2)) P)) + d j * energy j) →
      (∫⁻ y, ∫⁻ r, ‖complexDistanceDensity
        (deletedPacketSum ((Finset.range N) ×ˢ J)
          (inheritedPacketDeletionPins σ n e s t K L H I Y w C)
          (fun i ↦ sourceWavePacket μ hμ (𝓕 (dyadicAnnularKernel (4 * T) k))
            (hasCompactSupport_fourier_dyadicAnnularKernel (4 * T) k)
            (fourier_dyadicAnnularKernel_eventually_zero (4 * T) k)
            χ hχ N hN w i.1 i.2) y) y r‖ₑ ∂volume ∂σ) ≤
        ENNReal.ofReal C₀ *
          ((Nat.ceil ((2 * (C + 2) + 1) *
            (8 * (C + 2) * w * N / δ + 4 * Real.pi)) : ℝ≥0∞) *
            ∑ j ∈ Finset.range K, ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) *
              (c j * (∫⁻ y, ∫⁻ θ,
                radialProjectionDensity μ y θ ^ q ∂radialAngularMeasure ∂σ) +
                d j * energy j * σ univ)) +
        ENNReal.ofReal (C₁ / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * k)) * w) ^ m) *
          μ univ * (((Finset.range N) ×ˢ J).card * σ univ) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hpacket⟩ :=
    exists_standard_dyadic_packet_deletion_bound T m μ σ hμ χ hχ hχone hX hμX hδ hsep
  refine ⟨C₀, C₁, hC₀, hC₁, fun k ↦ ?_⟩
  dsimp only
  intro n e hn t K L hL H I J w C D q c d energy hw hC hscale hD hlocal
  let s := 6 + 2 * T * k
  have hcount : (2 : ℕ) ^ s = 64 * 2 ^ (2 * T * k) := by
    dsimp [s]
    rw [pow_add]
    norm_num
  let P := inheritedPacketDeletionPins σ n e s t K L H I Y w C
  have hP : ∀ i ∈ (Finset.range (64 * 2 ^ (2 * T * k))) ×ˢ J, MeasurableSet (P i) :=
    fun i _ ↦ measurableSet_inheritedPacketDeletionPins σ n e s t K L H I hY w C i
  have hPY : ∀ i ∈ (Finset.range (64 * 2 ^ (2 * T * k))) ×ˢ J, P i ⊆ Y :=
    fun _ _ ↦ inter_subset_left
  have hPT : ∀ i ∈ (Finset.range (64 * 2 ^ (2 * T * k))) ×ˢ J, P i ⊆
      packetSourceStrip (sourceWavePacketNormal (64 * 2 ^ (2 * T * k)) i.1)
        (w * i.2) ((C + 2) * w) := by
    intro i _
    rw [← hcount]
    exact inheritedPacketDeletionPins_subset_strip σ n e s t K L H I Y hscale i
  have hraw := hpacket k J w (C + 2) hw (by linarith) P hP hPY hPT
  simp only [← hcount] at hraw
  apply hraw.trans
  apply add_le_add ?_ le_rfl
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  exact prod_inheritedPacketDeletionPairs_le σ μ n e hn s t K hL H I X Y
    hscale hD J q c d energy hlocal

end FalconerPacking
