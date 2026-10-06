/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.InheritedPacketL1
public import FalconerPacking.UniformPhysicalDeletion

/-!
# Uniform inherited deletion with actual local physical thresholds

The cap constants are chosen before the pin measure. The local deletion estimate is then
obtained from the constructed physical threshold and its actual conditional-energy bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The actual deleted dyadic shell has the weighted bad-parent bound plus the proved cap
kernel tail. In particular, there is no factor counting initial pin cells or fine labels. -/
theorem exists_pin_uniform_inherited_packet_deletion_bound
    (T m : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hμX : μ Xᶜ = 0)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ ‖y - x‖) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ], ∀ k : ℕ,
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
  obtain ⟨C₀, C₁, hC₀, hC₁, hkernel⟩ := exists_uniform_standardCapKernel_bounds T m
  refine ⟨C₀, C₁, hC₀, hC₁, fun σ _ k ↦ ?_⟩
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
  have hraw := lintegral_enorm_deleted_sourceWavePackets_le μ σ hμ
    (𝓕 (dyadicAnnularKernel (4 * T) k))
    (hasCompactSupport_fourier_dyadicAnnularKernel (4 * T) k)
    (fourier_dyadicAnnularKernel_eventually_zero (4 * T) k)
    χ hχ hχone hX hμX (by positivity : 0 < 64 * 2 ^ (2 * T * k)) J hw
    (show 2 ≤ C + 2 by linarith) hδ hsep P hP hPY hPT
    (fun j _ ↦ (hkernel k j).1) (fun j _ ↦ (hkernel k j).2 w hw)
  simp only [← hcount] at hraw
  apply hraw.trans
  apply add_le_add ?_ le_rfl
  apply mul_le_mul' le_rfl
  apply mul_le_mul' le_rfl
  exact prod_inheritedPacketDeletionPairs_le σ μ n e hn s t K hL H I X Y
    hscale hD J q c d energy hlocal


/-- The inherited deleted shell is bounded using the actual local physical theorem. No
conditional bad-pair inequality is assumed. The only component-dependent analytic input is
its literal truncated energy, which regularity bounds by the profile factor. -/
theorem exists_uniform_inherited_profile_deletion_bound
    (T m K : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hμX : μ Xᶜ = 0)
    (hXR : ∀ x ∈ X, ‖x‖ ≤ R) (hYR : ∀ y ∈ Y, ‖y‖ ≤ R)
    (hsep : ∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0) :
    ∃ c C₀ C₁ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ],
      σ Yᶜ = 0 → (∀ᵐ y ∂σ, μ.map (radialAngle y) ≪ radialAngularMeasure) →
      ∀ k : ℕ,
      let s := 6 + 2 * T * k
      let N := 2 ^ s
      let hN : 0 < N := by dsimp only [N]; positivity
      ∀ (n e : ℕ → ℕ), Antitone n → ∀ (t : ℕ) (L : ℝ), 2 ≤ L →
      ∀ (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (J : Finset ℤ)
        (w q : ℝ) (A F : ℝ≥0∞) (profile : ℕ → ℝ≥0∞),
      0 < w → ((2 : ℝ) ^ n 0)⁻¹ ≤ w →
      A ≠ 0 → A ≠ ∞ → 1 ≤ q → 1 ≤ F → F ≠ ∞ →
      (∀ j < K, 1 ≤ profile j ∧ profile j ≠ ∞) →
      (∀ j < K, w ≤ L * (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹)) →
      (∀ j < K, ((2 : ℝ) ^ min s (e (j + 1)))⁻¹ ≤
        ((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹) →
      (∀ j < K, H j = ENNReal.ofReal (c * L ^ (20 * K + 100)) * profile j * F) →
      (∀ j < K, ∀ P ∈ I.image (ancestor (n 0 - n (j + 1))),
        let U := enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
          (L ^ (2 * (j + 1) + 2)) P
        σ U ≠ 0 → truncEnergy (normalizedRestrict σ U)
          (dyadicRadius (n j)) (dyadicRadius (n (j + 1))) ≤ profile j) →
      (∫⁻ y, ∫⁻ r, ‖complexDistanceDensity
        (deletedPacketSum ((Finset.range N) ×ˢ J)
          (inheritedPacketDeletionPins σ n e s t K L H I Y w 4)
          (fun i ↦ sourceWavePacket μ hμ (𝓕 (dyadicAnnularKernel (4 * T) k))
            (hasCompactSupport_fourier_dyadicAnnularKernel (4 * T) k)
            (fourier_dyadicAnnularKernel_eventually_zero (4 * T) k)
            χ hχ N hN w i.1 i.2) y) y r‖ₑ ∂volume ∂σ) ≤
        ENNReal.ofReal C₀ *
          ((Nat.ceil (13 * (48 * w * N / δ + 4 * Real.pi)) : ℝ≥0∞) *
            ∑ j ∈ Finset.range K, ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) *
              (8 * A ^ (1 - q) * (∫⁻ y, ∫⁻ θ,
                radialProjectionDensity μ y θ ^ q ∂radialAngularMeasure ∂σ) +
                A / F * σ univ)) +
        ENNReal.ofReal (C₁ / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * k)) * w) ^ m) *
          μ univ * (((Finset.range N) ×ˢ J).card * σ univ) := by
  obtain ⟨c, hc, hlocal⟩ := exists_uniform_physical_profile_deletion_bound
    hR hδ (by norm_num : (0 : ℝ) ≤ 6) (by positivity : 0 ≤ 2 * R) K
  have hsep' : ∀ x ∈ X, ∀ y ∈ Y, δ ≤ ‖y - x‖ := by
    intro x hx y hy
    exact (hsep y hy x hx).trans ((le_abs_self _).trans (PiLp.norm_apply_le (y - x) 0))
  obtain ⟨C₀, C₁, hC₀, hC₁, hpacket⟩ :=
    exists_pin_uniform_inherited_packet_deletion_bound T m μ hμ χ hχ hχone hX hY hμX
      hδ hsep'
  refine ⟨c, C₀, C₁, hc, hC₀, hC₁, fun σ _ hσY hac k ↦ ?_⟩
  dsimp only
  intro n e hn t L hL H I J w q A F profile hw hscale hA hAt hq hF hFt hp hwρ ha hH he
  have hbound := hpacket σ k n e hn t K L (by linarith) H I J w 4 (2 * R) q
    (fun _ ↦ 8 * A ^ (1 - q)) (fun _ ↦ A / F) (fun _ ↦ 1) hw (by norm_num) hscale
    (fun y hy x hx ↦ (norm_sub_le _ _).trans (by linarith [hXR x hx, hYR y hy])) ?_
  · simpa only [show (2 * ((4 : ℝ) + 2) + 1) = 13 by norm_num,
      show (8 : ℝ) * (4 + 2) = 48 by norm_num, mul_one] using hbound
  · intro j hj P hPI hP
    obtain ⟨hpinR, hpinsep, hpinac⟩ := normalizedRestrict_ae_pin_geometry σ μ
      (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
        (L ^ (2 * (j + 1) + 2)) P) X Y hσY hYR hsep hac
    simpa only [mul_one, show (4 : ℝ) + 2 = 6 by norm_num] using
      hlocal σ μ n e hn (6 + 2 * T * k) t L hL H X
      j P hj.le w hw.le hP (hwρ j hj) (ha j hj) hpinR hXR hpinsep hpinac
      A (profile j) F q hA hAt hq (hp j hj).1 (hp j hj).2 hF hFt
      (he j hj P hPI hP) (hH j hj)

end FalconerPacking
