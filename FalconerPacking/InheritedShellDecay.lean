/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicDeletionDecay

/-!
# Actual inherited deleted shells decay at every annulus

The shell frequency is indexed by every natural number. Its packet integer and the larger
regularization enlargement block are independent. The only measure-dependent coefficient is
the actual radial density moment, allowing subsequent weighted component summation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Actual deleted-shell decay with the radial moment displayed explicitly. In particular,
no component-independent upper bound on conditional radial moments is assumed. -/
theorem exists_inherited_deleted_shell_decay
    {T B : ℕ} (hT : 0 < T) (hB : 0 < B) (K : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ R)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    {X Y : Set (EuclideanSpace ℝ (Fin 2))}
    (hX : MeasurableSet X) (hY : MeasurableSet Y) (hμX : μ Xᶜ = 0)
    (hXR : ∀ x ∈ X, ‖x‖ ≤ R) (hYR : ∀ y ∈ Y, ‖y‖ ≤ R)
    (hsep : ∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0) :
    ∃ c C₀ C₁ : ℝ, 0 < c ∧ 0 < C₀ ∧ 0 < C₁ ∧
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure σ],
      σ Yᶜ = 0 → (∀ᵐ y ∂σ, μ.map (radialAngle y) ≪ radialAngularMeasure) →
      ∀ k : ℕ, 1 ≤ k →
      let s := 6 + 2 * T * k
      let N : ℕ := 2 ^ s
      let hN : 0 < N := by dsimp only [N]; positivity
      let x := (2 : ℝ) ^ k
      let L := x ^ B
      let w := x / x ^ (2 * T)
      let J := sourceWavePacketIndices χ hχ w
      ∀ (n e : ℕ → ℕ), Antitone n → ∀ (t : ℕ) (H : ℕ → ℝ≥0∞)
        (I : Finset (Fin 2 → ℤ)) (q D₁ D₂ : ℝ) (profile : ℕ → ℝ≥0∞),
      let F := (ENNReal.ofReal L) ^ D₂
      1 ≤ q → 0 ≤ D₂ →
      (4 * K + 9 : ℝ) - (q - 1) * D₁ ≤ -1 →
      (4 * K + 9 : ℝ) + D₁ - D₂ ≤ -1 →
      ((2 : ℝ) ^ n 0)⁻¹ ≤ w →
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
        (ENNReal.ofReal (C₀ * (13 * (3072 / δ + 4 * Real.pi) + 1) * 49 * K) *
          (8 * (∫⁻ y, ∫⁻ θ,
            radialProjectionDensity μ y θ ^ q ∂radialAngularMeasure ∂σ) + 1) +
          ENNReal.ofReal (C₁ * 64 * (2 * sourceCutoffRadius χ hχ + 3))) *
          (2 : ℝ≥0∞) ^ (-(k : ℝ)) := by
  obtain ⟨c, C₀, C₁, hc, hC₀, hC₁, hbound⟩ :=
    exists_uniform_inherited_profile_deletion_bound T (4 * T + 1) K μ hR hδ hμ χ hχ
      hχone hX hY hμX hXR hYR hsep
  refine ⟨c, C₀, C₁, hc, hC₀, hC₁, fun σ _ hσY hac k hk ↦ ?_⟩
  dsimp only
  intro n e hn t H I q D₁ D₂ profile hq hD₂ hsource hpin hscale hp hwρ ha hH he
  let x := (2 : ℝ) ^ k
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hxB : x ≤ x ^ B := by
    simpa only [pow_one] using pow_le_pow_right₀ hx (by omega : 1 ≤ B)
  have hL : 2 ≤ x ^ B := by
    apply le_trans _ hxB
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hLe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (x ^ B) := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ x ^ B by linarith)
  have hA : (ENNReal.ofReal (x ^ B)) ^ D₁ ≠ 0 :=
    (ENNReal.rpow_pos (zero_lt_one.trans_le hLe) ENNReal.ofReal_ne_top).ne'
  have hAt : (ENNReal.ofReal (x ^ B)) ^ D₁ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (zero_lt_one.trans_le hLe))
      ENNReal.ofReal_ne_top
  have hF : 1 ≤ (ENNReal.ofReal (x ^ B)) ^ D₂ := by
    simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_le hLe hD₂
  have hFt : (ENNReal.ofReal (x ^ B)) ^ D₂ ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (zero_lt_one.trans_le hLe))
      ENNReal.ofReal_ne_top
  have hactual := hbound σ hσY hac k n e hn t (x ^ B) hL H I
    (sourceWavePacketIndices χ hχ (x / x ^ (2 * T))) (x / x ^ (2 * T)) q
    ((ENNReal.ofReal (x ^ B)) ^ D₁) ((ENNReal.ofReal (x ^ B)) ^ D₂) profile
    (by positivity) hscale hA hAt hq hF hFt hp hwρ ha hH he
  simp only [measure_univ, mul_one] at hactual
  exact hactual.trans
    (dyadic_inherited_deletion_rhs_le χ hχ hT hB K k hδ hC₀.le hC₁.le hsource hpin _)

end FalconerPacking
