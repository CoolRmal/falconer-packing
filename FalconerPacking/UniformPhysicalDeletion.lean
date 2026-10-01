/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RegularPhysicalDeletion

/-!
# Uniform conditional deletion at the actual dyadic chain scales

One polynomial coefficient works for every finite pin and source measure, every occupied
parent, and every selected edge of a bounded chain. The spatial grid, angular mesh, and
complete geometric coefficient are constructed in the proof.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- At a threshold containing the actual conditional-energy bound, the complete pin-heavy
term is only the ratio of source and pin inflation thresholds. -/
theorem exists_uniform_physical_profile_deletion_bound
    {R δ C D : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hC : 0 ≤ C) (hD : 0 ≤ D) (K : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
        (n e : ℕ → ℕ), Antitone n → ∀ (s t : ℕ) (L : ℝ), 2 ≤ L →
      ∀ (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
        (j : ℕ) (P : Fin 2 → ℤ), j ≤ K → ∀ (w : ℝ), 0 ≤ w →
      let U := enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P
      let μ := normalizedRestrict σ U
      let ρ := ((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹
      σ U ≠ 0 → w ≤ L * ρ → ((2 : ℝ) ^ min s (e (j + 1)))⁻¹ ≤ ρ →
      (∀ᵐ y ∂μ, ‖y‖ ≤ R) → (∀ x ∈ X, ‖x‖ ≤ R) →
      (∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0) →
      (∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure) →
      ∀ (A profile F : ℝ≥0∞) (q : ℝ), A ≠ 0 → A ≠ ∞ → 1 ≤ q →
      1 ≤ profile → profile ≠ ∞ → 1 ≤ F → F ≠ ∞ →
      truncEnergy μ (dyadicRadius (n j)) (dyadicRadius (n (j + 1))) ≤ profile →
      H j = ENNReal.ofReal (c * L ^ (20 * K + 100)) * profile * F →
      (μ.prod ν) (physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
        8 * A ^ (1 - q) *
          (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) + A / F := by
  obtain ⟨c, hc, hconstant⟩ := exists_physical_deletion_constants hR hδ hC hD K
  refine ⟨c, hc, fun σ _ ν _ n e hn s t L hL H X j P hj w hw ↦ ?_⟩
  dsimp only
  intro hP hwρ hangle hμR hXR hsep hac A profile F q hA hAt hq hp hpt hF hFt henergy hH
  let Λ := 2 * L ^ (2 * (j + 1) + 2)
  let Z := Nat.ceil (4 * L ^ (4 * K + 20) + 2) + 1
  let G := 8 * R / δ ^ 2 *
    (((Z : ℝ) + 1) * Λ + 2 * (2 + C) * L + (4 * Real.pi + 1) * D)
  have hΛ : 1 ≤ Λ := by
    have : 1 ≤ L ^ (2 * (j + 1) + 2) := one_le_pow₀ (show 1 ≤ L by linarith)
    dsimp [Λ]
    linarith
  have hg : 0 < c * L ^ (20 * K + 100) := by positivity
  obtain ⟨hG, hGg, hgrid, _⟩ := hconstant L hL j hj
  change 0 < G at hG
  change G ≤ c * L ^ (20 * K + 100) at hGg
  change 20 * (2 * (Z : ℝ) + 1) ^ 2 * (12 * G) * Λ ≤
    c * L ^ (20 * K + 100) at hgrid
  have hlevels : n (j + 1) ≤ n j := hn (by omega)
  apply prod_physicalBadPacketPairs_le_profile_threshold_ae (E := L ^ (4 * K + 20))
    σ ν n e hn s t K hL H X j P hP
    (show 0 < (2 : ℕ) ^ (n j - n (j + 1)) by positivity)
    hA hAt hq (ENNReal.ofReal_pos.mpr hg).ne' ENNReal.ofReal_ne_top hp hpt hF hFt
    hG (ENNReal.ofReal_le_ofReal hGg) hH (ENNReal.ofReal Λ)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      physical_test_width_le_grid (L := L) (by linarith) K j hlevels
  · positivity
  · exact hD
  · exact hμR
  · exact hδ
  · exact hXR
  · exact hsep
  · exact hac
  · exact physical_angular_uncertainty_le (by linarith) hR.le hC hD K j s (e (j + 1))
      hlevels hwρ hangle
  · simpa only [Λ, Nat.cast_pow, Nat.cast_ofNat] using
      (truncEnergy_enlarged_dyadic_grid_le _ hlevels hΛ).trans
        (mul_le_mul' le_rfl henergy)
  · have he := ENNReal.ofReal_le_ofReal hgrid
    have hzCast : ENNReal.ofReal (2 * (Z : ℝ) + 1) = ((2 * Z + 1 : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
      simp
    simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 20),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 20 * (2 * (Z : ℝ) + 1) ^ 2),
      ENNReal.ofReal_mul
        (by positivity : (0 : ℝ) ≤ 20 * (2 * (Z : ℝ) + 1) ^ 2 * (12 * G)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12),
      ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * (Z : ℝ) + 1),
      hzCast, ENNReal.ofReal_ofNat] using he

end FalconerPacking
