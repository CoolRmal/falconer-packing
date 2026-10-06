/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PhysicalDeletionAE
public import FalconerPacking.PhysicalDeletionConstants

/-!
# Cancelling the actual conditional profile energy in the physical threshold

The pin threshold includes the regular conditional-energy bound and the complete finite-grid
coefficient. Their cancellation leaves only the ratio of the source and pin inflation thresholds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Positive finite profile factors cancel exactly, without a bound on their magnitudes. -/
theorem profile_threshold_cancellation {c g energy A F : ℝ≥0∞}
    (hcg : c ≤ g) (hg : g ≠ 0) (hgt : g ≠ ∞)
    (he : energy ≠ 0) (het : energy ≠ ∞) :
    c * (A / (g * energy * F)) * energy ≤ A / F := by
  calc
    _ ≤ g * (A / (g * energy * F)) * energy := by gcongr
    _ = (g * energy) * A / ((g * energy) * F) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := ENNReal.mul_div_mul_left A F (mul_ne_zero hg he) (ENNReal.mul_ne_top hgt het)

/-- The actual conditional bad-pair estimate after placing the complete profile-energy
factor in its physical pin threshold. Geometry is imposed only at measured pins. -/
theorem prod_physicalBadPacketPairs_le_profile_threshold_ae
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 2 ≤ L)
    (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (P : Fin 2 → ℤ) {w C D R δ : ℝ}
    (hP : σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
      (L ^ (2 * (j + 1) + 2)) P) ≠ 0)
    {M : ℕ} (hM : 0 < M) {A g profile F : ℝ≥0∞} {q E G : ℝ}
    (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q)
    (hg : g ≠ 0) (hgt : g ≠ ∞) (hp : 1 ≤ profile) (hpt : profile ≠ ∞)
    (hF : 1 ≤ F) (hFt : F ≠ ∞)
    (hG : 0 < G) (hGg : ENNReal.ofReal G ≤ g) (hH : H j = g * profile * F) :
    let U := enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P
    let μ := normalizedRestrict σ U
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let ρ := ((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    ∀ Λ : ℝ≥0∞,
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → (∀ᵐ y ∂μ, ‖y‖ ≤ R) → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0) →
    (∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure) →
    8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2 ≤ G * ρ →
    truncEnergy μ (b / M) b ≤ Λ * profile →
    20 * ((2 * Z + 1 : ℕ) : ℝ≥0∞) ^ 2 * (12 * ENNReal.ofReal G) * Λ ≤ g →
    (μ.prod ν) (physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) + A / F := by
  dsimp only
  intro Λ hw hε hD hR hδ hXR hsep hac hω henergy hconstant
  have hHG : ENNReal.ofReal G ≤ H j := by
    rw [hH]
    calc
      _ ≤ g := hGg
      _ = g * 1 * 1 := by simp
      _ ≤ _ := by gcongr
  have hHt : H j ≠ ∞ := by rw [hH]; exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hgt hpt) hFt
  have hbnd := prod_physicalBadPacketPairs_le_threshold_ae σ ν n e hn s t K hL H X j P hP
    hM hA hAt hq hG hHG hHt hw hε hD hR hδ hXR hsep hac hω
  apply hbnd.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (20 * ((2 * (Nat.ceil (4 * E + 2) + 1) + 1 : ℕ) : ℝ≥0∞) ^ 2) *
        (12 * ENNReal.ofReal G * (A / H j)) * (Λ * profile) :=
      mul_le_mul' le_rfl henergy
    _ = (20 * ((2 * (Nat.ceil (4 * E + 2) + 1) + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        (12 * ENNReal.ofReal G) * Λ) * (A / (g * profile * F)) * profile := by
      rw [hH]
      ring
    _ ≤ _ := profile_threshold_cancellation hconstant hg hgt
      (ne_of_gt (zero_lt_one.trans_le hp)) hpt

/-- The literal dyadic slope grid has the proved regular-profile energy at its exact scales. -/
theorem normalized_regular_dyadic_grid_energy_le_edgeCost
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} (hT : 0 < T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (he : ∀ j < L, e j ≤ 2 * T)
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ L)
    {q : Fin 2 → ℤ}
    (hq : 0 < normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * m) q))
    {X : Set (EuclideanSpace ℝ (Fin 2))} (hXm : MeasurableSet X)
    (hX : dyadicCube (T * m) q ⊆ X) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    truncEnergy (normalizedRestrict (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) X)
        ((Λ * ((2 : ℝ) ^ (T * m))⁻¹) / ((2 : ℕ) ^ (T * n - T * m) : ℝ))
        (Λ * ((2 : ℝ) ^ (T * m))⁻¹) ≤
      ENNReal.ofReal Λ *
        (4 * (n + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
          (3 * (L : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T L e) m n)) := by
  apply (truncEnergy_enlarged_dyadic_grid_le _ (Nat.mul_le_mul_left T hmn) hΛ).trans
  exact mul_le_mul' le_rfl
    (normalized_regular_conditional_energy_le_edgeCost μ hT he hA hreg hroot
      hmn hn hq hXm hX)

/-- The actual regular-profile energy factor is finite and at least one, as required in
physical threshold selection and exact cancellation. -/
theorem regular_profile_energy_one_le_and_ne_top {T L m n : ℕ} (hT : 0 < T)
    (e : ℕ → ℕ) (hmn : m ≤ n) :
    let profile := 4 * (n + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
      (3 * (L : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T L e) m n)
    1 ≤ profile ∧ profile ≠ ∞ := by
  dsimp only
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hcost : 0 ≤ edgeCost (regularBlockProfile T L e) m n := edgeCost_nonneg hmn
  have hexp : 0 < 3 * (L : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T L e) m n := by
    positivity
  constructor
  · calc
      (1 : ℝ≥0∞) = 1 * 1 * 1 := by simp
      _ ≤ _ := mul_le_mul'
        (mul_le_mul' (by norm_num) (by simp)) (ENNReal.one_le_rpow (by norm_num) hexp)
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp))
      (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))

end FalconerPacking
