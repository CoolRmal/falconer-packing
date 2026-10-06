/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PhysicalBadPacketBounds
public import FalconerPacking.ConditionalAngularThreshold

/-!
# Conditional deletion for the actual physical marks

The auxiliary angular grid is constructed internally. If the pin threshold is at least one,
there are no bad packets. Otherwise its lower bound by the geometric factor guarantees the
required small angular width, and the spatial scale ratio cancels from the estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- The actual conditional bad-packet estimate with its pin-threshold ratio made explicit. -/
theorem prod_physicalBadPacketPairs_le_threshold
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 2 ≤ L)
    (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (P : Fin 2 → ℤ) {w C D R δ : ℝ}
    (hP : σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
      (L ^ (2 * (j + 1) + 2)) P) ≠ 0)
    {M : ℕ} (hM : 0 < M) {A : ℝ≥0∞} {q E G : ℝ}
    (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q)
    (hG : 0 < G) (hHG : ENNReal.ofReal G ≤ H j) (hHt : H j ≠ ∞) :
    let U := enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P
    let μ := normalizedRestrict σ U
    let o := gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹ P
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let ρ := ((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    let ω := 8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → ‖o‖ + b ≤ R → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ y ∈ Metric.ball o b, ∀ x ∈ X, δ ≤ (y - x) 0) →
    (∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure) → ω ≤ G * ρ →
    (μ.prod ν) (physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) +
      20 * ((2 * Z + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        (12 * ENNReal.ofReal G * (A / H j)) * truncEnergy μ (b / M) b := by
  dsimp only
  intro hw hε hD hR hδ hXR hsep hac hω
  let ρ := ((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  by_cases hbig : 1 ≤ H j * ENNReal.ofReal ρ
  · rw [physicalBadPacketPairs_eq_empty_of_one_le σ n e s t K L H X j P w C D hbig,
      measure_empty]
    exact zero_le
  have hsmall : H j * ENNReal.ofReal ρ < 1 := lt_of_not_ge hbig
  obtain ⟨N, hN, hmesh₀, hmesh₁⟩ :=
    exists_angular_grid_below_conditional_threshold hρ hG hHG hsmall
  have hH : H j ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr hG).trans_le hHG)
  have ha : H j * ENNReal.ofReal ρ ≠ 0 :=
    mul_ne_zero hH (ENNReal.ofReal_pos.mpr hρ).ne'
  have hat : H j * ENNReal.ofReal ρ ≠ ∞ :=
    ENNReal.mul_ne_top hHt ENNReal.ofReal_ne_top
  have hbnd := prod_physicalBadPacketPairs_le σ ν n e hn s t K hL H X j P hP
    hM hN hA hAt hq ha hat hw hε hD hR hδ hXR hsep hac (hω.trans hmesh₀) rfl
  apply hbnd.trans
  apply add_le_add le_rfl
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact angular_source_mass_div_threshold_le hρ hG.le hmesh₁ A (H j)

end FalconerPacking
