/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PhysicalBadPacketPairs
public import FalconerPacking.AngularMeshChoice

/-!
# Actual conditional packet bounds with the angular grid chosen

Large conditional thresholds remove no packets. In the nontrivial small-width case the
angular mesh is constructed from the source-pair uncertainty, and its cardinality no longer
appears as an assumed choice in the deletion estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- A test with threshold at least the whole parent mass is always good. -/
theorem physicalDyadicGood_of_one_le
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (s K : ℕ)
    (L : ℝ) (H : ℕ → ℝ≥0∞) (j : ℕ) (Q : Fin 2 → ℤ) (β : ℕ ⊕ (ℕ × ℕ))
    (h : 1 ≤ H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹)) :
    physicalDyadicGood σ n e s K L H j Q β := by
  apply (measure_mono inter_subset_right).trans
  simpa only [one_mul] using mul_le_mul' h (le_refl (σ (physicalDyadicParent n L j Q)))

/-- There are no bad source packets when the conditional threshold is at least one. -/
theorem physicalBadPacketPairs_eq_empty_of_one_le
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (s t K : ℕ)
    (L : ℝ) (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (P : Fin 2 → ℤ) (w C D : ℝ)
    (h : 1 ≤ H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹)) :
    physicalBadPacketPairs σ n e s t K L H X j P w C D = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨Q, c, k, _, _, hbad, _⟩ := hz
  exact hbad (physicalDyadicGood_of_one_le σ n e s K L H j Q _ h)

/-- The actual conditional bad-pair bound uses a constructed angular mesh whose spacing is
at most twice the derived geometric uncertainty. -/
theorem prod_physicalBadPacketPairs_le_width
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 2 ≤ L)
    (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (P : Fin 2 → ℤ) {w C D R δ : ℝ}
    (hP : σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
      (L ^ (2 * (j + 1) + 2)) P) ≠ 0)
    {M : ℕ} (hM : 0 < M) {A a : ℝ≥0∞} {q E : ℝ}
    (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) (ha : a ≠ 0) (hat : a ≠ ∞) :
    let U := enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P
    let μ := normalizedRestrict σ U
    let o := gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹ P
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    let ω := 8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → ‖o‖ + b ≤ R → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ y ∈ Metric.ball o b, ∀ x ∈ X, δ ≤ (y - x) 0) →
    (∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure) →
    0 < ω → ω ≤ Real.pi →
    a = H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹) →
    (μ.prod ν) (physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) +
      20 * ((2 * Z + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        (((2 * A) * ENNReal.ofReal (6 * ω)) / a) * truncEnergy μ (b / M) b := by
  dsimp only
  intro hw hε hD hR hδ hXR hsep hac hω hωπ haeq
  obtain ⟨N, hN, hmesh₀, hmesh₁⟩ := exists_angular_grid_for_width hω hωπ
  have hbnd := prod_physicalBadPacketPairs_le σ ν n e hn s t K hL H X j P hP
    hM hN hA hAt hq ha hat hw hε hD hR hδ hXR hsep hac hmesh₀ haeq
  apply hbnd.trans
  apply add_le_add le_rfl
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  exact ENNReal.ofReal_le_ofReal (by linarith [hmesh₁])

end FalconerPacking
