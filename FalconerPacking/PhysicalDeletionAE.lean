/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.TubeDeletionAE
public import FalconerPacking.PhysicalConditionalDeletion

/-!
# Conditional physical deletion on the actual separated pin support

The parent ball can grow with the inflation parameters and need not be separated from the
source. Norm and coordinate separation are required only almost everywhere for its normalized
pin measure. The angular mesh, exact spatial ratio cancellation, and constants are unchanged.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Conditional bad-packet mass is bounded by the actual finite-grid energy, independently
of the number of packet labels and child cubes. -/
theorem prod_physicalBadPacketPairs_le_ae
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 2 ≤ L)
    (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (P : Fin 2 → ℤ) {w C D R δ : ℝ}
    (hP : σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
      (L ^ (2 * (j + 1) + 2)) P) ≠ 0)
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) {A a : ℝ≥0∞} {q E : ℝ}
    (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) (ha : a ≠ 0) (hat : a ≠ ∞) :
    let U := enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P
    let μ := normalizedRestrict σ U
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → (∀ᵐ y ∂μ, ‖y‖ ≤ R) → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0) →
    (∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure) →
    8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2 ≤ 2 * Real.pi / N →
    a = H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹) →
    (μ.prod ν) (physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) +
      20 * ((2 * Z + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        (((2 * A) * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
          truncEnergy μ (b / M) b := by
  dsimp only
  intro hw hε hD hR hδ hXR hsep hac hwidth haeq
  have hb : 0 < 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹ := by
    have hL₀ : 0 < L := by linarith
    positivity
  have hbnd := prod_all_direction_heavy_tubes_le_ae
    (normalizedRestrict σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
      (L ^ (2 * (j + 1) + 2)) P)) ν
    (gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹ P)
    (fun i : (Fin 2 → ℤ) × ℕ ↦ gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ i.1)
    (fun i ↦ packetEffectiveNormal s (e (j + 1)) i.2)
    (fun _ ↦ L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2)
    (fun i ↦ norm_packetEffectiveNormal _ _ _) hb hM (fun _ ↦ hw) hε hD hR hδ
    hXR hsep hac hN hwidth hA hAt hq ha hat
  apply le_trans (measure_mono ?_) hbnd
  apply Subset.trans
    (physicalBadPacketPairs_subset_heavy_family σ n e hn s t K hL H X j P w C D hP)
  rw [haeq]
  exact subset_union_right


/-- The actual conditional bad-pair bound uses a constructed angular mesh whose spacing is
at most twice the derived geometric uncertainty. -/
theorem prod_physicalBadPacketPairs_le_width_ae
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
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    let ω := 8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → (∀ᵐ y ∂μ, ‖y‖ ≤ R) → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0) →
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
  have hbnd := prod_physicalBadPacketPairs_le_ae σ ν n e hn s t K hL H X j P hP
    hM hN hA hAt hq ha hat hw hε hD hR hδ hXR hsep hac hmesh₀ haeq
  apply hbnd.trans
  apply add_le_add le_rfl
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  apply ENNReal.div_le_div_right
  apply mul_le_mul' le_rfl
  exact ENNReal.ofReal_le_ofReal (by linarith [hmesh₁])


/-- The actual conditional bad-packet estimate with its pin-threshold ratio made explicit. -/
theorem prod_physicalBadPacketPairs_le_threshold_ae
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
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let ρ := ((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    let ω := 8 * R * (((Z : ℝ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → (∀ᵐ y ∂μ, ‖y‖ ≤ R) → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0) →
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
  have hbnd := prod_physicalBadPacketPairs_le_ae σ ν n e hn s t K hL H X j P hP
    hM hN hA hAt hq ha hat hw hε hD hR hδ hXR hsep hac (hω.trans hmesh₀) rfl
  apply hbnd.trans
  apply add_le_add le_rfl
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact angular_source_mass_div_threshold_le hρ hG.le hmesh₁ A (H j)


/-- Every almost-everywhere property of the original pin measure survives normalization
on an arbitrary parent, including a parent of zero mass. -/
theorem ae_normalizedRestrict_of_ae
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (U : Set (EuclideanSpace ℝ (Fin 2)))
    {p : EuclideanSpace ℝ (Fin 2) → Prop} (hp : ∀ᵐ y ∂σ, p y) :
    ∀ᵐ y ∂normalizedRestrict σ U, p y :=
  Measure.ae_smul_measure (ae_restrict_of_ae hp) _

/-- A fixed bounded separated pin support supplies all geometric assumptions uniformly for
its normalized enlarged parents; the enlarged parent need not itself be separated. -/
theorem normalizedRestrict_ae_pin_geometry
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2)))
    (U X Y : Set (EuclideanSpace ℝ (Fin 2))) {R δ : ℝ}
    (hY : σ Yᶜ = 0) (hYR : ∀ y ∈ Y, ‖y‖ ≤ R)
    (hsep : ∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0)
    (hac : ∀ᵐ y ∂σ, ν.map (radialAngle y) ≪ radialAngularMeasure) :
    (∀ᵐ y ∂normalizedRestrict σ U, ‖y‖ ≤ R) ∧
      (∀ᵐ y ∂normalizedRestrict σ U, ∀ x ∈ X, δ ≤ (y - x) 0) ∧
      (∀ᵐ y ∂normalizedRestrict σ U, ν.map (radialAngle y) ≪ radialAngularMeasure) := by
  have hmem : ∀ᵐ y ∂normalizedRestrict σ U, y ∈ Y :=
    ae_normalizedRestrict_of_ae σ U (ae_iff.mpr hY)
  exact ⟨hmem.mono fun y hy ↦ hYR y hy,
    hmem.mono fun y hy ↦ hsep y hy, ae_normalizedRestrict_of_ae σ U hac⟩

end FalconerPacking
