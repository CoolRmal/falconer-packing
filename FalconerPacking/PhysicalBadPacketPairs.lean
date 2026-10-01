/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PhysicalMarkedPairs

/-!
# Coarsening the actual removed packet pairs in one parent

All child cubes, standard cap labels, and strip indices are included in one literal pair
set. Their bad physical tests put this entire set in the single heavy-tube family used by
the finite-grid deletion bound. No count of source caps or child cubes is incurred here.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The actual pairs from bad standard packets at one selected parent and one chain edge. -/
def physicalBadPacketPairs (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n e : ℕ → ℕ) (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (X : Set (EuclideanSpace ℝ (Fin 2))) (j : ℕ) (P : Fin 2 → ℤ) (w C D : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  {z | ∃ (Q : Fin 2 → ℤ) (c : ℕ) (k : ℤ),
    ancestor (n j - n (j + 1)) Q = P ∧ c < 2 ^ s ∧
    ¬ physicalDyadicGood σ n e s K L H j Q
      (dyadicCapAncestor s t (e (j + 1)) (c, 0)) ∧
    z.1 ∈ dyadicCube (n j) Q ∧ z.2 ∈ X ∧
    z.2 ∈ packetSourceStrip (sourceWavePacketNormal (2 ^ s) c) (w * k) (2 * w) ∧
    z.1 ∈ packetSourceStrip (sourceWavePacketNormal (2 ^ s) c) (w * k) (C * w) ∧
    ‖z.2 - z.1‖ ≤ D}

/-- The entire actual bad-packet pair set is contained in one arbitrary-direction heavy
family for the same normalized enlarged parent. -/
theorem physicalBadPacketPairs_subset_heavy_family
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 2 ≤ L)
    (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (P : Fin 2 → ℤ) (w C D : ℝ)
    (hP : σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
      (L ^ (2 * (j + 1) + 2)) P) ≠ 0) :
    physicalBadPacketPairs σ n e s t K L H X j P w C D ⊆
      ⋃ i : (Fin 2 → ℤ) × ℕ,
        heavyTestedTubePairs
          (normalizedRestrict σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
            (L ^ (2 * (j + 1) + 2)) P)) X
          (gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹ P)
          (gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ i.1)
          (packetEffectiveNormal s (e (j + 1)) i.2)
          (2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹)
          (L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2)
          (2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D) D
          (H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹)) := by
  rintro ⟨y, x⟩ ⟨Q, c, k, hparent, _, hbad, hy, hx, hxs, hys, hD⟩
  have hp : physicalDyadicParent n L j Q =
      enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P := by
    simp only [physicalDyadicParent, hparent]
  have hQ : σ (physicalDyadicParent n L j Q) ≠ 0 := hp ▸ hP
  have h := bad_physical_mark_pair_mem σ n e hn s t K hL H j Q c hQ hbad
    hx hy hxs hys hD
  rw [hp, hparent] at h
  exact mem_iUnion.mpr ⟨(Q, c), h⟩

/-- Conditional bad-packet mass is bounded by the actual finite-grid energy, independently
of the number of packet labels and child cubes. -/
theorem prod_physicalBadPacketPairs_le
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
    let o := gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹ P
    let b := 2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹
    let width := L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2
    let ε := 2 * w + C * w + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D
    let Z := Nat.ceil (4 * E + 2) + 1
    width ≤ E * (b / M) → 0 ≤ ε → 0 ≤ D → ‖o‖ + b ≤ R → 0 < δ →
    (∀ x ∈ X, ‖x‖ ≤ R) →
    (∀ y ∈ Metric.ball o b, ∀ x ∈ X, δ ≤ (y - x) 0) →
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
  have hbnd := prod_all_direction_heavy_tubes_le
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

end FalconerPacking
