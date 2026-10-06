/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourceTubeMassAE
public import FalconerPacking.AllDirectionTubeDeletion

/-!
# Finite-grid and arbitrary-direction deletion with almost-everywhere pin geometry

The tested geometric tubes and their finite-grid energy are unchanged. Only pins carrying
the conditional measure must lie in the fixed bounded, separated pin set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Actual finite source and pin tubes obey the joint deletion estimate, including all
source mass and finite-grid enlargement costs. -/
theorem prod_all_heavy_enlargedSlopeTubes_le_ae
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (o : EuclideanSpace ℝ (Fin 2)) {X : Set (EuclideanSpace ℝ (Fin 2))}
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) (L : ℕ)
    {R w δ : ℝ} (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) (hw : (L + 1) * (b / M) ≤ w)
    (hδ : 0 < δ) (hXR : ∀ x ∈ X, ‖x‖ ≤ R)
    (hsep : ∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0)
    (hac : ∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure)
    {N : ℕ} (hN : 0 < N) (hwidth : 8 * R * w / δ ^ 2 ≤ 2 * Real.pi / N)
    {A a : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q)
    (ha : a ≠ 0) (hat : a ≠ ∞) :
    (μ.prod ν)
      (radialHeavyCellPairs ν (Finset.range N) (enlargedAngularCell N) (2 * A) ∪
        ⋃ i ∈ (slopeTubeLabels M).filter (fun i ↦ a < μ (enlargedSlopeTube o b M L i)),
          enlargedSlopeTube o b M L i ×ˢ sourceSlopeTube X o b w M i) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) +
      20 * ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        (((2 * A) * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
          truncEnergy μ (b / M) b := by
  have hw₀ : 0 ≤ w := (by positivity : 0 ≤ (L + 1 : ℝ) * (b / M)).trans hw
  have hsep' : ∀ᵐ y ∂μ, ∀ i ∈ slopeTubeLabels M,
      ∀ x ∈ sourceSlopeTube X o b w M i, δ ≤ (y - x) 0 := by
    filter_upwards [hsep] with y hy
    exact fun _ _ x hx ↦ hy x hx.1
  have h := prod_all_heavy_tubes_of_common_strips_ae μ ν (slopeTubeLabels M)
    (enlargedSlopeTube o b M L) (sourceSlopeTube X o b w M)
    (fun i ↦ slopeUnitNormal i.1 ((i.2.1 : ℝ) / M)) (slopeTubeCenter o b M)
    (fun i _ ↦ norm_slopeUnitNormal _ _) hw₀ hδ hR
    (fun i _ x hx ↦ hXR x hx.1)
    hsep'
    (fun i _ y hy ↦ (enlargedSlopeTube_unit_normal_bound hb hM hy).trans hw)
    (fun i _ x hx ↦ hx.2) hac hN hwidth hA hAt hq ha hat
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (((2 * A) * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
        (20 * ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 * truncEnergy μ (b / M) b) :=
      mul_le_mul' le_rfl (sum_measure_enlargedSlopeTube_sq_le_truncEnergy μ o hb hM L)
    _ = _ := by ring


/-- The entire arbitrary family has the same actual deletion estimate as the finite grid. -/
theorem prod_all_direction_heavy_tubes_le_ae {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (o : EuclideanSpace ℝ (Fin 2)) {X : Set (EuclideanSpace ℝ (Fin 2))}
    (p e : ι → EuclideanSpace ℝ (Fin 2)) (w : ι → ℝ) (he : ∀ t, ‖e t‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) {C ε D R δ : ℝ}
    (hw : ∀ t, w t ≤ C * (b / M)) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hR : ∀ᵐ y ∂μ, ‖y‖ ≤ R) (hδ : 0 < δ) (hXR : ∀ x ∈ X, ‖x‖ ≤ R)
    (hsep : ∀ᵐ y ∂μ, ∀ x ∈ X, δ ≤ (y - x) 0)
    (hac : ∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure)
    {N : ℕ} (hN : 0 < N)
    (hwidth : 8 * R *
      (((Nat.ceil (4 * C + 2) + 1 : ℕ) + 1) * (b / M) + 2 * ε + D / M) / δ ^ 2 ≤
        2 * Real.pi / N)
    {A a : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q)
    (ha : a ≠ 0) (hat : a ≠ ∞) :
    let L := Nat.ceil (4 * C + 2) + 1
    (μ.prod ν) (radialHeavyCellPairs ν (Finset.range N) (enlargedAngularCell N) (2 * A) ∪
      ⋃ t, heavyTestedTubePairs μ X o (p t) (e t) b (w t) ε D a) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) +
      20 * ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        (((2 * A) * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
          truncEnergy μ (b / M) b := by
  dsimp only
  apply (measure_mono (union_subset_union_right _
    (union_heavyTestedTubePairs_subset_finite_grid μ X o p e w he hb hM hw a))).trans
  apply prod_all_heavy_enlargedSlopeTubes_le_ae μ ν o hb hM (Nat.ceil (4 * C + 2) + 1)
    hR (by
      have ht : 0 ≤ D / (M : ℝ) := by positivity
      linarith)
    hδ hXR hsep hac hN _ hA hAt hq ha hat
  simpa only [Nat.cast_add, Nat.cast_one] using hwidth


end FalconerPacking
