/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SlopeTubeSourceCoverage

/-!
# Coarsening every tested direction without a label-count loss

An arbitrary family of heavy physical tubes and its associated source pairs is contained
in the one concrete finite-grid heavy-tube union. Its index set may even be infinite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Pairs associated with an actual heavy unit-normal strip inside a parent ball. -/
def heavyTestedTubePairs (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (X : Set (EuclideanSpace ℝ (Fin 2))) (o p e : EuclideanSpace ℝ (Fin 2))
    (b w ε D : ℝ) (a : ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  {z | z.1 ∈ Metric.ball o b ∩ {y | |⟪e, y - p⟫| ≤ w} ∧ z.2 ∈ X ∧
    |⟪e, z.2 - z.1⟫| ≤ ε ∧ ‖z.2 - z.1‖ ≤ D ∧
    a < μ (Metric.ball o b ∩ {y | |⟪e, y - p⟫| ≤ w})}

/-- Every fine tested label is covered by the same finite heavy-tube family. -/
theorem union_heavyTestedTubePairs_subset_finite_grid {ι : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (o : EuclideanSpace ℝ (Fin 2)) (p e : ι → EuclideanSpace ℝ (Fin 2))
    (w : ι → ℝ) (he : ∀ t, ‖e t‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) {C ε D : ℝ}
    (hw : ∀ t, w t ≤ C * (b / M)) (a : ℝ≥0∞) :
    let L := Nat.ceil (4 * C + 2) + 1
    (⋃ t, heavyTestedTubePairs μ X o (p t) (e t) b (w t) ε D a) ⊆
      ⋃ i ∈ (slopeTubeLabels M).filter (fun i ↦ a < μ (enlargedSlopeTube o b M L i)),
        enlargedSlopeTube o b M L i ×ˢ
          sourceSlopeTube X o b ((L + 1) * (b / M) + 2 * ε + D / M) M i := by
  dsimp only
  rintro ⟨y, x⟩ hz
  obtain ⟨t, hy, hx, hangle, hnorm, hheavy⟩ := mem_iUnion.mp hz
  obtain ⟨i, hi, hpin, hsource⟩ := exists_slopeTube_cover_with_source_pairs X o
    (p t) (e t) (he t) hb hM (hw t) ⟨y, hy⟩
  exact mem_iUnion₂.mpr ⟨i,
    Finset.mem_filter.mpr ⟨hi, hheavy.trans_le (measure_mono hpin)⟩,
    hpin hy, hsource y hy x hx hangle hnorm⟩

/-- The entire arbitrary family has the same actual deletion estimate as the finite grid. -/
theorem prod_all_direction_heavy_tubes_le {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (o : EuclideanSpace ℝ (Fin 2)) {X : Set (EuclideanSpace ℝ (Fin 2))}
    (p e : ι → EuclideanSpace ℝ (Fin 2)) (w : ι → ℝ) (he : ∀ t, ‖e t‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) {C ε D R δ : ℝ}
    (hw : ∀ t, w t ≤ C * (b / M)) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hR : ‖o‖ + b ≤ R) (hδ : 0 < δ) (hXR : ∀ x ∈ X, ‖x‖ ≤ R)
    (hsep : ∀ y ∈ Metric.ball o b, ∀ x ∈ X, δ ≤ (y - x) 0)
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
  apply prod_all_heavy_enlargedSlopeTubes_le μ ν o hb hM (Nat.ceil (4 * C + 2) + 1)
    hR (by
      have ht : 0 ≤ D / (M : ℝ) := by positivity
      linarith)
    hδ hXR hsep hac hN _ hA hAt hq ha hat
  simpa only [Nat.cast_add, Nat.cast_one] using hwidth

end FalconerPacking
