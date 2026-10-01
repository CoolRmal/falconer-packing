/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SlopeTubeNormals
import FalconerPacking.SourceTubeMass

/-!
# Actual source sets associated with enlarged heavy pin tubes

The normals, centers, source strips, and pin tubes are all constructed. The source-heavy
radial deletion and the actual truncated pin energy give their total product-mass bound.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The actual source strip associated with a finite-grid pin tube. -/
def sourceSlopeTube (X : Set (EuclideanSpace ℝ (Fin 2)))
    (o : EuclideanSpace ℝ (Fin 2)) (b w : ℝ) (M : ℕ) (i : Bool × (ℤ × ℤ)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  X ∩ {x | |⟪slopeUnitNormal i.1 ((i.2.1 : ℝ) / M), x - slopeTubeCenter o b M i⟫| ≤ w}

theorem measurableSet_sourceSlopeTube {X : Set (EuclideanSpace ℝ (Fin 2))}
    (hX : MeasurableSet X) (o : EuclideanSpace ℝ (Fin 2)) (b w : ℝ) (M : ℕ)
    (i : Bool × (ℤ × ℤ)) : MeasurableSet (sourceSlopeTube X o b w M i) :=
  hX.inter ((isClosed_le (by fun_prop) continuous_const).measurableSet)

/-- Actual finite source and pin tubes obey the joint deletion estimate, including all
source mass and finite-grid enlargement costs. -/
theorem prod_all_heavy_enlargedSlopeTubes_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (o : EuclideanSpace ℝ (Fin 2)) {X : Set (EuclideanSpace ℝ (Fin 2))}
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) (L : ℕ)
    {R w δ : ℝ} (hR : ‖o‖ + b ≤ R) (hw : (L + 1) * (b / M) ≤ w)
    (hδ : 0 < δ) (hXR : ∀ x ∈ X, ‖x‖ ≤ R)
    (hsep : ∀ y ∈ Metric.ball o b, ∀ x ∈ X, δ ≤ (y - x) 0)
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
  have hTball (i) (y) (hy : y ∈ enlargedSlopeTube o b M L i) :
      y ∈ Metric.ball o b := (enlargedSlopeTube_normal_bound hb hM hy).1
  have hTR (i) (_ : i ∈ slopeTubeLabels M) (y)
      (hy : y ∈ enlargedSlopeTube o b M L i) : ‖y‖ ≤ R := by
    have hbdy : ‖y - o‖ < b := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hTball i y hy
    have hnorm := norm_add_le (y - o) o
    rw [sub_add_cancel] at hnorm
    linarith
  have h := prod_all_heavy_tubes_of_common_strips μ ν (slopeTubeLabels M)
    (enlargedSlopeTube o b M L) (sourceSlopeTube X o b w M)
    (fun i ↦ slopeUnitNormal i.1 ((i.2.1 : ℝ) / M)) (slopeTubeCenter o b M)
    (fun i _ ↦ norm_slopeUnitNormal _ _) hw₀ hδ hTR
    (fun i _ x hx ↦ hXR x hx.1)
    (fun i _ y hy x hx ↦ hsep y (hTball i y hy) x hx.1)
    (fun i _ y hy ↦ (enlargedSlopeTube_unit_normal_bound hb hM hy).trans hw)
    (fun i _ x hx ↦ hx.2) hac hN hwidth hA hAt hq ha hat
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (((2 * A) * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
        (20 * ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 * truncEnergy μ (b / M) b) :=
      mul_le_mul' le_rfl (sum_measure_enlargedSlopeTube_sq_le_truncEnergy μ o hb hM L)
    _ = _ := by ring

end FalconerPacking
