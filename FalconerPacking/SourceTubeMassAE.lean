/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SourceTubeMass

/-!
# Source tube mass with geometry only at almost every pin

An enlarged tested tube can extend outside the separated pin support. Its retained witness
is chosen outside the single null set where radial absolute continuity, the norm bound,
or source separation fails. No geometric assertion about the rest of the tube is required.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Only the pins carrying the measure need satisfy the norm and separation assumptions. -/
theorem prod_retained_heavy_tubes_of_common_strips_ae {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (T S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (n c : ι → EuclideanSpace ℝ (Fin 2)) {R w δ : ℝ}
    (hn : ∀ i ∈ I, ‖n i‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hTR : ∀ᵐ y ∂μ, ‖y‖ ≤ R)
    (hSR : ∀ i ∈ I, ∀ x ∈ S i, ‖x‖ ≤ R)
    (hsep : ∀ᵐ y ∂μ, ∀ i ∈ I, ∀ x ∈ S i, δ ≤ (y - x) 0)
    (hTstrip : ∀ i ∈ I, ∀ y ∈ T i, |⟪n i, y - c i⟫| ≤ w)
    (hSstrip : ∀ i ∈ I, ∀ x ∈ S i, |⟪n i, x - c i⟫| ≤ w)
    (hac : ∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure)
    {N : ℕ} (hN : 0 < N) (hwidth : 8 * R * w / δ ^ 2 ≤ 2 * Real.pi / N)
    (A : ℝ≥0∞) {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞) :
    (μ.prod ν) ((⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) \
      radialHeavyCellPairs ν (Finset.range N) (enlargedAngularCell N) A) ≤
      ((A * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
        ∑ i ∈ I, μ (T i) ^ 2 := by
  let P := {y | ¬(ν.map (radialAngle y) ≪ radialAngularMeasure ∧ ‖y‖ ≤ R ∧
    ∀ i ∈ I, ∀ x ∈ S i, δ ≤ (y - x) 0)}
  have hP : μ P = 0 := by
    apply ae_iff.mp
    filter_upwards [hac, hTR, hsep] with y hyac hyR hysep
    exact ⟨hyac, hyR, hysep⟩
  apply prod_retained_heavy_tubes_le_outside_null_pins μ ν I T S _ P hP ha hat
  intro i hi hretained
  obtain ⟨⟨y, x⟩, ⟨⟨hy, hyP⟩, hx⟩, hpair⟩ := hretained
  have hgood : ν.map (radialAngle y) ≪ radialAngularMeasure ∧ ‖y‖ ≤ R ∧
      ∀ i ∈ I, ∀ x ∈ S i, δ ≤ (y - x) 0 := by
    simpa only [P, mem_setOf_eq, not_not] using hyP
  exact source_tube_mass_le_of_retained_pair ν (hn i hi) hw hδ
    hgood.2.1 (hSR i hi) (hgood.2.2 i hi)
    (hTstrip i hi y hy) (hSstrip i hi) hx hN hwidth hgood.1 A hpair

/-- Source-heavy and pin-heavy deletion retain the same constants under almost-everywhere
pin geometry. -/
theorem prod_all_heavy_tubes_of_common_strips_ae {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (T S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (n c : ι → EuclideanSpace ℝ (Fin 2)) {R w δ : ℝ}
    (hn : ∀ i ∈ I, ‖n i‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hTR : ∀ᵐ y ∂μ, ‖y‖ ≤ R)
    (hSR : ∀ i ∈ I, ∀ x ∈ S i, ‖x‖ ≤ R)
    (hsep : ∀ᵐ y ∂μ, ∀ i ∈ I, ∀ x ∈ S i, δ ≤ (y - x) 0)
    (hTstrip : ∀ i ∈ I, ∀ y ∈ T i, |⟪n i, y - c i⟫| ≤ w)
    (hSstrip : ∀ i ∈ I, ∀ x ∈ S i, |⟪n i, x - c i⟫| ≤ w)
    (hac : ∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure)
    {N : ℕ} (hN : 0 < N) (hwidth : 8 * R * w / δ ^ 2 ≤ 2 * Real.pi / N)
    {A a : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q)
    (ha : a ≠ 0) (hat : a ≠ ∞) :
    (μ.prod ν) (radialHeavyCellPairs ν (Finset.range N) (enlargedAngularCell N) (2 * A) ∪
      ⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) ≤
      8 * A ^ (1 - q) *
        (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂μ) +
      (((2 * A) * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
        ∑ i ∈ I, μ (T i) ^ 2 := by
  rw [← union_sdiff_self]
  exact (measure_union_le _ _).trans (add_le_add
    (prod_enlarged_radialHeavyCells_le μ ν hac hN hA hAt hq)
    (prod_retained_heavy_tubes_of_common_strips_ae μ ν I T S n c hn hw hδ hTR hSR
      hsep hTstrip hSstrip hac hN hwidth (2 * A) ha hat))

end FalconerPacking
