/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularHeavyCells
import FalconerPacking.RadialProjectionTheorem

/-!
# Heavy angular cells in the actual source--pin product measure

The canonical radial densities define a jointly measurable deletion set. Finite disjoint
angular cell families at finitely many scales obey the density-moment deletion estimate.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The original source--pin pairs deleted by one finite angular cell family. -/
def radialHeavyCellPairs {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (I : Finset ι) (C : ι → Set ℝ) (A : ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
  {p | radialAngle p.1 p.2 ∈
    angularHeavyCells radialAngularMeasure (radialProjectionDensity ν p.1) I C A}

theorem measurableSet_radialHeavyCellPairs {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (I : Finset ι) (C : ι → Set ℝ) (A : ℝ≥0∞)
    (hC : ∀ i ∈ I, MeasurableSet (C i)) :
    MeasurableSet (radialHeavyCellPairs ν I C A) := by
  have h : MeasurableSet {p : EuclideanSpace ℝ (Fin 2) × ℝ |
      p.2 ∈ angularHeavyCells radialAngularMeasure (radialProjectionDensity ν p.1) I C A} :=
    measurableSet_angularHeavyCellPairs radialAngularMeasure
      (measurable_radialProjectionDensity ν) I C A hC
  have hf : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      (p.1, radialAngle p.1 p.2)) := measurable_fst.prodMk measurable_radialAngle
  change MeasurableSet ((fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
    (p.1, radialAngle p.1 p.2)) ⁻¹' {p : EuclideanSpace ℝ (Fin 2) × ℝ |
      p.2 ∈ angularHeavyCells radialAngularMeasure (radialProjectionDensity ν p.1) I C A})
  exact h.preimage hf

/-- The first moment of the canonical radial density is finite at every pin. -/
theorem lintegral_radialProjectionDensity_ne_top
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ θ, radialProjectionDensity ν x θ ∂radialAngularMeasure) ≠ ∞ := by
  have h := (withDensity_radialProjectionDensity_le ν x) univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.map_apply measurable_radialAngle.of_uncurry_left MeasurableSet.univ,
    preimage_univ] at h
  exact ne_top_of_le_ne_top (measure_ne_top ν univ) h

/-- At a retained pair every containing angular cell controls the actual source mass. -/
theorem radial_cell_mass_le_of_pair_retained {ι : Type*}
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (C : ι → Set ℝ) (A : ℝ≥0∞)
    {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : ν.map (radialAngle x) ≪ radialAngularMeasure)
    (hpair : (x, y) ∉ radialHeavyCellPairs ν I C A)
    {i : ι} (hi : i ∈ I) (hC : MeasurableSet (C i))
    (hθ : radialAngle x y ∈ C i) :
    ν (radialAngle x ⁻¹' C i) ≤ A * radialAngularMeasure (C i) := by
  rw [← Measure.map_apply measurable_radialAngle.of_uncurry_left hC,
    ← withDensity_radialProjectionDensity_eq ν x hx, withDensity_apply _ hC]
  exact cell_mass_le_of_not_mem_angularHeavyCells radialAngularMeasure
    (radialProjectionDensity ν x) I C A hpair hi hθ

/-- Finite-scale deletion is controlled by the actual averaged canonical radial moment. -/
theorem prod_radialHeavyCellPairs_le {ι κ : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (hac : ∀ᵐ x ∂μ, ν.map (radialAngle x) ≪ radialAngularMeasure)
    (S : Finset κ) (I : κ → Finset ι) (C : κ → ι → Set ℝ)
    (hd : ∀ j ∈ S, (↑(I j) : Set ι).PairwiseDisjoint (C j))
    (hC : ∀ j ∈ S, ∀ i ∈ I j, MeasurableSet (C j i))
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    μ.prod ν (⋃ j ∈ S, radialHeavyCellPairs ν (I j) (C j) (2 * A)) ≤
      S.card * (2 * A ^ (1 - q) *
        ∫⁻ x, ∫⁻ θ, radialProjectionDensity ν x θ ^ q ∂radialAngularMeasure ∂μ) := by
  have hmeas : MeasurableSet (⋃ j ∈ S, radialHeavyCellPairs ν (I j) (C j) (2 * A)) :=
    Finset.measurableSet_biUnion S fun j hj ↦
      measurableSet_radialHeavyCellPairs ν (I j) (C j) (2 * A) (hC j hj)
  rw [Measure.prod_apply hmeas]
  calc
    _ ≤ ∫⁻ x, S.card * (2 * A ^ (1 - q) *
        ∫⁻ θ, radialProjectionDensity ν x θ ^ q ∂radialAngularMeasure) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hac] with x hx
      have hset : Prod.mk x ⁻¹' (⋃ j ∈ S, radialHeavyCellPairs ν (I j) (C j) (2 * A)) =
          radialAngle x ⁻¹' (⋃ j ∈ S,
            angularHeavyCells radialAngularMeasure (radialProjectionDensity ν x)
              (I j) (C j) (2 * A)) := by
        ext y
        simp [radialHeavyCellPairs]
      rw [hset, ← Measure.map_apply measurable_radialAngle.of_uncurry_left
        (Finset.measurableSet_biUnion S fun j hj ↦ measurableSet_angularHeavyCells
          radialAngularMeasure (radialProjectionDensity ν x) (I j) (C j) (2 * A) (hC j hj)),
        ← withDensity_radialProjectionDensity_eq ν x hx]
      exact withDensity_biUnion_angularHeavyCells_le radialAngularMeasure
        (measurable_radialProjectionDensity ν).of_uncurry_left
        (lintegral_radialProjectionDensity_ne_top ν x) S I C hd hC hA hAt hq
    _ = _ := by
      rw [lintegral_const_mul _ ((measurable_radialProjectionMoment ν q).const_mul _),
        lintegral_const_mul _ (measurable_radialProjectionMoment ν q)]

end FalconerPacking
