/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PinnedKernel

/-!
# A positive absolutely continuous component gives a positive pinned distance set

The joint distance relation of two compact sets is compact. A measure dominated by the
joint distance law is carried by this relation. If all its pinned fibers had zero length,
Fubini would give the relation zero product measure, contradicting a positive absolutely
continuous component. No disintegration of the component is assumed or used.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The actual joint distance relation, with the pin in the first coordinate. -/
def jointPinnedDistanceRelation (K L : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
    (p.1, dist p.2 p.1)) '' (L ×ˢ K)

/-- Membership in the joint relation is exactly membership in the appropriate pinned fiber. -/
theorem mem_jointPinnedDistanceRelation
    {K L : Set (EuclideanSpace ℝ (Fin 2))} {y : EuclideanSpace ℝ (Fin 2)} {t : ℝ} :
    (y, t) ∈ jointPinnedDistanceRelation K L ↔ y ∈ L ∧ t ∈ pinnedDistances K y := by
  constructor
  · rintro ⟨⟨z, x⟩, ⟨hz, hx⟩, he⟩
    obtain ⟨hzy, hdist⟩ := Prod.mk.inj he
    change z = y at hzy
    subst z
    exact ⟨hz, x, hx, hdist⟩
  · rintro ⟨hy, x, hx, hdist⟩
    exact ⟨(y, x), ⟨hy, hx⟩, Prod.ext rfl hdist⟩

/-- Compact source and pin sets have a compact, hence Borel, joint distance relation. -/
theorem isCompact_jointPinnedDistanceRelation
    {K L : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hL : IsCompact L) :
    IsCompact (jointPinnedDistanceRelation K L) :=
  (hL.prod hK).image (by fun_prop)

/-- The joint distance law is carried by the actual relation of two conull compact sets. -/
theorem jointPinnedDistanceMeasure_compl_relation_eq_zero
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hL : IsCompact L) (hμK : μ Kᶜ = 0) (hνL : ν Lᶜ = 0) :
    jointPinnedDistanceMeasure μ ν (jointPinnedDistanceRelation K L)ᶜ = 0 := by
  have hS := (isCompact_jointPinnedDistanceRelation hK hL).measurableSet
  rw [jointPinnedDistanceMeasure, Measure.map_apply (by fun_prop) hS.compl]
  apply measure_mono_null (t := (L ×ˢ K)ᶜ) ?_
    (Measure.measure_prod_compl_eq_zero hνL hμK)
  intro p hp hpLK
  exact hp (mem_image_of_mem _ hpLK)

/-- If every pinned fiber in the compact pin set is null, Fubini makes the entire relation null. -/
theorem prod_volume_jointPinnedDistanceRelation_eq_zero
    (ν : Measure (EuclideanSpace ℝ (Fin 2)))
    {K L : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hL : IsCompact L)
    (hnull : ∀ y ∈ L, volume (pinnedDistances K y) = 0) :
    (ν.prod volume) (jointPinnedDistanceRelation K L) = 0 := by
  rw [Measure.prod_apply (isCompact_jointPinnedDistanceRelation hK hL).measurableSet]
  have hfiber (y : EuclideanSpace ℝ (Fin 2)) :
      volume (Prod.mk y ⁻¹' jointPinnedDistanceRelation K L) = 0 := by
    by_cases hy : y ∈ L
    · have he : Prod.mk y ⁻¹' jointPinnedDistanceRelation K L = pinnedDistances K y := by
        ext t
        simp only [mem_preimage, mem_jointPinnedDistanceRelation, hy, true_and]
      rw [he]
      exact hnull y hy
    · have he : Prod.mk y ⁻¹' jointPinnedDistanceRelation K L = ∅ := by
        ext t
        simp only [mem_preimage, mem_jointPinnedDistanceRelation, hy, false_and,
          mem_empty_iff_false]
      rw [he, measure_empty]
  simp_rw [hfiber]
  exact lintegral_zero

/-- Any positive absolutely continuous measure below the joint distance law forces a
positive-length pinned distance set at a pin in the prescribed compact pin set. -/
theorem exists_mem_volume_pinnedDistances_pos_of_positive_component
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hL : IsCompact L) (hμK : μ Kᶜ = 0) (hνL : ν Lᶜ = 0)
    (σ : Measure (EuclideanSpace ℝ (Fin 2) × ℝ)) (hσ : 0 < σ univ)
    (hdom : σ ≤ jointPinnedDistanceMeasure μ ν) (hac : σ ≪ ν.prod volume) :
    ∃ y ∈ L, 0 < volume (pinnedDistances K y) := by
  by_contra hnone
  have hnull : ∀ y ∈ L, volume (pinnedDistances K y) = 0 := by
    intro y hy
    exact nonpos_iff_eq_zero.mp (not_lt.mp (fun hp ↦ hnone ⟨y, hy, hp⟩))
  have hS := (isCompact_jointPinnedDistanceRelation hK hL).measurableSet
  have hzero : σ (jointPinnedDistanceRelation K L) = 0 :=
    hac (prod_volume_jointPinnedDistanceRelation_eq_zero ν hK hL hnull)
  have hcompl : σ (jointPinnedDistanceRelation K L)ᶜ = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.le_iff.mp hdom _ hS.compl).trans_eq
      (jointPinnedDistanceMeasure_compl_relation_eq_zero μ ν hK hL hμK hνL))
  have htotal := measure_add_measure_compl (μ := σ) hS
  rw [hzero, hcompl, zero_add] at htotal
  exact hσ.ne' htotal.symm

end FalconerPacking
