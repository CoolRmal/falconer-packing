/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PacketEffectiveNormals
import FalconerPacking.Restriction

/-!
# The physical marks used by both deletion and circle-energy iteration

A mark is defined by the actual measure of the tested rectangle in the enlarged parent.
The same definition supplies the selected tube test and the conditional heavy-tube event.
No auxiliary fine Fourier cell changes a whole standard packet's survival decision.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- The actual enlarged parent used for a child at the selected spatial level. -/
def physicalDyadicParent (n : ℕ → ℕ) (L : ℝ) (j : ℕ) (Q : Fin 2 → ℤ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2))
    (ancestor (n j - n (j + 1)) Q)

/-- The literal oriented rectangle tested by the spatial circle-energy edge. -/
def physicalDyadicTube (n e : ℕ → ℕ) (s K : ℕ) (L : ℝ) (j : ℕ)
    (Q : Fin 2 → ℤ) (β : ℕ ⊕ (ℕ × ℕ)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  frameRectangle (dyadicCapPhysicalFrame s (e (j + 1)) β)
    (gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ Q)
    (L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2)
    (L ^ (4 * K + 20) * ((2 : ℝ) ^ n (j + 1))⁻¹ / 2)

/-- A good mark is the actual tube test with the same parent mass as in the energy edge. -/
def physicalDyadicGood (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n e : ℕ → ℕ) (s K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (j : ℕ) (Q : Fin 2 → ℤ) (β : ℕ ⊕ (ℕ × ℕ)) : Prop :=
  σ (physicalDyadicTube n e s K L j Q β ∩ physicalDyadicParent n L j Q) ≤
    H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹) *
      σ (physicalDyadicParent n L j Q)

/-- For a positive-mass parent the raw test is exactly its normalized conditional test. -/
theorem physicalDyadicGood_iff_normalized
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (n e : ℕ → ℕ) (s K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (j : ℕ) (Q : Fin 2 → ℤ) (β : ℕ ⊕ (ℕ × ℕ))
    (hQ : σ (physicalDyadicParent n L j Q) ≠ 0) :
    physicalDyadicGood σ n e s K L H j Q β ↔
      normalizedRestrict σ (physicalDyadicParent n L j Q)
          (physicalDyadicTube n e s K L j Q β) ≤
        H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹) := by
  have hm : MeasurableSet (physicalDyadicTube n e s K L j Q β) :=
    measurableSet_frameRectangle _ _ _ _
  rw [normalizedRestrict_apply _ _ _ hm,
    ENNReal.inv_mul_le_iff hQ (measure_ne_top σ _)]
  simp only [physicalDyadicGood, mul_comm]

/-- Every physical ancestor test is independent of the terminal fine-cell index. -/
theorem physicalDyadicGood_ancestor_iff
    (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n e : ℕ → ℕ) (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (j : ℕ) (Q : Fin 2 → ℤ) (c u v : ℕ) :
    physicalDyadicGood σ n e s K L H j Q
        (dyadicCapAncestor s t (e (j + 1)) (c, u)) ↔
      physicalDyadicGood σ n e s K L H j Q
        (dyadicCapAncestor s t (e (j + 1)) (c, v)) := by
  unfold physicalDyadicGood physicalDyadicTube
  rw [dyadicCapPhysicalFrame_ancestor_eq s t (e (j + 1)) c u v]

/-- The source packet survival predicate is an explicit test on its original standard cap. -/
def standardPacketSurvives (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n e : ℕ → ℕ) (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (j : ℕ) (Q : Fin 2 → ℤ) (c : ℕ) : Prop :=
  dyadicCapSpatialSurvives s t n e (physicalDyadicGood σ n e s K L H) j K Q (c, 0)

/-- The Fourier survival masks are exactly the whole-standard-packet decisions. -/
theorem dyadicCapSpatialSurvives_physical_iff
    (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n e : ℕ → ℕ) (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (j : ℕ) (Q : Fin 2 → ℤ) (q : ℕ × ℕ) :
    dyadicCapSpatialSurvives s t n e (physicalDyadicGood σ n e s K L H) j K Q q ↔
      standardPacketSurvives σ n e s t K L H j Q q.1 := by
  unfold dyadicCapSpatialSurvives standardPacketSurvives
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  exact physicalDyadicGood_ancestor_iff σ n e s t K L H i _ q.1 q.2 0

/-- A failed whole-packet decision has an actual bad ancestor, with no extra Fourier labels. -/
theorem not_standardPacketSurvives_iff
    (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (n e : ℕ → ℕ) (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞)
    (j : ℕ) (Q : Fin 2 → ℤ) (c : ℕ) :
    ¬ standardPacketSurvives σ n e s t K L H j Q c ↔
      ∃ i, j ≤ i ∧ i < K ∧
        ¬ physicalDyadicGood σ n e s K L H i (ancestor (n j - n i) Q)
          (dyadicCapAncestor s t (e (i + 1)) (c, 0)) := by
  simp only [standardPacketSurvives, dyadicCapSpatialSurvives, not_forall, exists_prop]

end FalconerPacking
