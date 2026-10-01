/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.FiniteTubeEnlargement
import FalconerPacking.SlopeTubeEnergy
import FalconerPacking.SlopeTubeNet

/-!
# Actual enlarged slope tubes

Each enlargement is a finite union of neighboring strips at the same slope. Both incidence
degrees are bounded explicitly, so their square masses retain the truncated-energy bound.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Neighboring parallel strips preserve both the chart and the slope label. -/
def slopeTubeNeighbor (L : ℕ) (i j : Bool × (ℤ × ℤ)) : Prop :=
  i.1 = j.1 ∧ i.2.1 = j.2.1 ∧ |i.2.2 - j.2.2| ≤ (L : ℤ)

theorem slopeTubeNeighbor_comm (L : ℕ) (i j : Bool × (ℤ × ℤ)) :
    slopeTubeNeighbor L i j ↔ slopeTubeNeighbor L j i := by
  simp only [slopeTubeNeighbor, eq_comm, abs_sub_comm]

/-- A strip has at most 2L+1 neighbors in any finite subfamily. -/
theorem card_slopeTube_neighbors_le (I : Finset (Bool × (ℤ × ℤ))) (L : ℕ)
    (i : Bool × (ℤ × ℤ)) :
    (I.filter (slopeTubeNeighbor L i)).card ≤ 2 * L + 1 := by
  have hinj : (I.filter (slopeTubeNeighbor L i)).card ≤
      (Finset.Icc (i.2.2 - L) (i.2.2 + L)).card := by
    apply Finset.card_le_card_of_injOn (fun j ↦ j.2.2)
    · intro j hj
      have h := (abs_le.mp (Finset.mem_filter.mp hj).2.2.2)
      apply Finset.mem_Icc.mpr
      change i.2.2 - (L : ℤ) ≤ j.2.2 ∧ j.2.2 ≤ i.2.2 + L
      omega
    · rintro ⟨c, k, l⟩ hj ⟨c', k', l'⟩ hj' he
      have h := (Finset.mem_filter.mp hj).2
      have h' := (Finset.mem_filter.mp hj').2
      dsimp only [slopeTubeNeighbor] at h h'
      dsimp only at he
      obtain ⟨rfl, rfl⟩ : c = c' ∧ k = k' := ⟨h.1.symm.trans h'.1, h.2.1.symm.trans h'.2.1⟩
      simp only [he]
  have hcard : (Finset.Icc (i.2.2 - (L : ℤ)) (i.2.2 + L)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  rwa [hcard] at hinj

/-- A concrete tube enlargement, expressed as an actual finite union. -/
def enlargedSlopeTube (o : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (M L : ℕ)
    (i : Bool × (ℤ × ℤ)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ j ∈ (slopeTubeLabels M).filter (slopeTubeNeighbor L i), slopeTube o b M j

theorem measurableSet_enlargedSlopeTube (o : EuclideanSpace ℝ (Fin 2))
    (b : ℝ) (M L : ℕ) (i : Bool × (ℤ × ℤ)) :
    MeasurableSet (enlargedSlopeTube o b M L i) :=
  Finset.measurableSet_biUnion _ (fun j _ ↦ measurableSet_slopeStrip o b M j.1 j.2)

/-- Actual enlargement loses only the square of its finite offset multiplicity. -/
theorem sum_measure_enlargedSlopeTube_sq_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (o : EuclideanSpace ℝ (Fin 2))
    (b : ℝ) (M L : ℕ) :
    (∑ i ∈ slopeTubeLabels M, μ (enlargedSlopeTube o b M L i) ^ 2) ≤
      ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 *
        ∑ i ∈ slopeTubeLabels M, μ (slopeTube o b M i) ^ 2 := by
  have hr := fun i (_ : i ∈ slopeTubeLabels M) ↦
    card_slopeTube_neighbors_le (slopeTubeLabels M) L i
  have hc (j) (_ : j ∈ slopeTubeLabels M) :
      ((slopeTubeLabels M).filter (fun i ↦ slopeTubeNeighbor L i j)).card ≤ 2 * L + 1 := by
    simpa only [slopeTubeNeighbor_comm L _ j] using hr j (by assumption)
  simpa only [enlargedSlopeTube, pow_two] using
    sum_measure_finite_expansion_sq_le μ (slopeTubeLabels M) (slopeTube o b M)
      (slopeTubeNeighbor L) (2 * L + 1) (2 * L + 1) hr hc

/-- The enlarged family has a fully proved truncated-energy square-mass bound. -/
theorem sum_measure_enlargedSlopeTube_sq_le_truncEnergy
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (o : EuclideanSpace ℝ (Fin 2))
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) (L : ℕ) :
    (∑ i ∈ slopeTubeLabels M, μ (enlargedSlopeTube o b M L i) ^ 2) ≤
      20 * ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 * truncEnergy μ (b / M) b := by
  apply (sum_measure_enlargedSlopeTube_sq_le μ o b M L).trans
  calc
    _ ≤ ((2 * L + 1 : ℕ) : ℝ≥0∞) ^ 2 * (20 * truncEnergy μ (b / M) b) :=
      mul_le_mul' le_rfl (sum_measure_slopeTube_sq_le_truncEnergy μ o hb hM)
    _ = _ := by ring

end FalconerPacking
