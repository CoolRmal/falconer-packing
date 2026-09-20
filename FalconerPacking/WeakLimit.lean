/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.OccupiedCubes
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Weak compactness for the finite Frostman measures

Probability measures carried by one compact planar set form a compact set for the weak topology.
Consequently every sequence of the normalized atomic Frostman measures has a weakly convergent
subsequence whose limit is still carried by the same compact set.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace FalconerPacking

/-- Probability measures that give no mass to the complement of `K`. -/
def probabilityMeasuresSupportedOn (K : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) :=
  {μ | (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0}

/-- Probability measures carried by a compact planar set form a compact set in the weak
topology. -/
theorem isCompact_probabilityMeasuresSupportedOn {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) : IsCompact (probabilityMeasuresSupportedOn K) := by
  have hcompact :=
    isCompact_setOf_probabilityMeasure_mass_eq_compl_isCompact_le
      (E := EuclideanSpace ℝ (Fin 2)) (u := fun _ ↦ 0) (K := fun _ ↦ K)
      tendsto_const_nhds (fun _ ↦ hK) (Or.inl inferInstance)
  have heq : probabilityMeasuresSupportedOn K =
      {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) | ∀ n : ℕ, μ Kᶜ ≤ 0} := by
    ext μ
    simp only [probabilityMeasuresSupportedOn, mem_setOf_eq, nonpos_iff_eq_zero]
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simp
  rw [heq]
  exact hcompact

/-- Every sequence of probability measures carried by one compact set has a weakly convergent
subsequence, and its limit remains carried by that set. -/
theorem exists_tendsto_subseq_of_supported {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (hμ : ∀ n, μ n ∈ probabilityMeasuresSupportedOn K) :
    ∃ ν ∈ probabilityMeasuresSupportedOn K, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  obtain ⟨ν, hν, φ, hφ, hconv⟩ :=
    (isCompact_probabilityMeasuresSupportedOn hK).isSeqCompact hμ
  exact ⟨ν, hν, φ, hφ, hconv⟩

/-- A normalized atomic Frostman measure whose selected atoms lie in `K` belongs to the compact
space of probability measures carried by `K`. -/
theorem weightProbabilityMeasure_mem_probabilityMeasuresSupportedOn
    {S : Finset (Fin 2 → ℤ)}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K)
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k ∈ S, pt k ∈ K) :
    weightProbabilityMeasure S pt w ∈ probabilityMeasuresSupportedOn K :=
  weightProbabilityMeasure_compl_eq_zero hK hw hmass hpt

end FalconerPacking
