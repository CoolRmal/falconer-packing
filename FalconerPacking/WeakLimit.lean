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

/-- Choose one normalized finite Frostman approximation at every positive depth.  The ball
constant is uniform, and the `n`-th approximation has the estimate through depth `n + 1`. -/
theorem exists_probabilityMeasure_approximation_sequence
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {d : ℝ} (hd : 0 ≤ d) (hcontent : 0 < hausdorffContent d K) :
    ∃ μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      (∀ n, μ n ∈ probabilityMeasuresSupportedOn K) ∧
      ∀ n i, i ≤ n + 1 → ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            (4 * ENNReal.ofReal (allowance i d)) := by
  have hex : ∀ n : ℕ, ∃ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0 ∧
      ∀ i ≤ n + 1, ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            (4 * ENNReal.ofReal (allowance i d)) := by
    intro n
    exact exists_compact_probabilityMeasure_all_scale_estimates hK
      (Nat.succ_le_succ (Nat.zero_le n)) hd hcontent
  choose μ hsupp hbound using hex
  refine ⟨μ, ?_, ?_⟩
  · exact fun n ↦ hsupp n
  · exact fun n i hi ↦ hbound n i hi

/-- The finite Frostman approximations have a weakly convergent subsequence supported on `K`. -/
theorem exists_tendsto_frostman_approximation_subseq
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {d : ℝ} (hd : 0 ≤ d) (hcontent : 0 < hausdorffContent d K) :
    ∃ (μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
      (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (φ : ℕ → ℕ),
      ν ∈ probabilityMeasuresSupportedOn K ∧ StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 ν) ∧
      ∀ n i, i ≤ n + 1 → ∀ x r, 0 < r → r ≤ dyadicCoverRadius i →
        (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            (4 * ENNReal.ofReal (allowance i d)) := by
  obtain ⟨μ, hsupp, hbound⟩ :=
    exists_probabilityMeasure_approximation_sequence hK hd hcontent
  obtain ⟨ν, hν, φ, hφ, hconv⟩ := exists_tendsto_subseq_of_supported hK μ hsupp
  exact ⟨μ, ν, φ, hν, hφ, hconv, hbound⟩

/-- An eventual uniform upper bound on the mass of an open ball passes to a weak limit. -/
theorem probabilityMeasure_ball_le_of_tendsto_of_eventually_le
    {μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))}
    (hconv : Tendsto μ atTop (𝓝 ν)) {x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    {C : ℝ≥0∞}
    (hbound : ∀ᶠ n in atTop,
      (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤ C) :
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤ C := by
  refine (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
    hconv Metric.isOpen_ball).trans ?_
  calc
    atTop.liminf (fun n ↦
        (μ n : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r))
      ≤ atTop.liminf (fun _ : ℕ ↦ C) := Filter.liminf_le_liminf hbound
    _ = C := Filter.liminf_const C

/-- The weak limit of the finite constructions is supported on `K` and retains every dyadic-scale
ball estimate. -/
theorem exists_probabilityMeasure_dyadic_frostman
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    {d : ℝ} (hd : 0 ≤ d) (hcontent : 0 < hausdorffContent d K) :
    ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      ν ∈ probabilityMeasuresSupportedOn K ∧
      ∀ i x r, 0 < r → r ≤ dyadicCoverRadius i →
        (ν : Measure (EuclideanSpace ℝ (Fin 2))) (Metric.ball x r) ≤
          (ENNReal.ofReal (Real.sqrt 2 ^ d) * (hausdorffContent d K)⁻¹) *
            (4 * ENNReal.ofReal (allowance i d)) := by
  obtain ⟨μ, ν, φ, hν, hφ, hconv, hbound⟩ :=
    exists_tendsto_frostman_approximation_subseq hK hd hcontent
  refine ⟨ν, hν, ?_⟩
  intro i x r hr hri
  apply probabilityMeasure_ball_le_of_tendsto_of_eventually_le hconv
  filter_upwards [eventually_ge_atTop i] with k hk
  apply hbound (φ k) i
  · exact hk.trans (hφ.le_apply.trans (Nat.le_add_right (φ k) 1))
  · exact hr
  · exact hri

end FalconerPacking
