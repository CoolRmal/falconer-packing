/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.FrostmanWeights
import FalconerPacking.Restriction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# From Frostman weights to measures

The finite Frostman construction produces weights on the occupied cubes of one generation.  This
file turns them into an actual measure — a finite sum of point masses, one in each occupied cube
— and transfers the combinatorial bounds:

* the mass of a dyadic cube of any generation `i ≤ n` is exactly the combinatorial `cubeMass`;
* hence every such cube stays within its allowance;
* hence, through the cube-to-ball bridge, balls of radius at most `2⁻ⁿ⁻¹` satisfy a Frostman
  bound with constant `4`;
* and the total mass is the total weight.

What remains for the classical Frostman lemma is the weak limit as `n → ∞`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The measure carried by a weight assignment: one point mass in each occupied cube. -/
def weightMeasure (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    Measure (EuclideanSpace ℝ (Fin 2)) :=
  ∑ k' ∈ S, Real.toNNReal (w k') • Measure.dirac (pt k')

theorem weightMeasure_apply (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (w : (Fin 2 → ℤ) → ℝ) {A : Set (EuclideanSpace ℝ (Fin 2))} (_hA : MeasurableSet A) :
    weightMeasure S pt w A =
      ∑ k' ∈ S, ENNReal.ofReal (w k') * Measure.dirac (pt k') A := by
  rw [weightMeasure, Measure.finsetSum_apply]
  simp only [Measure.coe_nnreal_smul_apply, ENNReal.ofNNReal_toNNReal]

/-- The total mass is the total weight. -/
theorem weightMeasure_univ (S : Finset (Fin 2 → ℤ)) (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    {w : (Fin 2 → ℤ) → ℝ} (hw : ∀ k, 0 ≤ w k) :
    weightMeasure S pt w univ = ENNReal.ofReal (∑ k' ∈ S, w k') := by
  rw [weightMeasure_apply _ _ _ MeasurableSet.univ]
  simp only [Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  exact (ENNReal.ofReal_sum_of_nonneg fun k' _ ↦ hw k').symm

/-- Regard the finite atomic measure as a finite measure in mathlib's bundled type. -/
def weightFiniteMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    FiniteMeasure (EuclideanSpace ℝ (Fin 2)) :=
  ⟨weightMeasure S pt w, by
    rw [weightMeasure]
    infer_instance⟩

@[simp]
theorem weightFiniteMeasure_toMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    (weightFiniteMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))) =
      weightMeasure S pt w :=
  rfl

/-- Normalize a nonzero finite Frostman construction to a probability measure.  The definition is
total; as in mathlib, the zero input is sent to a fixed point mass. -/
def weightProbabilityMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) (w : (Fin 2 → ℤ) → ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) :=
  (weightFiniteMeasure S pt w).normalize

/-- Positive total weight makes the atomic measure nonzero. -/
theorem weightFiniteMeasure_ne_zero (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) {w : (Fin 2 → ℤ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k') :
    weightFiniteMeasure S pt w ≠ 0 := by
  intro hzero
  have huniv : weightMeasure S pt w univ = 0 := by
    rw [← weightFiniteMeasure_toMeasure]
    simp [hzero]
  rw [weightMeasure_univ S pt hw, ENNReal.ofReal_eq_zero] at huniv
  exact (not_le_of_gt hmass) huniv

/-- On a nonzero construction, normalization divides the original measure by its total mass. -/
theorem weightProbabilityMeasure_toMeasure (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) {w : (Fin 2 → ℤ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k') :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))) =
      (weightFiniteMeasure S pt w).mass⁻¹ • weightMeasure S pt w := by
  rw [weightProbabilityMeasure,
    (weightFiniteMeasure S pt w).toMeasure_normalize_eq_of_nonzero
      (weightFiniteMeasure_ne_zero S pt hw hmass), weightFiniteMeasure_toMeasure]

/-- The bundled finite measure has the expected total mass. -/
theorem weightFiniteMeasure_mass (S : Finset (Fin 2 → ℤ))
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) {w : (Fin 2 → ℤ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) :
    (weightFiniteMeasure S pt w).mass = Real.toNNReal (∑ k' ∈ S, w k') := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass, weightFiniteMeasure_toMeasure,
    weightMeasure_univ S pt hw]
  rfl

/-- If every selected atom lies in `K`, the atomic measure gives zero mass to its complement. -/
theorem weightMeasure_compl_eq_zero {S : Finset (Fin 2 → ℤ)}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K)
    (hpt : ∀ k ∈ S, pt k ∈ K) :
    weightMeasure S pt w Kᶜ = 0 := by
  rw [weightMeasure_apply S pt w hK.compl]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  simp [Measure.dirac_apply, hpt k hk]

/-- Normalization preserves the fact that all mass is carried by `K`. -/
theorem weightProbabilityMeasure_compl_eq_zero {S : Finset (Fin 2 → ℤ)}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K)
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k ∈ S, pt k ∈ K) :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0 := by
  rw [weightProbabilityMeasure_toMeasure S pt hw hmass,
    Measure.coe_nnreal_smul_apply, weightMeasure_compl_eq_zero hK hpt, mul_zero]

section CubeMass

variable {S : Finset (Fin 2 → ℤ)} {n : ℕ} {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ}

/-- A chosen point of an occupied cube lies in a cube of a coarser generation exactly when that
cube is its ancestor. -/
theorem mem_dyadicCube_iff_ancestor {i : ℕ} (hin : i ≤ n) {k' c : Fin 2 → ℤ}
    (hpt : pt k' ∈ dyadicCube n k') :
    pt k' ∈ dyadicCube i c ↔ ancestor (n - i) k' = c := by
  constructor
  · intro hmem
    have hanc : pt k' ∈ dyadicCube i (ancestor (n - i) k') := by
      have harith : i + (n - i) = n := by omega
      have := dyadicCube_subset_ancestor i (n - i) k'
      rw [harith] at this
      exact this hpt
    by_contra hne
    exact absurd (mem_dyadicCube_iff.1 hmem) (by
      rw [mem_dyadicCube_iff.1 hanc] at *
      exact fun h ↦ hne h)
  · intro hanc
    have harith : i + (n - i) = n := by omega
    have hsub := dyadicCube_subset_ancestor i (n - i) k'
    rw [harith] at hsub
    rw [← hanc]
    exact hsub hpt

/-- **The measure of a dyadic cube is its combinatorial mass.** -/
theorem weightMeasure_dyadicCube (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k') {i : ℕ} (hin : i ≤ n) (c : Fin 2 → ℤ) :
    weightMeasure S pt w (dyadicCube i c) = ENNReal.ofReal (cubeMass S n i w c) := by
  classical
  rw [weightMeasure_apply _ _ _ (measurableSet_dyadicCube i c), cubeMass,
    ENNReal.ofReal_sum_of_nonneg fun k' _ ↦ hw k']
  simp only [Measure.dirac_apply, Set.indicator_apply, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun k' hk' ↦ ?_
  by_cases hmem : pt k' ∈ dyadicCube i c
  · rw [if_pos hmem, if_pos ((mem_dyadicCube_iff_ancestor hin (hpt k' hk')).1 hmem)]
  · rw [if_neg hmem, if_neg (fun h ↦ hmem ((mem_dyadicCube_iff_ancestor hin (hpt k' hk')).2 h))]

/-- The measure obeys the allowance of every generation. -/
theorem weightMeasure_dyadicCube_le {d : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) {i : ℕ} (hin : i ≤ n)
    (c : Fin 2 → ℤ) :
    weightMeasure S pt w (dyadicCube i c) ≤ ENNReal.ofReal (allowance i d) := by
  rw [weightMeasure_dyadicCube hw hpt hin c]
  exact ENNReal.ofReal_le_ofReal (hbound i hin c)

/-- **A Frostman bound on balls.**  Through the four-cube bridge, the measure of a ball of radius
at most `2⁻ⁿ⁻¹` is at most `4` times the allowance of generation `n`. -/
theorem weightMeasure_ball_le {d : ℝ} (hw : ∀ k, 0 ≤ w k)
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    weightMeasure S pt w (Metric.ball x r) ≤ 4 * ENNReal.ofReal (allowance n d) :=
  measure_ball_le_of_cube_bound hr hrn fun k ↦
    weightMeasure_dyadicCube_le hw hpt hbound le_rfl k

end CubeMass

/-- Normalization transfers a dyadic cube estimate, with the reciprocal total mass as the new
constant. -/
theorem weightProbabilityMeasure_dyadicCube_le {S : Finset (Fin 2 → ℤ)} {n : ℕ}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ} {d : ℝ}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d)
    {i : ℕ} (hin : i ≤ n) (c : Fin 2 → ℤ) :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
        (dyadicCube i c) ≤
      ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ * ENNReal.ofReal (allowance i d) := by
  rw [weightProbabilityMeasure_toMeasure S pt hw hmass,
    Measure.coe_nnreal_smul_apply,
    ENNReal.coe_inv ((weightFiniteMeasure S pt w).mass_nonzero_iff.mpr
      (weightFiniteMeasure_ne_zero S pt hw hmass))]
  gcongr
  exact weightMeasure_dyadicCube_le hw hpt hbound hin c

/-- Normalization transfers the four-cube ball estimate, again divided by the total mass. -/
theorem weightProbabilityMeasure_ball_le {S : Finset (Fin 2 → ℤ)} {n : ℕ}
    {pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)} {w : (Fin 2 → ℤ) → ℝ} {d : ℝ}
    (hw : ∀ k, 0 ≤ w k) (hmass : 0 < ∑ k' ∈ S, w k')
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k')
    (hbound : ∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d)
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (hrn : r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1))) :
    (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
        (Metric.ball x r) ≤
      ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ *
        (4 * ENNReal.ofReal (allowance n d)) := by
  rw [weightProbabilityMeasure_toMeasure S pt hw hmass,
    Measure.coe_nnreal_smul_apply,
    ENNReal.coe_inv ((weightFiniteMeasure S pt w).mass_nonzero_iff.mpr
      (weightFiniteMeasure_ne_zero S pt hw hmass))]
  gcongr
  exact weightMeasure_ball_le hw hpt hbound x hr hrn

/-- A positive content lower bound forces the total weight in the finite Frostman construction to
be positive. -/
theorem totalWeight_pos_of_hausdorffContent_pos {S : Finset (Fin 2 → ℤ)} {d : ℝ}
    {K : Set (EuclideanSpace ℝ (Fin 2))} {w : (Fin 2 → ℤ) → ℝ}
    (hcontent : 0 < hausdorffContent d K)
    (hbound : hausdorffContent d K ≤
      ENNReal.ofReal (Real.sqrt 2 ^ d) * ENNReal.ofReal (∑ k' ∈ S, w k')) :
    0 < ∑ k' ∈ S, w k' := by
  by_contra hmass
  rw [not_lt] at hmass
  rw [ENNReal.ofReal_eq_zero.mpr hmass, mul_zero] at hbound
  exact (not_le_of_gt hcontent) hbound

/-- The finite Frostman lemma, packaged as normalized probability measures.  At every finite depth
it produces a genuine probability measure with all dyadic estimates and the finest-scale ball
estimate. -/
theorem exists_weightProbabilityMeasure_estimates (S : Finset (Fin 2 → ℤ)) {n : ℕ}
    (hn : 1 ≤ n) {d : ℝ} (hd : 0 ≤ d) {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hcontent : 0 < hausdorffContent d K)
    (hcov : K ⊆ ⋃ k' ∈ S, dyadicCube n k')
    (pt : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (hpt : ∀ k' ∈ S, pt k' ∈ dyadicCube n k') :
    ∃ w : (Fin 2 → ℤ) → ℝ,
      (∀ k, 0 ≤ w k) ∧
      0 < ∑ k' ∈ S, w k' ∧
      (∀ i ≤ n, ∀ k, cubeMass S n i w k ≤ allowance i d) ∧
      (∀ i ≤ n, ∀ c,
        (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
            (dyadicCube i c) ≤
          ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (allowance i d)) ∧
      ∀ x r, 0 < r → r ≤ (2 : ℝ) ^ (-((n : ℝ) + 1)) →
        (weightProbabilityMeasure S pt w : Measure (EuclideanSpace ℝ (Fin 2)))
            (Metric.ball x r) ≤
          ((weightFiniteMeasure S pt w).mass : ℝ≥0∞)⁻¹ *
            (4 * ENNReal.ofReal (allowance n d)) := by
  obtain ⟨w, hw, hbound, hmassbound⟩ := exists_frostman_weights S hn hd hcov
  have hmass : 0 < ∑ k' ∈ S, w k' :=
    totalWeight_pos_of_hausdorffContent_pos hcontent hmassbound
  refine ⟨w, hw, hmass, hbound, ?_, ?_⟩
  · exact fun i hi c ↦
      weightProbabilityMeasure_dyadicCube_le hw hmass hpt hbound hi c
  · exact fun x r hr hrn ↦
      weightProbabilityMeasure_ball_le hw hmass hpt hbound x hr hrn

end FalconerPacking
