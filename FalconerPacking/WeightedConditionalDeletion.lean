/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicAffineDensity
import FalconerPacking.PhysicalBadPacketPairs
import FalconerPacking.GridEnergyBounds

/-!
# Summing conditional deletion bounds with their original masses

Normalization is undone before summing. Enlarged parents cost their geometric overlap,
whereas disjoint regular components cost no counting factor. The pair sets may be arbitrary;
only the parent regions need to be measurable.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Original mass exactly cancels normalization in every nonnegative conditional integral. -/
theorem measure_mul_lintegral_normalizedRestrict
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (U : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    σ U * (∫⁻ x, f x ∂normalizedRestrict σ U) = ∫⁻ x in U, f x ∂σ := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, measure_smul_normalizedRestrict]

/-- A pair set carried by a parent has its exact original product mass after weighting. -/
theorem measure_mul_normalizedRestrict_prod
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [SFinite ν]
    {U : Set (EuclideanSpace ℝ (Fin 2))} (hU : MeasurableSet U)
    {E : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))}
    (hE : E ⊆ U ×ˢ univ) :
    σ U * ((normalizedRestrict σ U).prod ν) E = (σ.prod ν) E := by
  rw [← smul_eq_mul, ← Measure.smul_apply, ← Measure.prod_smul_left,
    measure_smul_normalizedRestrict, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply' (hU.prod MeasurableSet.univ), inter_eq_left.mpr hE]

/-- The conditional moments over overlapping parents sum with only their overlap. -/
theorem sum_weighted_conditional_moment_le {ι : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hU : ∀ i ∈ I, MeasurableSet (U i)) (B : ℕ)
    (hB : ∀ x, (I.filter (fun i ↦ x ∈ U i)).card ≤ B)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∑ i ∈ I, σ (U i) * ∫⁻ x, f x ∂normalizedRestrict σ (U i)) ≤
      (B : ℝ≥0∞) * ∫⁻ x, f x ∂σ := by
  simp_rw [measure_mul_lintegral_normalizedRestrict]
  have h := sum_measure_le_mul_of_multiplicity (σ.withDensity f) I U
    MeasurableSet.univ hU (fun _ _ ↦ subset_univ _) B hB
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    show (∑ i ∈ I, σ.withDensity f (U i)) = ∑ i ∈ I, ∫⁻ x in U i, f x ∂σ from
      Finset.sum_congr rfl fun i hi ↦ withDensity_apply f (hU i hi)] using h

/-- Conditional pair estimates sum without the number of parents. The second term retains
its original mass-weighted energies, allowing either a uniform or a sharper energy estimate. -/
theorem prod_biUnion_le_conditional_deletion {ι : Type*}
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [SFinite ν]
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (E : ι → Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hU : ∀ i ∈ I, MeasurableSet (U i))
    (hE : ∀ i ∈ I, E i ⊆ U i ×ˢ univ) (B : ℕ)
    (hB : ∀ x, (I.filter (fun i ↦ x ∈ U i)).card ≤ B)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (c d : ℝ≥0∞) (energy : ι → ℝ≥0∞)
    (hlocal : ∀ i ∈ I, σ (U i) ≠ 0 →
      ((normalizedRestrict σ (U i)).prod ν) (E i) ≤
        c * (∫⁻ x, f x ∂normalizedRestrict σ (U i)) + d * energy i) :
    (σ.prod ν) (⋃ i ∈ I, E i) ≤
      c * (B * ∫⁻ x, f x ∂σ) + d * ∑ i ∈ I, σ (U i) * energy i := by
  calc
    _ ≤ ∑ i ∈ I, (σ.prod ν) (E i) := measure_biUnion_finset_le _ _
    _ = ∑ i ∈ I, σ (U i) * ((normalizedRestrict σ (U i)).prod ν) (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (measure_mul_normalizedRestrict_prod σ ν (hU i hi) (hE i hi)).symm
    _ ≤ ∑ i ∈ I, σ (U i) *
        (c * (∫⁻ x, f x ∂normalizedRestrict σ (U i)) + d * energy i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : σ (U i) = 0
      · simp only [hz, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (hlocal i hi hz)
    _ = c * (∑ i ∈ I, σ (U i) * ∫⁻ x, f x ∂normalizedRestrict σ (U i)) +
        d * ∑ i ∈ I, σ (U i) * energy i := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul' le_rfl (sum_weighted_conditional_moment_le σ I U hU B hB f)) le_rfl

/-- A common conditional energy bound leaves only the total original mass. -/
theorem prod_biUnion_le_uniform_conditional_deletion {ι : Type*}
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [SFinite ν]
    (I : Finset ι) (U : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (E : ι → Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hU : ∀ i ∈ I, MeasurableSet (U i))
    (hE : ∀ i ∈ I, E i ⊆ U i ×ˢ univ) (B : ℕ)
    (hB : ∀ x, (I.filter (fun i ↦ x ∈ U i)).card ≤ B)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (c d energy : ℝ≥0∞)
    (hlocal : ∀ i ∈ I, σ (U i) ≠ 0 →
      ((normalizedRestrict σ (U i)).prod ν) (E i) ≤
        c * (∫⁻ x, f x ∂normalizedRestrict σ (U i)) + d * energy) :
    (σ.prod ν) (⋃ i ∈ I, E i) ≤
      (B : ℝ≥0∞) * (c * (∫⁻ x, f x ∂σ) + d * energy * σ univ) := by
  apply (prod_biUnion_le_conditional_deletion σ ν I U E hU hE B hB
    f c d (fun _ ↦ energy) hlocal).trans
  rw [← Finset.sum_mul]
  have hm := sum_measure_le_mul_of_multiplicity σ I U MeasurableSet.univ hU
    (fun _ _ ↦ subset_univ _) B hB
  calc
    _ ≤ c * (B * ∫⁻ x, f x ∂σ) + d * (B * σ univ * energy) := by gcongr
    _ = _ := by ring

/-- For the actual enlarged dyadic parents, the only spatial summation loss is quadratic
in the enlargement. The source in the radial moment is unchanged in every conditional law. -/
theorem prod_biUnion_enlargedGrid_le_conditional_deletion
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [SFinite ν]
    {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t) (I : Finset (Fin 2 → ℤ))
    (E : (Fin 2 → ℤ) → Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (hE : ∀ Q ∈ I, E Q ⊆ enlargedGridSquare a t Q ×ˢ univ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (c d energy : ℝ≥0∞)
    (hlocal : ∀ Q ∈ I, σ (enlargedGridSquare a t Q) ≠ 0 →
      ((normalizedRestrict σ (enlargedGridSquare a t Q)).prod ν) (E Q) ≤
        c * (∫⁻ x, f x ∂normalizedRestrict σ (enlargedGridSquare a t Q)) + d * energy) :
    (σ.prod ν) (⋃ Q ∈ I, E Q) ≤
      ENNReal.ofReal (49 * t ^ 2) *
        (c * (∫⁻ x, f x ∂σ) + d * energy * σ univ) := by
  have hb : (((2 * ⌈t⌉₊ + 3) ^ 2 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (49 * t ^ 2) := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ t by linarith)
    have hnon : 0 ≤ 2 * (⌈t⌉₊ : ℝ) + 3 := by positivity
    have hu : 2 * (⌈t⌉₊ : ℝ) + 3 ≤ 7 * t := by linarith
    have hr : (((2 * ⌈t⌉₊ + 3) ^ 2 : ℕ) : ℝ) ≤ 49 * t ^ 2 := by
      push_cast
      nlinarith [sq_le_sq₀ hnon (by positivity : 0 ≤ 7 * t) |>.mpr hu]
    exact_mod_cast ENNReal.ofReal_le_ofReal hr
  exact (prod_biUnion_le_uniform_conditional_deletion σ ν I (enlargedGridSquare a t) E
    (fun _ _ ↦ measurableSet_enlargedGridSquare _ _ _) hE _
    (card_enlargedGridSquare_overlap_le ha I) f c d energy hlocal).trans
      (mul_le_mul' hb le_rfl)

/-- Actual physical bad pairs are carried by their enlarged parent in the pin variable. -/
theorem physicalBadPacketPairs_subset_parent
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (hn : Antitone n)
    (s t K : ℕ) {L : ℝ} (hL : 1 ≤ L) (H : ℕ → ℝ≥0∞)
    (X : Set (EuclideanSpace ℝ (Fin 2))) (j : ℕ) (P : Fin 2 → ℤ) (w C D : ℝ) :
    physicalBadPacketPairs σ n e s t K L H X j P w C D ⊆
      enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P ×ˢ univ := by
  rintro ⟨y, x⟩ ⟨Q, c, k, hparent, _, _, hy, _⟩
  refine ⟨?_, mem_univ _⟩
  have hp := mem_physicalDyadicParent hn hL hy
  simpa only [physicalDyadicParent, hparent] using hp

/-- Summing the literal bad-packet pair sets keeps the actual common radial moment and
costs only the enlarged-parent overlap. The conditional bound is the one supplied by the
finite-grid deletion theorem and the regular conditional-energy estimate. -/
theorem prod_biUnion_physicalBadPacketPairs_le
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [SFinite ν]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (H : ℕ → ℝ≥0∞) (X : Set (EuclideanSpace ℝ (Fin 2)))
    (j : ℕ) (I : Finset (Fin 2 → ℤ)) (w C D q : ℝ) (c d energy : ℝ≥0∞)
    (hlocal : ∀ P ∈ I,
      σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P) ≠ 0 →
      ((normalizedRestrict σ
        (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
          (L ^ (2 * (j + 1) + 2)) P)).prod ν)
        (physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
      c * (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure
        ∂normalizedRestrict σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
          (L ^ (2 * (j + 1) + 2)) P)) + d * energy) :
    (σ.prod ν) (⋃ P ∈ I, physicalBadPacketPairs σ n e s t K L H X j P w C D) ≤
      ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) *
        (c * (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂σ) +
          d * energy * σ univ) := by
  apply prod_biUnion_enlargedGrid_le_conditional_deletion σ ν
    (by positivity) (one_le_pow₀ hL) I
    (fun P ↦ physicalBadPacketPairs σ n e s t K L H X j P w C D)
    (fun P _ ↦ physicalBadPacketPairs_subset_parent σ n e hn s t K hL H X j P w C D)
    (fun y ↦ ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure) c d energy
    hlocal

/-- Disjoint component regions have overlap at most one, even on their boundaries. -/
theorem card_mem_disjoint_components_le_one {α ι : Type*} (I : Finset ι)
    (V : ι → Set α) (hV : Set.PairwiseDisjoint (I : Set ι) V) (x : α) :
    (I.filter (fun i ↦ x ∈ V i)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi, hxi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hxj⟩ := Finset.mem_filter.mp hj
  by_contra hne
  exact Set.disjoint_left.mp (hV hi hj hne) hxi hxj

/-- Original regular-component masses exactly recover the global moment, up to discarded
mass. There is no inverse component mass and no number-of-components factor. -/
theorem sum_weighted_disjoint_component_moment_le {ι : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (I : Finset ι) (V : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hV : ∀ i ∈ I, MeasurableSet (V i)) (hdisj : Set.PairwiseDisjoint (I : Set ι) V)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∑ i ∈ I, σ (V i) * ∫⁻ x, f x ∂normalizedRestrict σ (V i)) ≤ ∫⁻ x, f x ∂σ := by
  simpa only [Nat.cast_one, one_mul] using
    sum_weighted_conditional_moment_le σ I V hV 1
      (card_mem_disjoint_components_le_one I V hdisj) f

/-- The same component weighting controls both the moment and a common scalar error. -/
theorem sum_weighted_component_deletion_le {ι : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (I : Finset ι) (V : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (hV : ∀ i ∈ I, MeasurableSet (V i)) (hdisj : Set.PairwiseDisjoint (I : Set ι) V)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (c error : ℝ≥0∞) :
    (∑ i ∈ I, σ (V i) *
      (c * (∫⁻ x, f x ∂normalizedRestrict σ (V i)) + error)) ≤
      c * (∫⁻ x, f x ∂σ) + error * σ univ := by
  have hm := sum_weighted_disjoint_component_moment_le σ I V hV hdisj f
  have hw := sum_measure_le_mul_of_multiplicity σ I V MeasurableSet.univ hV
    (fun _ _ ↦ subset_univ _) 1 (card_mem_disjoint_components_le_one I V hdisj)
  simp only [Nat.cast_one, one_mul] at hw
  calc
    _ = c * (∑ i ∈ I, σ (V i) * ∫⁻ x, f x ∂normalizedRestrict σ (V i)) +
        error * (∑ i ∈ I, σ (V i)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hm) (mul_le_mul' le_rfl hw)

end FalconerPacking
