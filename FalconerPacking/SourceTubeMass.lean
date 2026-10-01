/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.EnlargedAngularCells
import FalconerPacking.StripRadialContainment
import FalconerPacking.WitnessedTubeDeletion

/-!
# Source-tube mass from actual geometry and a retained pair

Positive coordinate separation gives a common angular chart. The proved strip geometry
then places the entire source tube in one enlarged angular cell. A retained witness
therefore bounds its mass, which is precisely the hypothesis needed for heavy-pin deletion.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Actual strip geometry turns a single retained pair into a bound for the whole source tube. -/
theorem source_tube_mass_le_of_retained_pair
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {n c y x₀ : EuclideanSpace ℝ (Fin 2)} {R w δ : ℝ}
    (hn : ‖n‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hyR : ‖y‖ ≤ R) (hSR : ∀ x ∈ S, ‖x‖ ≤ R)
    (hSδ : ∀ x ∈ S, δ ≤ (y - x) 0)
    (hy : |⟪n, y - c⟫| ≤ w) (hS : ∀ x ∈ S, |⟪n, x - c⟫| ≤ w)
    (hx₀ : x₀ ∈ S) {N : ℕ} (hN : 0 < N)
    (hwidth : 8 * R * w / δ ^ 2 ≤ 2 * Real.pi / N)
    (hac : ν.map (radialAngle y) ≪ radialAngularMeasure)
    (A : ℝ≥0∞)
    (hpair : (y, x₀) ∉ radialHeavyCellPairs ν
      (Finset.range N) (enlargedAngularCell N) A) :
    ν S ≤ A * ENNReal.ofReal (3 * (2 * Real.pi / N)) := by
  have hR : 0 ≤ R := (norm_nonneg y).trans hyR
  have hε : 0 ≤ 8 * R * w / δ ^ 2 := by positivity
  obtain ⟨k, hk, hcover⟩ := exists_enlargedAngularCell_cover hN (radialAngle_mem y x₀) hwidth
  have himage := radialAngle_image_subset_interval_of_common_strip hn hw hδ hyR
    hSR hSδ hy hS hx₀
  have hsub : S ⊆ radialAngle y ⁻¹' enlargedAngularCell N k :=
    fun x hx ↦ hcover (himage ⟨x, hx, rfl⟩)
  have hθ : radialAngle y x₀ ∈ enlargedAngularCell N k :=
    hcover ⟨sub_le_self _ hε, le_add_of_nonneg_right hε⟩
  exact (source_mass_le_of_retained_cell_witness ν (Finset.range N)
    (enlargedAngularCell N) A hac hpair hk (measurableSet_enlargedAngularCell N k)
    hθ S hsub).trans (mul_le_mul_right (radialAngularMeasure_enlargedAngularCell_le N k) A)

/-- The retained heavy-pin estimate follows from geometric strip assumptions alone,
without assuming a source mass bound for the associated tubes. -/
theorem prod_retained_heavy_tubes_of_common_strips {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (T S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (n c : ι → EuclideanSpace ℝ (Fin 2)) {R w δ : ℝ}
    (hn : ∀ i ∈ I, ‖n i‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hTR : ∀ i ∈ I, ∀ y ∈ T i, ‖y‖ ≤ R)
    (hSR : ∀ i ∈ I, ∀ x ∈ S i, ‖x‖ ≤ R)
    (hsep : ∀ i ∈ I, ∀ y ∈ T i, ∀ x ∈ S i, δ ≤ (y - x) 0)
    (hTstrip : ∀ i ∈ I, ∀ y ∈ T i, |⟪n i, y - c i⟫| ≤ w)
    (hSstrip : ∀ i ∈ I, ∀ x ∈ S i, |⟪n i, x - c i⟫| ≤ w)
    (hac : ∀ᵐ y ∂μ, ν.map (radialAngle y) ≪ radialAngularMeasure)
    {N : ℕ} (hN : 0 < N) (hwidth : 8 * R * w / δ ^ 2 ≤ 2 * Real.pi / N)
    (A : ℝ≥0∞) {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞) :
    (μ.prod ν) ((⋃ i ∈ I.filter (fun i ↦ a < μ (T i)), T i ×ˢ S i) \
      radialHeavyCellPairs ν (Finset.range N) (enlargedAngularCell N) A) ≤
      ((A * ENNReal.ofReal (3 * (2 * Real.pi / N))) / a) *
        ∑ i ∈ I, μ (T i) ^ 2 := by
  let P := {y | ¬ν.map (radialAngle y) ≪ radialAngularMeasure}
  have hP : μ P = 0 := ae_iff.mp hac
  apply prod_retained_heavy_tubes_le_outside_null_pins μ ν I T S _ P hP ha hat
  intro i hi hretained
  obtain ⟨⟨y, x⟩, ⟨⟨hy, hyP⟩, hx⟩, hpair⟩ := hretained
  have hyac : ν.map (radialAngle y) ≪ radialAngularMeasure := by simpa only [P,
    mem_setOf_eq, not_not] using hyP
  exact source_tube_mass_le_of_retained_pair ν (hn i hi) hw hδ
    (hTR i hi y hy) (hSR i hi) (hsep i hi y hy)
    (hTstrip i hi y hy) (hSstrip i hi) hx hN hwidth hyac A hpair

/-- Source-heavy deletion and retained heavy-pin deletion have independent, additive costs.
Every source mass used here is obtained from the actual strip geometry. -/
theorem prod_all_heavy_tubes_of_common_strips {ι : Type*}
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (I : Finset ι) (T S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (n c : ι → EuclideanSpace ℝ (Fin 2)) {R w δ : ℝ}
    (hn : ∀ i ∈ I, ‖n i‖ = 1) (hw : 0 ≤ w) (hδ : 0 < δ)
    (hTR : ∀ i ∈ I, ∀ y ∈ T i, ‖y‖ ≤ R)
    (hSR : ∀ i ∈ I, ∀ x ∈ S i, ‖x‖ ≤ R)
    (hsep : ∀ i ∈ I, ∀ y ∈ T i, ∀ x ∈ S i, δ ≤ (y - x) 0)
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
    (prod_retained_heavy_tubes_of_common_strips μ ν I T S n c hn hw hδ hTR hSR
      hsep hTstrip hSstrip hac hN hwidth (2 * A) ha hat))

end FalconerPacking
