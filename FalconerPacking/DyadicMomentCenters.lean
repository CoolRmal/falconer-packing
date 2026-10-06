/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.MomentCenters
public import FalconerPacking.DyadicCenters

/-!
# A fixed dyadic family with controlled moments

The centers lie in one prescribed full-measure set and satisfy both the cube geometry and
the mass-weighted moment estimate at every finite level.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Almost every source point belongs to a positive-mass cube at each fixed generation. -/
theorem ae_measure_dyadicCube_pos (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ) :
    ∀ᵐ x ∂μ, 0 < μ (dyadicCube n (cubeIndex n x)) := by
  have hnull : ∀ k : Fin 2 → ℤ, ∀ᵐ x ∂μ, μ (dyadicCube n k) = 0 →
      x ∉ dyadicCube n k := by
    intro k
    by_cases hk : μ (dyadicCube n k) = 0
    · have hx : ∀ᵐ x ∂μ, x ∉ dyadicCube n k := by
        simpa only [ae_iff, not_not, setOf_mem_eq] using hk
      filter_upwards [hx] with x hx
      exact fun _ ↦ hx
    · exact Filter.Eventually.of_forall fun _ h ↦ (hk h).elim
  filter_upwards [ae_all_iff.mpr hnull] with x hx
  exact pos_iff_ne_zero.mpr fun h ↦ hx (cubeIndex n x) h (mem_dyadicCube_cubeIndex n x)

/-- Select one center in every positive-mass cube, simultaneously at all generations. -/
theorem exists_dyadic_moment_centers
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {G : Set (EuclideanSpace ℝ (Fin 2))}
    {M : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hG : μ Gᶜ = 0)
    (hM : AEMeasurable M μ) :
    ∃ c : ℕ → (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2),
      (∀ n k, 0 < μ (dyadicCube n k) → c n k ∈ dyadicCube n k ∩ G) ∧
      (∀ n k, μ (dyadicCube n k) * M (c n k) ≤ ∫⁻ z in dyadicCube n k, M z ∂μ) ∧
      (∀ n (I : Finset (Fin 2 → ℤ)),
        ∑ k ∈ I, μ (dyadicCube n k) * M (c n k) ≤ ∫⁻ z, M z ∂μ) ∧
      (∀ n, Measurable (dyadicCenterMap n (c n))) ∧
      ∀ n, ∀ᵐ x ∂μ, dyadicCenterMap n (c n) x ∈ G ∧
        dist x (dyadicCenterMap n (c n) x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  obtain ⟨c, hc⟩ := exists_moment_centers μ
    (fun i : ℕ × (Fin 2 → ℤ) ↦ dyadicCube i.1 i.2) hG hM
  let pt := fun n k ↦ c (n, k)
  have hpt (n : ℕ) (k : Fin 2 → ℤ) :
      μ (dyadicCube n k) * M (pt n k) ≤ ∫⁻ z in dyadicCube n k, M z ∂μ := by
    by_cases hk : 0 < μ (dyadicCube n k)
    · exact (hc (n, k) hk).2
    · have hz : μ (dyadicCube n k) = 0 := le_antisymm (le_of_not_gt hk) bot_le
      simp only [hz, zero_mul, zero_le]
  refine ⟨pt, fun n k hk ↦ (hc (n, k) hk).1, hpt, ?_,
    fun n ↦ measurable_dyadicCenterMap n (pt n), ?_⟩
  · intro n I
    apply sum_mul_moment_le_lintegral μ (dyadicCube n) (pt n) M I
      (fun k _ ↦ measurableSet_dyadicCube n k)
    · exact fun _ _ _ _ hne ↦ dyadicCube_disjoint hne
    · exact fun k _ ↦ hpt n k
  · intro n
    filter_upwards [ae_measure_dyadicCube_pos μ n] with x hx
    have hcenter := (hc (n, cubeIndex n x) hx).1
    exact ⟨hcenter.2, dist_le_of_mem_dyadicCube
      (mem_dyadicCube_cubeIndex n x) hcenter.1⟩

end FalconerPacking
