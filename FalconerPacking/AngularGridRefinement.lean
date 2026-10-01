/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleCellSchwartz

/-!
# Exact ancestry of the half-open angular grid

Integral refinements have exact parent sums, including angular endpoints. These
identities concern measurable spectral data and do not differentiate indicators.
-/

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Classical
open scoped FourierTransform

namespace FalconerPacking

/-- Nominal centers lie in the closure of their unique parent interval. -/
theorem angularGridPoint_ancestor_bound {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (j : ℕ) :
    |angularGridPoint (M * N) j - angularGridPoint N (j / M)| ≤ 2 * Real.pi / N := by
  have hlo := angularGridPoint_mono (M * N) (Nat.mul_div_le j M)
  have hindex : j ≤ M * (j / M + 1) := by
    have hm := Nat.mod_lt j hM
    have he := Nat.mod_add_div j M
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hhi := angularGridPoint_mono (M * N) hindex
  rw [angularGridPoint_refinement hM hN] at hlo hhi
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hs := angularGridPoint_step N (j / M)
  linarith

/-- The nominal standard direction stays within its parent's angular width. -/
theorem angularGridDirection_ancestor_bound {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (j : ℕ) :
    dist (angularDirection (angularGridPoint (M * N) j))
      (angularDirection (angularGridPoint N (j / M))) ≤ 2 * Real.pi / N := by
  rw [dist_eq_norm]
  exact (norm_angularDirection_sub_le_angle _ _).trans
    (angularGridPoint_ancestor_bound hM hN j)

/-- Actual cell membership determines exactly the integer-division ancestor. -/
theorem circleAngularCell_parent_eq {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    {j c : ℕ} {ξ : EuclideanSpace ℝ (Fin 2)}
    (hj : ξ ∈ circleAngularCell (M * N) j) (hc : ξ ∈ circleAngularCell N c) :
    j / M = c := by
  by_contra hne
  exact Set.disjoint_left.mp (disjoint_angularGridCell N hne)
    (angularGridCell_refinement_subset hM hN j hj) hc

/-- Summing all children gives exactly the parent indicator, with the endpoint convention retained. -/
theorem sum_circleCellData_refinement {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (c : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ (Finset.range (M * N)).filter (fun j ↦ j / M = c),
      circleCellData (M * N) j g ξ = circleCellData N c g ξ := by
  have hθ := radialAngle_mem ξ 0
  rw [← biUnion_angularGridCell (Nat.mul_pos hM hN)] at hθ
  obtain ⟨j, hj, hξj⟩ := mem_iUnion₂.mp hθ
  change ξ ∈ circleAngularCell (M * N) j at hξj
  by_cases hc : ξ ∈ circleAngularCell N c
  · have hp := circleAngularCell_parent_eq hM hN hξj hc
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_filter.mpr ⟨hj, hp⟩)]
    · simp only [circleCellData, indicator_of_mem hξj, indicator_of_mem hc]
    · intro i hi hij
      have hn : ξ ∉ circleAngularCell (M * N) i := by
        intro hξi
        exact Set.disjoint_left.mp (disjoint_angularGridCell (M * N) hij) hξi hξj
      exact indicator_of_notMem hn g
  · rw [circleCellData, indicator_of_notMem hc]
    apply Finset.sum_eq_zero
    intro i hi
    have hn : ξ ∉ circleAngularCell (M * N) i := by
      intro hξi
      have hp := angularGridCell_refinement_subset hM hN i hξi
      rw [(Finset.mem_filter.mp hi).2] at hp
      exact hc hp
    exact indicator_of_notMem hn g

/-- Circle smoothing and inverse Fourier transformation commute with actual finite data sums. -/
theorem sum_circlePhysicalSchwartz_data {ι : Type*} (I : Finset ι) (r : ℝ)
    (g : ι → EuclideanSpace ℝ (Fin 2) → ℂ)
    (hg : ∀ i, Integrable (g i) (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k) :
    ∑ i ∈ I, circlePhysicalSchwartz r (hg i) k hk =
      circlePhysicalSchwartz r (integrable_finsetSum I (fun i _ ↦ hg i)) k hk := by
  ext x
  simp only [sum_apply, circlePhysicalSchwartz_apply, ← Finset.mul_sum]
  congr 1
  simp only [circleSpectralExtension]
  rw [← integral_finsetSum I (fun i _ ↦
    (hg i).bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun ξ ↦ by simp))]
  apply integral_congr_ae
  exact ae_of_all _ fun ξ ↦ by
    dsimp only
    rw [Finset.mul_sum]

/-- Physical child functions reconstruct their actual angular parent. -/
theorem sum_circleCellPhysicalSchwartz_refinement {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (c : ℕ) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k) :
    ∑ j ∈ (Finset.range (M * N)).filter (fun j ↦ j / M = c),
      circleCellPhysicalSchwartz r hg (M * N) j k hk =
      circleCellPhysicalSchwartz r hg N c k hk := by
  change (∑ j ∈ _, circlePhysicalSchwartz r (integrable_circleCellData hg (M * N) j) k hk) = _
  rw [sum_circlePhysicalSchwartz_data]
  have he : (fun ξ ↦ ∑ j ∈ (Finset.range (M * N)).filter (fun j ↦ j / M = c),
      circleCellData (M * N) j g ξ) = circleCellData N c g :=
    funext (sum_circleCellData_refinement hM hN c g)
  congr 1

end FalconerPacking
