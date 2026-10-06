/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.MarkedDyadicCircle
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Uniform square sums for arbitrary inherited cap multipliers

Nonnegative cap weights and disjoint auxiliary cells bound the total absolute multiplier
amplitude. Arbitrary deletions and grouping cannot increase this bound, so no number of
labels or parent cubes enters the circle-energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap
open scoped Topology

namespace FalconerPacking

/-- Grouping and deletion do not increase the sum of absolute amplitudes. -/
theorem sum_norm_inheritedLabelSum_le {ι κ : Type*}
    (I : Finset ι) (A : Finset κ) (label : ι → κ) (keep : ι → Prop) (v : ι → ℂ) :
    ∑ α ∈ A, ‖inheritedLabelSum I label α keep v‖ ≤ ∑ i ∈ I, ‖v i‖ := by
  calc
    _ ≤ ∑ α ∈ A, ∑ i ∈ I.filter (fun i ↦ label i = α), ‖v i‖ := by
      apply Finset.sum_le_sum
      intro α _
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi ↦ Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,
          (Finset.mem_filter.mp hi).2.1⟩) (fun _ _ _ ↦ norm_nonneg _)
    _ = ∑ i ∈ I.filter (fun i ↦ label i ∈ A), ‖v i‖ :=
      Finset.sum_fiberwise_eq_sum_filter I A label (fun i ↦ ‖v i‖)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ norm_nonneg _)

/-- Disjoint angular cells conserve the sum of absolute amplitudes exactly. -/
theorem sum_norm_circleCellData {N : ℕ} (hN : 0 < N)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ i ∈ Finset.range N, ‖circleCellData N i g ξ‖ = ‖g ξ‖ := by
  have hθ := radialAngle_mem ξ 0
  rw [← biUnion_angularGridCell hN] at hθ
  obtain ⟨j, hj, hθ⟩ := mem_iUnion₂.mp hθ
  rw [Finset.sum_eq_single_of_mem j hj]
  · rw [circleCellData, indicator_of_mem (show ξ ∈ circleAngularCell N j from hθ)]
  · intro i hi hij
    have hnot : ξ ∉ circleAngularCell N i := fun hθi ↦
      Set.disjoint_left.mp (disjoint_angularGridCell N hij) hθi hθ
    simp only [circleCellData, indicator_of_notMem hnot, norm_zero]

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (S : ℕ) (hS : 0 < S)

/-- The actual inherited multiplier before multiplying by the common source spectrum. -/
def inheritedCapMultiplier {κ : Type*} (T : ℕ) (label : ℕ × ℕ → κ)
    (keep : ℕ × ℕ → Prop) (α : κ) (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  inheritedLabelSum (fineCapLabels S T) label α keep
    (fun p ↦ circleCellData T p.2 (smoothAngularCap ψ hψ hzero S hS p.1) ξ)

/-- Every actual inherited multiplier is measurable despite its sharp auxiliary cells. -/
theorem measurable_inheritedCapMultiplier {κ : Type*} (T : ℕ) (label : ℕ × ℕ → κ)
    (keep : ℕ × ℕ → Prop) (α : κ) :
    Measurable (inheritedCapMultiplier ψ hψ hzero S hS T label keep α) := by
  apply Finset.measurable_sum
  intro p _
  exact measurable_circleCellData (smoothAngularCap ψ hψ hzero S hS p.1).continuous.measurable T p.2

/-- The total absolute amplitude is bounded by the original annular multiplier, for arbitrary marks. -/
theorem sum_norm_inheritedCapMultiplier_le {κ : Type*} {T : ℕ} (hT : 0 < T)
    (A : Finset κ) (label : ℕ × ℕ → κ) (keep : ℕ × ℕ → Prop)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ α ∈ A, ‖inheritedCapMultiplier ψ hψ hzero S hS T label keep α ξ‖ ≤ ‖ψ ξ‖ := by
  apply (sum_norm_inheritedLabelSum_le _ A label keep _).trans
  calc
    _ ≤ ∑ p ∈ (Finset.range S) ×ˢ (Finset.range T),
        ‖circleCellData T p.2 (smoothAngularCap ψ hψ hzero S hS p.1) ξ‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ ↦ norm_nonneg _)
    _ = _ := by
      rw [Finset.sum_product]
      simp_rw [sum_norm_circleCellData hT]
      exact sum_norm_smoothAngularCap ψ hψ hzero S hS ξ

/-- The square-sum bound is uniform in the terminal depth, labels, and surviving subset. -/
theorem sum_norm_sq_inheritedCapMultiplier_le {κ : Type*} {T : ℕ} (hT : 0 < T)
    (A : Finset κ) (label : ℕ × ℕ → κ) (keep : ℕ × ℕ → Prop)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ α ∈ A, ‖inheritedCapMultiplier ψ hψ hzero S hS T label keep α ξ‖ ^ 2 ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2 := by
  apply (Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)).trans
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
    ((sum_norm_inheritedCapMultiplier_le ψ hψ hzero S hS hT A label keep ξ).trans
      (SchwartzMap.norm_le_seminorm ℝ ψ ξ)) 2

/-- Multiplying the actual inherited multiplier by a common spectrum commutes with its finite sums. -/
theorem inheritedCapMultiplier_mul {κ : Type*} (T : ℕ) (label : ℕ × ℕ → κ)
    (keep : ℕ × ℕ → Prop) (α : κ) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    inheritedCapMultiplier ψ hψ hzero S hS T label keep α ξ * g ξ =
      inheritedLabelSum (fineCapLabels S T) label α keep
        (fun p ↦ fineStandardCapData ψ hψ hzero S hS T p g ξ) := by
  unfold inheritedCapMultiplier inheritedLabelSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hξ : ξ ∈ circleAngularCell T p.2 <;>
    simp only [fineStandardCapData, standardCapData, circleCellData,
      indicator_apply, hξ, ↓reduceIte, zero_mul]

end FalconerPacking
