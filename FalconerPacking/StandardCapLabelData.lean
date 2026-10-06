/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CapLabelGeometry
public import FalconerPacking.InheritedFourierLabels

/-!
# Actual circular data with inherited standard-cap labels

Coarse labels sum whole standard caps according to their nominal ancestors. Fine
labels retain the standard cap and split its entire support into angular cells.
The resulting identities hold pointwise, including nominal-cap crossings.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Filter Classical
open scoped FourierTransform Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (S : ℕ) (hS : 0 < S)

/-- The circle data of one actual standard smooth cap. -/
def standardCapData (j : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  smoothAngularCap ψ hψ hzero S hS j ξ * g ξ

/-- Coarse data group entire standard labels by nominal angular ancestors. -/
def coarseStandardCapData (M c : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∑ j ∈ (Finset.range S).filter (fun j ↦ j / M = c),
    standardCapData ψ hψ hzero S hS j g ξ

/-- Fine data split the entire actual standard support, including its portion outside
its nominal interval. The indicator is used only on spectral data. -/
def fineStandardCapData (F : ℕ) (p : ℕ × ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ :=
  circleCellData F p.2 (standardCapData ψ hψ hzero S hS p.1 g)

theorem integrable_standardCapData {r : ℝ} {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (j : ℕ) :
    Integrable (standardCapData ψ hψ hzero S hS j g) (normalizedCircleMeasure r) :=
  hg.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 (smoothAngularCap ψ hψ hzero S hS j))
    (smoothAngularCap ψ hψ hzero S hS j).continuous.aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ SchwartzMap.norm_le_seminorm ℝ _ ξ)

theorem integrable_coarseStandardCapData {r : ℝ} {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (M c : ℕ) :
    Integrable (coarseStandardCapData ψ hψ hzero S hS M c g) (normalizedCircleMeasure r) :=
  integrable_finsetSum _ (fun j _ ↦ integrable_standardCapData ψ hψ hzero S hS hg j)

theorem integrable_fineStandardCapData {r : ℝ} {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (F : ℕ) (p : ℕ × ℕ) :
    Integrable (fineStandardCapData ψ hψ hzero S hS F p g) (normalizedCircleMeasure r) :=
  integrable_circleCellData (integrable_standardCapData ψ hψ hzero S hS hg p.1) F p.2

/-- Fine children reconstruct the whole standard cap, without truncating to its nominal interval. -/
theorem sum_fineStandardCapData_standard {F : ℕ} (hF : 0 < F) (j : ℕ)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ i ∈ Finset.range F, fineStandardCapData ψ hψ hzero S hS F (j, i) g ξ =
      standardCapData ψ hψ hzero S hS j g ξ :=
  sum_circleCellData hF (standardCapData ψ hψ hzero S hS j g) ξ

/-- At fine levels the standard label stays fixed and only the auxiliary cell is coarsened. -/
theorem sum_fineStandardCapData_refinement {M F : ℕ} (hM : 0 < M) (hF : 0 < F)
    (j c : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ i ∈ (Finset.range (M * F)).filter (fun i ↦ i / M = c),
      fineStandardCapData ψ hψ hzero S hS (M * F) (j, i) g ξ =
      fineStandardCapData ψ hψ hzero S hS F (j, c) g ξ :=
  sum_circleCellData_refinement hM hF c (standardCapData ψ hψ hzero S hS j g) ξ

/-- Crossing the standard scale adds only an exact angular regrouping, with no spatial step. -/
theorem sum_fineStandardCapData_coarse {F : ℕ} (hF : 0 < F) (M c : ℕ)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ (Finset.range S).filter (fun j ↦ j / M = c), ∑ i ∈ Finset.range F,
      fineStandardCapData ψ hψ hzero S hS F (j, i) g ξ =
      coarseStandardCapData ψ hψ hzero S hS M c g ξ := by
  simp only [sum_fineStandardCapData_standard ψ hψ hzero S hS hF]
  rfl

/-- A nonzero fine datum automatically belongs to the explicitly filtered geometric label set. -/
theorem mem_fineCapLabels_of_data_ne_zero {F : ℕ} {p : ℕ × ℕ}
    (hpS : p.1 < S) (hpF : p.2 < F) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : fineStandardCapData ψ hψ hzero S hS F p g ξ ≠ 0) : p ∈ fineCapLabels S F := by
  have hc : ξ ∈ circleAngularCell F p.2 := by
    by_contra hn
    exact hξ (indicator_of_notMem hn _)
  have hcap : smoothAngularCap ψ hψ hzero S hS p.1 ξ ≠ 0 := by
    intro he
    apply hξ
    simp only [fineStandardCapData, circleCellData, indicator_of_mem hc, standardCapData,
      he, zero_mul]
  have hne : ξ ≠ 0 := by
    intro he
    apply hcap
    simp [he, hzero.eq_of_nhds]
  have hd := smoothAngularCap_direction_support ψ hψ hzero S hS p.1 hcap
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hpS, Finset.mem_range.mpr hpF⟩, radialAngle ξ 0, hc, ?_⟩
  simpa only [angularDirection_radialAngle hne, sub_zero, mem_ball] using hd

/-- Dropping nonincident pairs loses no data. -/
theorem sum_fineStandardCapData_active_eq {F : ℕ} (hF : 0 < F)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ p ∈ fineCapLabels S F, fineStandardCapData ψ hψ hzero S hS F p g ξ = ψ ξ * g ξ := by
  have he : (∑ p ∈ fineCapLabels S F, fineStandardCapData ψ hψ hzero S hS F p g ξ) =
      ∑ p ∈ (Finset.range S) ×ˢ (Finset.range F),
        fineStandardCapData ψ hψ hzero S hS F p g ξ := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    by_contra hn
    have hp' := Finset.mem_product.mp hp
    exact hnot (mem_fineCapLabels_of_data_ne_zero ψ hψ hzero S hS
      (Finset.mem_range.mp hp'.1) (Finset.mem_range.mp hp'.2) g hn)
  rw [he, Finset.sum_product]
  simp only [sum_fineStandardCapData_standard ψ hψ hzero S hS hF, standardCapData,
    ← Finset.sum_mul]
  congr 1
  simpa only [sum_apply] using congrArg
    (fun f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ ↦ f ξ)
    (sum_smoothAngularCap ψ hψ hzero S hS)

/-- Actual fine multipliers have squared mass bounded by the original multiplier,
with no factor counting standard caps or auxiliary cells. -/
theorem sum_fineStandardCapData_active_norm_sq_le {F : ℕ} (hF : 0 < F)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ p ∈ fineCapLabels S F, ‖fineStandardCapData ψ hψ hzero S hS F p g ξ‖ ^ 2 ≤
      ‖ψ ξ‖ ^ 2 * ‖g ξ‖ ^ 2 := by
  calc
    _ ≤ ∑ p ∈ (Finset.range S) ×ˢ (Finset.range F),
        ‖fineStandardCapData ψ hψ hzero S hS F p g ξ‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
    _ = (∑ j ∈ Finset.range S, ‖smoothAngularCap ψ hψ hzero S hS j ξ‖ ^ 2) * ‖g ξ‖ ^ 2 := by
      rw [Finset.sum_product]
      simp only [fineStandardCapData, sum_circleCellData_norm_sq hF, standardCapData,
        norm_mul, mul_pow, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_norm_sq_smoothAngularCap ψ hψ hzero S hS ξ) (sq_nonneg _)

/-- Exact coarse parent sums preserve whole standard labels. -/
theorem coarseStandardCapData_regroup {L M N : ℕ} (hL : 0 < L)
    (hsize : S = L * (M * N)) (c : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    coarseStandardCapData ψ hψ hzero S hS (L * M) c g ξ =
      ∑ j ∈ (Finset.range (M * N)).filter (fun j ↦ j / M = c),
        coarseStandardCapData ψ hψ hzero S hS L j g ξ := by
  have hlabel : ∀ j ∈ Finset.range S, j / L ∈ Finset.range (M * N) := by
    intro j hj
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hL).mpr
    rw [mul_comm]
    exact hsize ▸ Finset.mem_range.mp hj
  have h := inheritedLabelSum_regroup (Finset.range S) (Finset.range (M * N))
    (fun j ↦ j / L) (fun j ↦ j / M) hlabel c (fun _ ↦ True) (fun _ ↦ True)
    (fun j ↦ standardCapData ψ hψ hzero S hS j g ξ)
  simpa only [inheritedLabelSum, Function.comp_apply, Nat.div_div_eq_div_mul, and_true,
    coarseStandardCapData] using h

end FalconerPacking
