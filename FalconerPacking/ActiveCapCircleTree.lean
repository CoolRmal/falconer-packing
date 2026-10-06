/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.StandardCapCircleSchwartz

/-!
# Exact parent sums on the active circular label tree

Discarding geometrically nonincident cap-cell pairs changes no Schwartz function.
The actual finite label sets therefore have exact parent sums both within the fine
grid and across the standard scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Filter Classical
open scoped FourierTransform Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (S : ℕ) (hS : 0 < S) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)

/-- A nonincident pair gives the zero physical Schwartz function exactly. -/
theorem fineCapCircleSchwartz_eq_zero_of_notMem {F : ℕ} {p : ℕ × ℕ}
    (hpS : p.1 < S) (hpF : p.2 < F) (hp : p ∉ fineCapLabels S F) :
    fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p = 0 := by
  have he (ξ : EuclideanSpace ℝ (Fin 2)) :
      fineStandardCapData ψ hψ hzero S hS F p g ξ = 0 := by
    by_contra hn
    exact hp (mem_fineCapLabels_of_data_ne_zero ψ hψ hzero S hS hpS hpF g hn)
  ext x
  simp only [fineCapCircleSchwartz, circleCellPhysicalSchwartz,
    circlePhysicalSchwartz_apply, zero_apply]
  change (𝓕⁻ k) x * circleSpectralExtension r
    (fineStandardCapData ψ hψ hzero S hS F p g) x = 0
  simp only [circleSpectralExtension, he, mul_zero, integral_zero]

/-- Crossing the standard scale uses exactly the active fine-label set and the nominal
standard ancestor map. No data outside nominal standard intervals are discarded. -/
theorem sum_active_fineCapCircleSchwartz_coarse {F : ℕ} (hF : 0 < F) (M c : ℕ) :
    ∑ p ∈ (fineCapLabels S F).filter (fun p ↦ p.1 / M = c),
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p =
      coarseCapCircleSchwartz ψ hψ hzero S hS r hg k hk M c := by
  let J := ((Finset.range S).filter (fun j ↦ j / M = c)) ×ˢ (Finset.range F)
  have hsub : (fineCapLabels S F).filter (fun p ↦ p.1 / M = c) ⊆ J := by
    intro p hp
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp hp
    have hindex := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hindex.1, hc⟩, hindex.2⟩
  have he : (∑ p ∈ (fineCapLabels S F).filter (fun p ↦ p.1 / M = c),
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p) =
      ∑ p ∈ J, fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    have hi := Finset.mem_product.mp hp
    have hc := (Finset.mem_filter.mp hi.1).2
    apply fineCapCircleSchwartz_eq_zero_of_notMem ψ hψ hzero S hS r hg k hk
      (Finset.mem_range.mp (Finset.mem_filter.mp hi.1).1) (Finset.mem_range.mp hi.2)
    intro hmem
    exact hnot (Finset.mem_filter.mpr ⟨hmem, hc⟩)
  rw [he]
  dsimp only [J]
  rw [Finset.sum_product]
  exact sum_fineCapCircleSchwartz_coarse ψ hψ hzero S hS r hg k hk hF M c

/-- Actual fine parents have exactly their active fine children, with the standard
label unchanged and the half-open endpoint convention preserved. -/
theorem sum_active_fineCapCircleSchwartz_refinement {M F : ℕ}
    (hM : 0 < M) (hF : 0 < F) {j : ℕ} (hj : j < S) (c : ℕ) :
    ∑ p ∈ (fineCapLabels S (M * F)).filter (fun p ↦ p.1 = j ∧ p.2 / M = c),
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F) p =
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F (j, c) := by
  let J := ({j} : Finset ℕ) ×ˢ ((Finset.range (M * F)).filter (fun i ↦ i / M = c))
  have hsub : (fineCapLabels S (M * F)).filter (fun p ↦ p.1 = j ∧ p.2 / M = c) ⊆ J := by
    intro p hp
    obtain ⟨hp, hj', hc⟩ := Finset.mem_filter.mp hp
    have hi := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hj', Finset.mem_filter.mpr ⟨hi.2, hc⟩⟩
  have he : (∑ p ∈ (fineCapLabels S (M * F)).filter (fun p ↦ p.1 = j ∧ p.2 / M = c),
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F) p) =
      ∑ p ∈ J, fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F) p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    have hi := Finset.mem_product.mp hp
    have hj' := Finset.mem_singleton.mp hi.1
    have hc := (Finset.mem_filter.mp hi.2).2
    apply fineCapCircleSchwartz_eq_zero_of_notMem ψ hψ hzero S hS r hg k hk
      (hj' ▸ hj) (Finset.mem_range.mp (Finset.mem_filter.mp hi.2).1)
    intro hmem
    exact hnot (Finset.mem_filter.mpr ⟨hmem, hj', hc⟩)
  rw [he]
  dsimp only [J]
  rw [Finset.sum_product, Finset.sum_singleton]
  exact sum_fineCapCircleSchwartz_refinement ψ hψ hzero S hS r hg k hk hM hF j c

end FalconerPacking
