/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AngularGridGeometry
public import FalconerPacking.OverlappingHeavyCells

/-!
# Explicit enlarged angular cells

Enlarging equal cells by one grid step on each side covers every interval of that radius
centered in the original cell. The enlarged family has overlap at most four, so its
heavy-cell deletion estimate remains independent of the grid size.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Classical
open scoped ENNReal

namespace FalconerPacking

/-- Three consecutive grid widths around a half-open cell, with closed endpoints. -/
def enlargedAngularCell (N k : ℕ) : Set ℝ :=
  Icc (angularGridPoint N k - 2 * Real.pi / N)
    (angularGridPoint N k + 2 * (2 * Real.pi / N))

theorem measurableSet_enlargedAngularCell (N k : ℕ) :
    MeasurableSet (enlargedAngularCell N k) := measurableSet_Icc

/-- One enlarged cell covers a whole interval around any direction in its original cell. -/
theorem interval_subset_enlargedAngularCell {N k : ℕ} {θ ε : ℝ}
    (hθ : θ ∈ angularGridCell N k) (hε : ε ≤ 2 * Real.pi / N) :
    Icc (θ - ε) (θ + ε) ⊆ enlargedAngularCell N k := by
  have hs := angularGridPoint_step N k
  intro φ hφ
  constructor <;> linarith [hθ.1, hθ.2, hφ.1, hφ.2]

theorem mem_enlargedAngularCell_of_mem_cell {N k : ℕ} {θ : ℝ}
    (hθ : θ ∈ angularGridCell N k) : θ ∈ enlargedAngularCell N k :=
  interval_subset_enlargedAngularCell hθ (le_refl _)
    ⟨sub_le_self _ (by positivity), le_add_of_nonneg_right (by positivity)⟩

/-- Exact equal spacing gives an overlap bound of four, including closed endpoints. -/
theorem card_enlargedAngularCell_le {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    ((Finset.range N).filter (fun k ↦ θ ∈ enlargedAngularCell N k)).card ≤ 4 := by
  let I := (Finset.range N).filter (fun k ↦ θ ∈ enlargedAngularCell N k)
  by_cases hI : I.Nonempty
  · let m := I.min' hI
    have hm : m ∈ I := Finset.min'_mem I hI
    have hδ : 0 < 2 * Real.pi / N := by positivity
    have hsub : I ⊆ Finset.Icc m (m + 3) := by
      intro k hk
      refine Finset.mem_Icc.mpr ⟨Finset.min'_le I k hk, ?_⟩
      have hkθ := (Finset.mem_filter.mp hk).2
      have hmθ := (Finset.mem_filter.mp hm).2
      change -Real.pi + (2 * Real.pi / N) * k - 2 * Real.pi / N ≤ θ ∧ _ at hkθ
      change _ ∧ θ ≤ -Real.pi + (2 * Real.pi / N) * m +
        2 * (2 * Real.pi / N) at hmθ
      have hreal : (k : ℝ) ≤ m + 3 := by nlinarith [hkθ.1, hmθ.2]
      exact_mod_cast hreal
    exact (Finset.card_le_card hsub).trans_eq (by simp; omega)
  · change I.card ≤ 4
    rw [Finset.not_nonempty_iff_eq_empty.mp hI]
    norm_num

/-- The angular reference mass of each enlarged cell is at most three grid widths. -/
theorem radialAngularMeasure_enlargedAngularCell_le (N k : ℕ) :
    radialAngularMeasure (enlargedAngularCell N k) ≤
      ENNReal.ofReal (3 * (2 * Real.pi / N)) := by
  calc
    _ ≤ volume (enlargedAngularCell N k) := Measure.restrict_le_self _
    _ = _ := by
      rw [enlargedAngularCell, Real.volume_Icc]
      congr 1
      ring

/-- Every angular direction admits a cell covering its prescribed small neighborhood. -/
theorem exists_enlargedAngularCell_cover {N : ℕ} (hN : 0 < N) {θ ε : ℝ}
    (hθ : θ ∈ Ioc (-Real.pi) Real.pi) (hε : ε ≤ 2 * Real.pi / N) :
    ∃ k ∈ Finset.range N, Icc (θ - ε) (θ + ε) ⊆ enlargedAngularCell N k := by
  rw [← biUnion_angularGridCell hN] at hθ
  obtain ⟨k, hk, hθ⟩ := mem_iUnion₂.mp hθ
  exact ⟨k, hk, interval_subset_enlargedAngularCell hθ hε⟩

/-- These actual enlarged cells have a source-pair deletion cost independent of N. -/
theorem prod_enlarged_radialHeavyCells_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (hac : ∀ᵐ x ∂μ, ν.map (radialAngle x) ≪ radialAngularMeasure)
    {N : ℕ} (hN : 0 < N)
    {A : ℝ≥0∞} {q : ℝ} (hA : A ≠ 0) (hAt : A ≠ ∞) (hq : 1 ≤ q) :
    μ.prod ν (radialHeavyCellPairs ν (Finset.range N) (enlargedAngularCell N) (2 * A)) ≤
      8 * A ^ (1 - q) *
        ∫⁻ x, ∫⁻ θ, radialProjectionDensity ν x θ ^ q ∂radialAngularMeasure ∂μ := by
  simpa only [Nat.cast_ofNat, show (2 : ℝ≥0∞) * 4 = 8 by norm_num] using
    prod_radialHeavyCellPairs_le_of_overlap μ ν hac (Finset.range N)
      (enlargedAngularCell N) 4 (card_enlargedAngularCell_le hN)
      (fun _ _ ↦ measurableSet_enlargedAngularCell _ _) hA hAt hq

end FalconerPacking
