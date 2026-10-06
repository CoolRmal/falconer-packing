/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CoherentBorelTheorem
public import FalconerPacking.HardGapBorelData
public import FalconerPacking.RegularAnnularComponents

/-!
# The Hausdorff-packing criterion for a positive-length self-pinned distance set

The coherent range is already proved by positive affine approximations. Outside that range,
the actual compact regular-shell theorem applies to the extracted source and pin measures.
The common isometry preserves pinned distances and returns the pin to the original Borel set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Theorem 1.1 of the focused proof: the strict Hausdorff-packing condition supplies a pin
inside the original Borel set whose distance set has positive Lebesgue measure. -/
theorem exists_pin_volume_pinnedDistances_pos (E : Set (EuclideanSpace ℝ (Fin 2))) (d : ℝ)
    (hE : MeasurableSet E) (hdimH : dimH E = ENNReal.ofReal d)
    (hd_lt : 1 < d) (hd_le : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (hausdorffPackingBound d)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  by_cases hcoherent : packingDim E < ENNReal.ofReal (2 * d - 1)
  · exact exists_pin_volume_pinnedDistances_pos_of_coherent_cutoff hE hdimH hd_lt
      (by linarith) hcoherent
  obtain ⟨s, u, X, Y, μ, ν, f, q₀, Cμ, Cν, δ, R, q, hs, hs', hu, hu', hX, hY,
    hXE, hYE, hroot, hbox, hμX, hνY, hCμ, hCν, hfrμ, hfrν, hδ, hR,
    hXR, hYR, hsep, hq, hac, hmoment⟩ :=
    exists_hardGap_borel_measure_data hE hdimH hd_lt hd_le hpack hcoherent
  have hpin := (pinnedDistance_absolutelyContinuous_of_compact_regular_shells μ ν
    hs hs' hu hu' hX hY hroot hbox hμX hνY hCμ hCν hfrμ hfrν hδ hR hXR hYR
    hsep hq hac hmoment).2
  have hmass : 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) X := by
    rw [probabilityMeasure_apply_eq_one_of_compl_eq_zero μ hX.measurableSet hμX]
    exact zero_lt_one
  obtain ⟨y, hyY, hy⟩ := exists_mem_volume_pinnedDistances_pos_of_ae ν hmass hνY hpin
  obtain ⟨z, hz, rfl⟩ := hYE hyY
  refine ⟨z, hz, ?_⟩
  rw [← pinnedDistances_image_isometryEquiv E z f]
  exact hy.trans_le (measure_mono (image_mono hXE))

end FalconerPacking
