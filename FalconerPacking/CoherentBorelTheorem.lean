/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CoherentCompactTheorem

/-!
# The unconditional coherent branch for Borel planar sets

Borel compact extraction supplies the actual source and pin probabilities. The proved
coherent compact theorem then gives a positive-length pin in the original set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The coherent Hausdorff-packing criterion for arbitrary Borel planar sets. -/
theorem exists_pin_volume_pinnedDistances_pos_of_coherent_cutoff
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ} (hE : MeasurableSet E)
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd₂ : d < 2)
    (hpack : packingDim E < ENNReal.ofReal (2 * d - 1)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  obtain ⟨s, u, K, L, μ, ν, Cμ, Cν, δ, hs, hs₂, _, hu,
    hK, hL, hKE, hLE, hbox, hμK, hνL, hCμ, _, hμ, hν, hδ, hδ₁, hsep⟩ :=
    exists_coherent_compact_data_of_measurableSet hE hdim hd hd₂ hpack
  obtain ⟨y, hyL, hy⟩ := exists_pin_of_compact_frostman_upperBox μ ν hK hL hμK hνL
    hs hs₂.le hCμ hμ hν hbox hu hδ hδ₁ hsep
  exact ⟨y, hLE hyL, hy.trans_le (measure_mono (image_mono hKE))⟩

/-- The entire first interval of the focused theorem is unconditional. -/
theorem exists_pin_volume_pinnedDistances_pos_of_first_interval
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ} (hE : MeasurableSet E)
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd' : d ≤ 5 / 4)
    (hfirst : d ≤ hardGapTransition)
    (hpack : packingDim E < ENNReal.ofReal (hausdorffPackingBound d)) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  rw [hausdorffPackingBound_of_le_hardGapTransition hfirst] at hpack
  exact exists_pin_volume_pinnedDistances_pos_of_coherent_cutoff hE hdim hd
    (by linarith) hpack

end FalconerPacking
