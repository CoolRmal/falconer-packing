/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RegularPartitionInitialLoss

/-!
# The actual discarded pin mass in annular coordinates

The complement of the finite component union is the same set discarded by finite
regularization. Its real mass bound converts to the extended nonnegative bound used
by the joint density criterion, with the exact complete-annulus decay exponent.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The regularization remainder is the actual uncovered pin set in the gluing theorem. -/
theorem regular_partition_discarded_mass_le
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (F : Finset (Finset (Fin 2 → ℤ))) (J T k : ℕ) (θ : ℝ)
    (hrem : ν.real (finiteDyadicUnion (T * (4 * J * k)) (F.biUnion id))ᶜ ≤
      (2 : ℝ) ^ (-(θ * T * (4 * J * k : ℕ)))) :
    ν (⋃ A ∈ F, finiteDyadicUnion (T * (4 * J * k)) A)ᶜ ≤
      (2 : ℝ≥0∞) ^ (-(4 * (J * T) * θ) * k) := by
  have hunion : finiteDyadicUnion (T * (4 * J * k)) (F.biUnion id) =
      ⋃ A ∈ F, finiteDyadicUnion (T * (4 * J * k)) A := by
    ext x
    simp [mem_finiteDyadicUnion_iff, Finset.mem_biUnion]
  rw [← hunion]
  have h := ENNReal.ofReal_le_ofReal hrem
  rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top ν _)] at h
  apply h.trans_eq
  rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_ofNat]
  congr 1
  push_cast
  ring

end FalconerPacking
