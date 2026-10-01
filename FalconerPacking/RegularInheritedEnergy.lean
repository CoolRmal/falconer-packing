/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InheritedShellDecay

/-!
# Actual regular-component energies at every inherited parent

Positive initial cells force positive mass in each ancestor core. Regularity therefore supplies
the literal energy bound needed by the inherited deleted-shell theorem, including padded edges.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Regularity discharges every conditional-energy input in the inherited deletion theorem.
Equal consecutive levels are allowed, so fixed-length padded chains require no special case. -/
theorem regular_component_inherited_parent_energy
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    {T N : ℕ} (hT : 0 < T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (he : ∀ j < N, e j ≤ 2 * T)
    (hA : ν (finiteDyadicUnion (T * N) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict ν (finiteDyadicUnion (T * N) A)).real
        (dyadicCube (T * N) k)) (ancestor T) N e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * N) x = ancestor (T * N) y)
    (ℓ : ℕ → ℕ) (hℓ : Antitone ℓ) (hℓN : ℓ 0 ≤ N)
    (I : Finset (Fin 2 → ℤ))
    (hI : ∀ Q ∈ I, 0 < (normalizedRestrict ν (finiteDyadicUnion (T * N) A))
      (dyadicCube (T * ℓ 0) Q)) {L : ℝ} (hL : 1 ≤ L) (j : ℕ)
    {P : Fin 2 → ℤ} (hP : P ∈ I.image (ancestor (T * ℓ 0 - T * ℓ (j + 1)))) :
    let σ := normalizedRestrict ν (finiteDyadicUnion (T * N) A)
    let U := enlargedGridSquare ((2 : ℝ) ^ (T * ℓ (j + 1)))⁻¹
      (L ^ (2 * (j + 1) + 2)) P
    truncEnergy (normalizedRestrict σ U)
      (dyadicRadius (T * ℓ j)) (dyadicRadius (T * ℓ (j + 1))) ≤
        4 * (ℓ j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
          (3 * (N : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T N e)
            (ℓ (j + 1)) (ℓ j)) := by
  dsimp only
  have hj : ℓ (j + 1) ≤ ℓ j := hℓ (by omega)
  have hjN : ℓ j ≤ N := (hℓ (Nat.zero_le j)).trans hℓN
  have hcore : 0 < (normalizedRestrict ν (finiteDyadicUnion (T * N) A))
      (dyadicCube (T * ℓ (j + 1)) P) := by
    obtain ⟨Q, hQI, rfl⟩ := Finset.mem_image.mp hP
    apply (hI Q hQI).trans_le
    apply measure_mono
    have hlev : T * ℓ (j + 1) ≤ T * ℓ 0 :=
      Nat.mul_le_mul_left T (hℓ (Nat.zero_le (j + 1)))
    have hc := dyadicCube_subset_ancestor (T * ℓ (j + 1))
      (T * ℓ 0 - T * ℓ (j + 1)) Q
    rwa [Nat.add_sub_of_le hlev] at hc
  exact normalized_regular_conditional_energy_le_edgeCost ν hT he hA hreg hroot
    hj hjN hcore (measurableSet_enlargedGridSquare _ _ _)
    (dyadicCube_subset_enlargedGridSquare P (one_le_pow₀ hL))

end FalconerPacking
