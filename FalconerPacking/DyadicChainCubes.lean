/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dyadic

/-!
# The actual finite spatial family of a dyadic chain

At every level we take the ancestors of the prescribed initial finite collection.
The next collection is exactly the parent image, so summing over its fibers counts
each current cube once, irrespective of overlapping enlarged squares.
-/

noncomputable section

open Classical

namespace FalconerPacking

/-- Actual spatial ancestors of an initial finite collection. -/
def dyadicChainCubes (n : ℕ → ℕ) (I : Finset (Fin 2 → ℤ)) (j : ℕ) :
    Finset (Fin 2 → ℤ) := I.image (ancestor (n 0 - n j))

@[simp]
theorem dyadicChainCubes_zero (n : ℕ → ℕ) (I : Finset (Fin 2 → ℤ)) :
    dyadicChainCubes n I 0 = I := by
  have h : ancestor 0 = id := by funext Q; exact ancestor_zero Q
  simp only [dyadicChainCubes, Nat.sub_self, h, Finset.image_id]

/-- Two successive ancestor maps compose exactly along the decreasing depth sequence. -/
theorem dyadicChainCubes_ancestor_eq {n : ℕ → ℕ} (hn : Antitone n)
    (j : ℕ) (Q : Fin 2 → ℤ) :
    ancestor (n j - n (j + 1)) (ancestor (n 0 - n j) Q) =
      ancestor (n 0 - n (j + 1)) Q := by
  rw [ancestor_ancestor]
  have h₀ : n j ≤ n 0 := hn (Nat.zero_le j)
  have h₁ : n (j + 1) ≤ n j := hn (Nat.le_succ j)
  have he : n j - n (j + 1) + (n 0 - n j) = n 0 - n (j + 1) := by omega
  rw [he]

/-- The constructed next family is exactly the parent image of the current one. -/
theorem dyadicChainCubes_succ {n : ℕ → ℕ} (hn : Antitone n)
    (I : Finset (Fin 2 → ℤ)) (j : ℕ) :
    dyadicChainCubes n I (j + 1) =
      (dyadicChainCubes n I j).image (ancestor (n j - n (j + 1))) := by
  simp only [dyadicChainCubes, Finset.image_image]
  congr 1
  funext Q
  exact (dyadicChainCubes_ancestor_eq hn j Q).symm

/-- Every actual child has a parent in the next constructed finite family. -/
theorem dyadicChainCubes_parent_mem {n : ℕ → ℕ} (hn : Antitone n)
    {I : Finset (Fin 2 → ℤ)} {j : ℕ} {Q : Fin 2 → ℤ}
    (hQ : Q ∈ dyadicChainCubes n I j) :
    ancestor (n j - n (j + 1)) Q ∈ dyadicChainCubes n I (j + 1) := by
  rw [dyadicChainCubes_succ hn]
  exact Finset.mem_image.mpr ⟨Q, hQ, rfl⟩

/-- Spatial fiber summation is exact, without an enlarged-square overlap loss. -/
theorem sum_dyadicChainCubes_fibers {V : Type*} [AddCommMonoid V]
    {n : ℕ → ℕ} (hn : Antitone n) (I : Finset (Fin 2 → ℤ)) (j : ℕ)
    (f : (Fin 2 → ℤ) → V) :
    (∑ P ∈ dyadicChainCubes n I (j + 1),
      ∑ Q ∈ (dyadicChainCubes n I j).filter
        (fun Q ↦ ancestor (n j - n (j + 1)) Q = P), f Q) =
      ∑ Q ∈ dyadicChainCubes n I j, f Q := by
  exact Finset.sum_fiberwise_of_maps_to (fun Q hQ ↦ dyadicChainCubes_parent_mem hn hQ) f

end FalconerPacking
