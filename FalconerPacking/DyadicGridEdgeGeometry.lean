/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dyadic
import FalconerPacking.EnlargedGridSquares

/-!
# Actual dyadic centers in a spatial inflation edge

The child centers and enlarged parent squares used by the selected-cap estimate are
identified with the actual dyadic hierarchy, rather than supplied as geometric assumptions.
-/

noncomputable section

open Set Classical

namespace FalconerPacking

/-- The grid-square center lies in its actual dyadic cell. -/
theorem gridSquareCenter_mem_dyadicCube (n : ℕ) (Q : Fin 2 → ℤ) :
    gridSquareCenter ((2 : ℝ) ^ n)⁻¹ Q ∈ dyadicCube n Q := by
  intro i
  change (Q i : ℝ) ≤ 2 ^ n * (((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2)) ∧
    2 ^ n * (((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2)) < (Q i : ℝ) + 1
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  constructor <;> linarith

/-- Every point of a dyadic cell is coordinatewise within half its side length of its center. -/
theorem coordinate_sub_gridSquareCenter_le {n : ℕ} {Q : Fin 2 → ℤ}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ dyadicCube n Q) (i : Fin 2) :
    |x i - (gridSquareCenter ((2 : ℝ) ^ n)⁻¹ Q) i| ≤ ((2 : ℝ) ^ n)⁻¹ / 2 := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  change |x i - ((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2)| ≤ ((2 : ℝ) ^ n)⁻¹ / 2
  apply (mul_le_mul_iff_right₀ hp).mp
  have ha : (2 : ℝ) ^ n * |x i - ((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2)| =
      |2 ^ n * (x i - ((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2))| := by
    rw [abs_mul, abs_of_pos hp]
  rw [ha]
  have he : 2 ^ n * (x i - ((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2)) =
      2 ^ n * x i - ((Q i : ℝ) + 1 / 2) := by
    rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
  rw [he]
  have he' : (2 : ℝ) ^ n * (((2 : ℝ) ^ n)⁻¹ / 2) = 1 / 2 := by
    rw [← mul_div_assoc, mul_inv_cancel₀ hp.ne']
  rw [he', abs_le]
  have h := hx i
  constructor <;> linarith

/-- A dyadic cell lies in every concentric enlargement by a factor at least one. -/
theorem dyadicCube_subset_enlargedGridSquare {n : ℕ} (Q : Fin 2 → ℤ) {t : ℝ}
    (ht : 1 ≤ t) : dyadicCube n Q ⊆ enlargedGridSquare ((2 : ℝ) ^ n)⁻¹ t Q := by
  intro x hx
  apply (mem_enlargedGridSquare_iff _ _ _ _).mpr
  intro i
  have h := coordinate_sub_gridSquareCenter_le hx i
  change |x i - ((2 : ℝ) ^ n)⁻¹ * ((Q i : ℝ) + 1 / 2)| ≤ _ at h
  exact h.trans (by nlinarith [inv_pos.mpr (by positivity : (0 : ℝ) < 2 ^ n)])

/-- The child center satisfies the actual parent-center condition of an inflation edge. -/
theorem dyadic_child_center_parent_bound {m n : ℕ} (hmn : m ≤ n)
    (Q : Fin 2 → ℤ) (i : Fin 2) :
    |(gridSquareCenter ((2 : ℝ) ^ n)⁻¹ Q) i -
      (gridSquareCenter ((2 : ℝ) ^ m)⁻¹ (ancestor (n - m) Q)) i| ≤
        ((2 : ℝ) ^ m)⁻¹ / 2 := by
  apply coordinate_sub_gridSquareCenter_le
  apply dyadicCube_subset_ancestor m (n - m) Q
  simpa only [Nat.add_sub_of_le hmn] using gridSquareCenter_mem_dyadicCube n Q

/-- The parent's enlargement at the next level is exactly the one used in the edge estimate. -/
theorem enlargedGridSquare_next_level (b L : ℝ) (j : ℕ) (P : Fin 2 → ℤ) :
    enlargedGridSquare b (L ^ (2 * (j + 1) + 2)) P =
      frameRectangle (LinearIsometryEquiv.refl ℝ _) (gridSquareCenter b P)
        (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2) := by
  have he : 2 * (j + 1) + 2 = 2 * j + 4 := by omega
  simp only [enlargedGridSquare, he]

end FalconerPacking
