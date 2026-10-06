/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.EnlargedGridSquares
public import FalconerPacking.SelectedCapGridEmbedding
public import FalconerPacking.BallOverlap

/-!
# Actual enlarged-grid mass and normalized energy bounds

Bounded pointwise overlap controls total pin mass even for overlapping enlarged cells.
For normalized Lebesgue averages, their exact area cancels the enlargement-square loss.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal

namespace FalconerPacking

/-- Actual enlarged squares have exactly the area of their side length squared. -/
theorem volume_enlargedGridSquare (a t : ℝ) (Q : Fin 2 → ℤ) :
    volume (enlargedGridSquare a t Q) = ENNReal.ofReal (t * a) ^ 2 :=
  volume_coordinateSquare (gridSquareCenter a Q) (t * a)

/-- The actual finite grid has controlled total mass, independently of the number of cells. -/
theorem sum_measure_enlargedGridSquare_le
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) {a t : ℝ} (ha : 0 < a)
    (I : Finset (Fin 2 → ℤ)) :
    ∑ Q ∈ I, σ (enlargedGridSquare a t Q) ≤
      (((2 * ⌈t⌉₊ + 3) ^ 2 : ℕ) : ℝ≥0∞) * σ univ :=
  sum_measure_le_mul_of_multiplicity σ I (enlargedGridSquare a t) MeasurableSet.univ
    (fun _ _ ↦ measurableSet_enlargedGridSquare _ _ _) (fun _ _ ↦ subset_univ _)
    _ (card_enlargedGridSquare_overlap_le ha I)

/-- The grid overlap is at most forty-nine times the square of an enlargement at least one. -/
theorem sum_measure_enlargedGridSquare_le_real
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t)
    (I : Finset (Fin 2 → ℤ)) :
    ∑ Q ∈ I, σ (enlargedGridSquare a t Q) ≤ ENNReal.ofReal (49 * t ^ 2) * σ univ := by
  let B := (2 * ⌈t⌉₊ + 3) ^ 2
  have hb : (B : ℝ) ≤ 49 * t ^ 2 := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ t by linarith)
    have hnon : 0 ≤ 2 * (⌈t⌉₊ : ℝ) + 3 := by positivity
    have hu : 2 * (⌈t⌉₊ : ℝ) + 3 ≤ 7 * t := by linarith
    dsimp [B]
    push_cast
    nlinarith [sq_le_sq₀ hnon (by positivity : 0 ≤ 7 * t) |>.mpr hu]
  apply (sum_measure_enlargedGridSquare_le σ ha I).trans
  apply mul_le_mul_left
  exact_mod_cast ENNReal.ofReal_le_ofReal hb

/-- Restricting and normalizing a nonnegative integral is bounded by inverse area times
its full-space integral; no support or integrability hypothesis is required. -/
theorem lintegral_normalized_square_le {a t : ℝ} (Q : Fin 2 → ℤ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    (∫⁻ x, f x ∂((volume (enlargedGridSquare a t Q))⁻¹ •
      volume.restrict (enlargedGridSquare a t Q))) ≤
      (ENNReal.ofReal (t * a) ^ 2)⁻¹ * ∫⁻ x, f x := by
  rw [lintegral_smul_measure, volume_enlargedGridSquare, smul_eq_mul]
  gcongr
  exact Measure.restrict_le_self

/-- A uniform global energy bound controls the weighted global error over the whole finite grid. -/
theorem sum_grid_global_energy_le {κ : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t)
    (I : Finset (Fin 2 → ℤ)) (A : Finset κ)
    (f : (Fin 2 → ℤ) → κ → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (G : ℝ≥0∞) (hG : ∀ Q ∈ I, ∑ α ∈ A, ∫⁻ x, f Q α x ≤ G) :
    (∑ Q ∈ I, σ (enlargedGridSquare a t Q) * ∑ α ∈ A, ∫⁻ x, f Q α x) ≤
      ENNReal.ofReal (49 * t ^ 2) * σ univ * G := by
  calc
    _ ≤ ∑ Q ∈ I, σ (enlargedGridSquare a t Q) * G := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact mul_le_mul_right (hG Q hQ) _
    _ = (∑ Q ∈ I, σ (enlargedGridSquare a t Q)) * G := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_left (sum_measure_enlargedGridSquare_le_real σ ha ht I) G

/-- The normalized grid energy costs only the inverse un-enlarged area. -/
theorem sum_grid_local_energy_le {κ : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) {a t : ℝ} (ha : 0 < a) (ht : 1 ≤ t)
    (I : Finset (Fin 2 → ℤ)) (A : Finset κ)
    (f : (Fin 2 → ℤ) → κ → EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (G : ℝ≥0∞) (hG : ∀ Q ∈ I, ∑ α ∈ A, ∫⁻ x, f Q α x ≤ G) :
    (∑ Q ∈ I, ∑ α ∈ A, σ (enlargedGridSquare a t Q) *
      ∫⁻ x, f Q α x ∂((volume (enlargedGridSquare a t Q))⁻¹ •
        volume.restrict (enlargedGridSquare a t Q))) ≤
      ENNReal.ofReal (49 * (a ^ 2)⁻¹) * σ univ * G := by
  have hb : (∑ Q ∈ I, ∑ α ∈ A, σ (enlargedGridSquare a t Q) *
      ∫⁻ x, f Q α x ∂((volume (enlargedGridSquare a t Q))⁻¹ •
        volume.restrict (enlargedGridSquare a t Q))) ≤
      (∑ Q ∈ I, σ (enlargedGridSquare a t Q) *
        ((ENNReal.ofReal (t * a) ^ 2)⁻¹ * G)) := by
    apply Finset.sum_le_sum
    intro Q hQ
    rw [← Finset.mul_sum]
    apply mul_le_mul_right
    calc
      _ ≤ ∑ α ∈ A, (ENNReal.ofReal (t * a) ^ 2)⁻¹ * ∫⁻ x, f Q α x := by
        apply Finset.sum_le_sum
        intro α _
        exact lintegral_normalized_square_le Q _
      _ = _ := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_right (hG Q hQ) _
  apply hb.trans
  rw [← Finset.sum_mul]
  apply (mul_le_mul_left (sum_measure_enlargedGridSquare_le_real σ ha ht I) _).trans_eq
  have ht₀ : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hc : ENNReal.ofReal (49 * t ^ 2) * (ENNReal.ofReal (t * a) ^ 2)⁻¹ =
      ENNReal.ofReal (49 * (a ^ 2)⁻¹) := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc
    _ = (ENNReal.ofReal (49 * t ^ 2) * (ENNReal.ofReal (t * a) ^ 2)⁻¹) * σ univ * G := by ring
    _ = _ := by rw [hc]

end FalconerPacking
