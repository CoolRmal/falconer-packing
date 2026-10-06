/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedCapEnergySums
public import FalconerPacking.EnlargedGridSquares
public import FalconerPacking.Dyadic

/-!
# Geometry of the measures used in the selected-cap embedding

Inverse images of unit grid cells are actual oriented rectangles. The Euclidean support
margin controls the anisotropic norm, including arbitrary aspect ratios.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Classical
open scoped ENNReal

namespace FalconerPacking

/-- Inverse-image unit grid cells lie in translates of the dual spatial rectangle. -/
theorem orientedDilation_preimage_unitCube_subset
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (k : Fin 2 → ℤ) :
    (orientedRectangleDilation O a b ha hb) ⁻¹' dyadicCube 0 k ⊆
      frameRectangle O
        ((orientedRectangleDilation O a b ha hb).symm (gridSquareCenter 1 k)) a b := by
  intro x hx
  let A := orientedRectangleDilation O a b ha hb
  have hcoord (i : Fin 2) : |(A (x - A.symm (gridSquareCenter 1 k))) i| ≤ 1 / 2 := by
    have hi := hx i
    change (k i : ℝ) ≤ 2 ^ 0 * (A x) i ∧ 2 ^ 0 * (A x) i < (k i : ℝ) + 1 at hi
    simp only [pow_zero, one_mul] at hi
    rw [map_sub, A.apply_symm_apply]
    change |(A x) i - 1 * ((k i : ℝ) + 1 / 2)| ≤ 1 / 2
    apply abs_le.mpr
    constructor <;> linarith [hi.1, hi.2]
  have h₀ := hcoord 0
  have h₁ := hcoord 1
  change |(O (x - A.symm (gridSquareCenter 1 k))) 0| ≤ a ∧
    |(O (x - A.symm (gridSquareCenter 1 k))) 1| ≤ b
  rw [orientedRectangleDilation_apply_zero, abs_div, abs_of_pos ha] at h₀
  rw [orientedRectangleDilation_apply_one, abs_div, abs_of_pos hb] at h₁
  exact ⟨((div_le_iff₀ ha).mp h₀).trans (by linarith),
    ((div_le_iff₀ hb).mp h₁).trans (by linarith)⟩

/-- The long spatial width controls Euclidean displacement by anisotropic displacement. -/
theorem norm_le_twice_width_mul_orientedDilation
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖x‖ ≤ 2 * b * ‖orientedRectangleDilation O a b ha (ha.trans_le hab) x‖ := by
  let A := orientedRectangleDilation O a b ha (ha.trans_le hab)
  have h₀ := PiLp.norm_apply_le (A x) 0
  have h₁ := PiLp.norm_apply_le (A x) 1
  rw [Real.norm_eq_abs, orientedRectangleDilation_apply_zero, abs_div, abs_of_pos ha] at h₀
  rw [Real.norm_eq_abs, orientedRectangleDilation_apply_one, abs_div,
    abs_of_pos (ha.trans_le hab)] at h₁
  have hc₀ := (div_le_iff₀ ha).mp h₀
  have hc₁ := (div_le_iff₀ (ha.trans_le hab)).mp h₁
  have hh := norm_le_frame_coordinate_sum O x
  have hw := mul_le_mul_of_nonneg_left hab (norm_nonneg (A x))
  dsimp only [A] at *
  nlinarith

/-- Ball localization requires only a harmless factor two in the parent support margin. -/
theorem embedding_ball_parent_margin_powers {L : ℝ} (hL : 8 ≤ L) (j : ℕ) :
    1 + 2 * L ^ (2 * j + 3) + 2 * L ≤ L ^ (2 * j + 4) := by
  have hL₁ : 1 ≤ L := by linarith
  have ht : L ≤ L ^ (2 * j + 3) := le_self_pow₀ hL₁ (by omega)
  rw [show 2 * j + 4 = (2 * j + 3) + 1 by omega, pow_succ L (2 * j + 3)]
  nlinarith

/-- Renormalizing all averaging components by their common mass is an exact measure identity. -/
theorem selectedCapMeasure_eq_smul_normalized {α ι κ : Type*} [MeasurableSpace α]
    (I : Finset ι) (selection : ι → Finset κ) (w : ι → ℝ≥0∞)
    (μ : ι → Measure α) (θ : κ) {V : ℝ≥0∞} (hV₀ : V ≠ 0) (hVtop : V ≠ ∞) :
    selectedCapMeasure I selection w μ θ =
      V • selectedCapMeasure I selection w (fun i ↦ V⁻¹ • μ i) θ := by
  simp only [selectedCapMeasure, selectedAveragingMeasure, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [mul_left_comm, ENNReal.mul_inv_cancel hV₀ hVtop, mul_one]

/-- A common component-mass bound controls every selected cap measure. -/
theorem selectedCapMeasure_univ_le {α ι κ : Type*} [MeasurableSpace α]
    (I : Finset ι) (selection : ι → Finset κ) (w : ι → ℝ≥0∞)
    (μ : ι → Measure α) (θ : κ) (W : ℝ≥0∞)
    (hmass : ∀ i ∈ I, μ i univ ≤ W) :
    selectedCapMeasure I selection w μ θ univ ≤ W * ∑ i ∈ I, w i := by
  rw [selectedCapMeasure, selectedAveragingMeasure, Measure.finsetSum_apply]
  calc
    _ ≤ ∑ i ∈ I with θ ∈ selection i, w i * W := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [Measure.smul_apply, smul_eq_mul] using
        mul_le_mul_right (hmass i (Finset.mem_filter.mp hi).1) (w i)
    _ ≤ ∑ i ∈ I, w i * W := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Almost-everywhere properties of the retained components pass to their selected sum. -/
theorem ae_selectedCapMeasure {α ι κ : Type*} [MeasurableSpace α]
    (I : Finset ι) (selection : ι → Finset κ) (w : ι → ℝ≥0∞)
    (μ : ι → Measure α) (θ : κ) {p : α → Prop}
    (hp : ∀ i ∈ I, θ ∈ selection i → ∀ᵐ x ∂μ i, p x) :
    ∀ᵐ x ∂selectedCapMeasure I selection w μ θ, p x := by
  rw [ae_iff, selectedCapMeasure, selectedAveragingMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hn := ae_iff.mp (hp i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
  simp only [Measure.smul_apply, hn, smul_zero]

/-- Selected tube tests control unnormalized averaging components of any common finite mass.
This includes the localized volume restrictions used by local Fourier orthogonality. -/
theorem selectedCapMeasure_frameRectangle_le {ι κ : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (I : Finset ι)
    (selection : ι → Finset κ) (θ : κ)
    (E S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (q : ι → EuclideanSpace ℝ (Fin 2))
    (μ : ι → Measure (EuclideanSpace ℝ (Fin 2)))
    (O V : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (P : Set (EuclideanSpace ℝ (Fin 2)))
    {a b t C₀ D : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 1 ≤ t) (hC : 0 ≤ C₀)
    (hD : (5 + 7 * C₀) * t ≤ D) (Λ : ℕ) (A W : ℝ≥0∞)
    (hW₀ : W ≠ 0) (hWtop : W ≠ ∞)
    (hframe : ∀ y i, |(V y) i - (O y) i| ≤ C₀ * (a / b) * ‖y‖)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) (hP : MeasurableSet P)
    (hsub : ∀ i ∈ I, E i ⊆ P)
    (hover : ∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ)
    (hEball : ∀ i ∈ I, ∀ x ∈ E i, ‖x - q i‖ ≤ t * a)
    (hSball : ∀ i ∈ I, ∀ x ∈ S i, ‖x - q i‖ ≤ t * a)
    (hmass : ∀ i ∈ I, μ i univ ≤ W) (hsupport : ∀ i ∈ I, μ i (S i)ᶜ = 0)
    (htest : ∀ i ∈ I, θ ∈ selection i →
      σ (frameRectangle V (q i) (D * a) (D * b) ∩ P) ≤ A)
    (c : EuclideanSpace ℝ (Fin 2)) :
    selectedCapMeasure I selection (fun i ↦ σ (E i)) μ θ (frameRectangle O c a b) ≤
      W * (Λ * A) := by
  rw [selectedCapMeasure_eq_smul_normalized I selection (fun i ↦ σ (E i)) μ θ hW₀ hWtop,
    Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul_right
  apply selectedAveragingMeasure_frameRectangle_le σ
    (I.filter fun i ↦ θ ∈ selection i) E S q (fun i ↦ W⁻¹ • μ i)
    O V P ha hab ht hC hD Λ A hframe
    (fun i hi ↦ hE i (Finset.mem_filter.mp hi).1) hP
    (fun i hi ↦ hsub i (Finset.mem_filter.mp hi).1) ?_
    (fun i hi ↦ hEball i (Finset.mem_filter.mp hi).1)
    (fun i hi ↦ hSball i (Finset.mem_filter.mp hi).1) ?_ ?_
    (fun i hi ↦ htest i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2) c
  · intro x
    exact (Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.filter_subset _ _))).trans (hover x)
  · intro i hi
    rw [Measure.smul_apply, smul_eq_mul]
    exact (mul_le_mul_right (hmass i (Finset.mem_filter.mp hi).1) _).trans_eq
      (ENNReal.inv_mul_cancel hW₀ hWtop)
  · intro i hi
    simp [Measure.smul_apply, hsupport i (Finset.mem_filter.mp hi).1]

end FalconerPacking
