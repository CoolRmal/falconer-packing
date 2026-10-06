/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedTubeWeights
public import FalconerPacking.OrientedReproducingKernel

/-!
# Geometric containment for selected tube tests

Rectangles below are specified by their half-widths. The proof allows a change of frame
of order a/b, and keeps the transverse and longitudinal bounds separate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open Classical

namespace FalconerPacking

/-- A closed rectangle centered at c, with half-widths a and b in the frame O. -/
def frameRectangle
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | |(O (x - c)) 0| ≤ a ∧ |(O (x - c)) 1| ≤ b}

/-- Every frame rectangle is measurable. -/
theorem measurableSet_frameRectangle
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (c : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) : MeasurableSet (frameRectangle O c a b) := by
  have h₀ : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ |(O (x - c)) 0|) := by
    fun_prop
  have h₁ : Continuous (fun x : EuclideanSpace ℝ (Fin 2) ↦ |(O (x - c)) 1|) := by
    fun_prop
  exact (isClosed_le h₀ continuous_const).measurableSet.inter
    (isClosed_le h₁ continuous_const).measurableSet

/-- The Euclidean norm is bounded by the sum of the absolute frame coordinates. -/
theorem norm_le_frame_coordinate_sum
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ≤ |(O x) 0| + |(O x) 1| := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 ↦ ℝ) (O x)
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, O.norm_map] at h
  nlinarith [norm_nonneg x, abs_nonneg ((O x) 0), abs_nonneg ((O x) 1),
    mul_nonneg (abs_nonneg ((O x) 0)) (abs_nonneg ((O x) 1))]

/-- Coordinate bounds for two points in one rectangle. -/
theorem frameRectangle_sub_bounds
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {c z z₀ : EuclideanSpace ℝ (Fin 2)} {a b : ℝ}
    (hz : z ∈ frameRectangle O c a b) (hz₀ : z₀ ∈ frameRectangle O c a b) :
    |(O (z - z₀)) 0| ≤ 2 * a ∧ |(O (z - z₀)) 1| ≤ 2 * b := by
  have heq : z - z₀ = (z - c) - (z₀ - c) := by abel
  change |(O (z - c)) 0| ≤ a ∧ |(O (z - c)) 1| ≤ b at hz
  change |(O (z₀ - c)) 0| ≤ a ∧ |(O (z₀ - c)) 1| ≤ b at hz₀
  rw [heq, map_sub]
  constructor
  · apply (abs_sub _ _).trans
    change |(O (z - c)) 0| + |(O (z₀ - c)) 0| ≤ 2 * a
    linarith [hz.1, hz₀.1]
  · apply (abs_sub _ _).trans
    change |(O (z - c)) 1| + |(O (z₀ - c)) 1| ≤ 2 * b
    linarith [hz.2, hz₀.2]

/-- The coordinate form of the small angular mismatch follows from nearby frame vectors. -/
theorem frame_mismatch_of_coordinate_vectors
    (O V : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (u v : Fin 2 → EuclideanSpace ℝ (Fin 2)) {ε : ℝ}
    (hO : ∀ x i, (O x) i = ⟪x, u i⟫)
    (hV : ∀ x i, (V x) i = ⟪x, v i⟫)
    (huv : ∀ i, ‖v i - u i‖ ≤ ε) :
    ∀ x i, |(V x) i - (O x) i| ≤ ε * ‖x‖ := by
  intro x i
  rw [hO, hV, ← inner_sub_right]
  exact (abs_real_inner_le_norm x (v i - u i)).trans
    (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left (huv i) (norm_nonneg x))

/-- All enlarged children meeting one dual rectangle fit inside a tube centered at any
one of them, even after a frame mismatch of size C₀a/b. -/
theorem mem_frameRectangle_of_common_intersections
    (O V : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {a b t C₀ : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 1 ≤ t) (hC : 0 ≤ C₀)
    (hframe : ∀ y i, |(V y) i - (O y) i| ≤ C₀ * (a / b) * ‖y‖)
    {c q q₀ x z z₀ : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x - q‖ ≤ t * a) (hzq : ‖z - q‖ ≤ t * a)
    (hz₀q : ‖z₀ - q₀‖ ≤ t * a)
    (hz : z ∈ frameRectangle O c a b) (hz₀ : z₀ ∈ frameRectangle O c a b) :
    x ∈ frameRectangle V q₀ ((5 + 7 * C₀) * t * a) ((5 + 7 * C₀) * t * b) := by
  have hb : 0 < b := ha.trans_le hab
  have ht₀ : 0 ≤ t := le_trans (by norm_num) ht
  let e := (x - q) + (q - z) + (z₀ - q₀)
  have he : ‖e‖ ≤ 3 * t * a := by
    have hqz : ‖q - z‖ ≤ t * a := by simpa only [norm_sub_rev] using hzq
    calc
      ‖e‖ ≤ ‖x - q‖ + ‖q - z‖ + ‖z₀ - q₀‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ _ := by linarith
  have hdecomp : x - q₀ = e + (z - z₀) := by dsimp [e]; abel
  obtain ⟨hz₀, hz₁⟩ := frameRectangle_sub_bounds O hz hz₀
  have hc (i : Fin 2) : |(O e) i| ≤ 3 * t * a := by
    have hi := PiLp.norm_apply_le (O e) i
    simpa only [Real.norm_eq_abs, O.norm_map] using hi.trans (by simpa using he)
  have hcoord₀ : |(O (x - q₀)) 0| ≤ 3 * t * a + 2 * a := by
    rw [hdecomp, map_add]
    exact (abs_add_le _ _).trans (add_le_add (hc 0) hz₀)
  have hcoord₁ : |(O (x - q₀)) 1| ≤ 3 * t * a + 2 * b := by
    rw [hdecomp, map_add]
    exact (abs_add_le _ _).trans (add_le_add (hc 1) hz₁)
  have hnorm : ‖x - q₀‖ ≤ 3 * t * a + 4 * b := by
    have hzNorm := norm_le_frame_coordinate_sum O (z - z₀)
    rw [hdecomp]
    exact (norm_add_le _ _).trans (by linarith)
  have herror : C₀ * (a / b) * ‖x - q₀‖ ≤ 7 * C₀ * t * a := by
    calc
      _ ≤ C₀ * (a / b) * (3 * t * a + 4 * b) := by gcongr
      _ = 3 * C₀ * t * a * (a / b) + 4 * C₀ * a := by field_simp
      _ ≤ 3 * C₀ * t * a + 4 * C₀ * a := by
        apply add_le_add_left
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          ((div_le_one hb).mpr hab) (show 0 ≤ 3 * C₀ * t * a by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht (mul_nonneg hC ha.le)]
  have hVcoord (i : Fin 2) : |(V (x - q₀)) i| ≤
      |(O (x - q₀)) i| + 7 * C₀ * t * a := by
    calc
      _ ≤ |(O (x - q₀)) i| + |(V (x - q₀)) i - (O (x - q₀)) i| := by
        simpa only [add_sub_cancel] using abs_add_le ((O (x - q₀)) i)
          ((V (x - q₀)) i - (O (x - q₀)) i)
      _ ≤ _ := add_le_add le_rfl ((hframe _ i).trans herror)
  constructor
  · nlinarith [hVcoord 0, mul_le_mul_of_nonneg_right ht ha.le]
  · have hta : t * a ≤ t * b := mul_le_mul_of_nonneg_left hab ht₀
    have hCa : 7 * C₀ * t * a ≤ 7 * C₀ * t * b := by gcongr
    nlinarith [hVcoord 1, mul_le_mul_of_nonneg_right ht hb.le]

/-- An axis-parallel closed square of side r lies in the closed ball of radius r
around its center. The same statement holds in every orthonormal frame. -/
theorem frameRectangle_square_norm_le
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {q x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hx : x ∈ frameRectangle O q (r / 2) (r / 2)) : ‖x - q‖ ≤ r := by
  have h := norm_le_frame_coordinate_sum O (x - q)
  linarith [hx.1, hx.2]

/-- The tested rectangles at the selected centers control the mass of every translate
of the dual rectangle. The geometric containment is proved, rather than assumed. -/
theorem selectedAveragingMeasure_frameRectangle_le {ι : Type*}
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (I : Finset ι)
    (E S : ι → Set (EuclideanSpace ℝ (Fin 2)))
    (q : ι → EuclideanSpace ℝ (Fin 2))
    (μ : ι → Measure (EuclideanSpace ℝ (Fin 2)))
    (O V : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (P : Set (EuclideanSpace ℝ (Fin 2)))
    {a b t C₀ D : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 1 ≤ t) (hC : 0 ≤ C₀)
    (hD : (5 + 7 * C₀) * t ≤ D) (Λ : ℕ) (A : ℝ≥0∞)
    (hframe : ∀ y i, |(V y) i - (O y) i| ≤ C₀ * (a / b) * ‖y‖)
    (hE : ∀ i ∈ I, MeasurableSet (E i)) (hP : MeasurableSet P)
    (hsub : ∀ i ∈ I, E i ⊆ P)
    (hover : ∀ x, (I.filter fun i ↦ x ∈ E i).card ≤ Λ)
    (hEball : ∀ i ∈ I, ∀ x ∈ E i, ‖x - q i‖ ≤ t * a)
    (hSball : ∀ i ∈ I, ∀ x ∈ S i, ‖x - q i‖ ≤ t * a)
    (hmass : ∀ i ∈ I, μ i univ ≤ 1) (hsupport : ∀ i ∈ I, μ i (S i)ᶜ = 0)
    (htest : ∀ i ∈ I, σ (frameRectangle V (q i) (D * a) (D * b) ∩ P) ≤ A)
    (c : EuclideanSpace ℝ (Fin 2)) :
    selectedAveragingMeasure I (fun i ↦ σ (E i)) μ (frameRectangle O c a b) ≤ Λ * A := by
  apply selectedAveragingMeasure_le_of_tube_tests σ I E S
    (fun i ↦ frameRectangle V (q i) (D * a) (D * b)) μ P
    (frameRectangle O c a b) Λ A hE hP
    (fun i _ ↦ measurableSet_frameRectangle V (q i) (D * a) (D * b))
    hsub hover hmass hsupport htest
  intro i hi hiU j hj hjU x hx
  obtain ⟨z₀, hz₀S, hz₀U⟩ := hiU
  obtain ⟨z, hzS, hzU⟩ := hjU
  have h := mem_frameRectangle_of_common_intersections O V ha hab ht hC hframe
    (hEball j hj x hx) (hSball j hj z hzS) (hSball i hi z₀ hz₀S) hzU hz₀U
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hD ha.le),
    h.2.trans (mul_le_mul_of_nonneg_right hD (ha.trans_le hab).le)⟩

end FalconerPacking
