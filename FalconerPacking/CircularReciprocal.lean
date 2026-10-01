import FalconerPacking.CircularPhase
import FalconerPacking.RegularizedReciprocal
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# A quantitative reciprocal for the circular phase

The reciprocal is constructed globally, agrees with the inverse phase derivative on
nonstationary arcs, and has uniform derivative bounds proved by Faà di Bruno's formula.
-/

open Set Function Finset MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- A globally smooth regularization of the inverse derivative of the actual circular phase. -/
noncomputable def circularReciprocal (γ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ → ℝ :=
  scaledRegularizedReciprocal γ ∘ deriv (circularPhase z)

theorem contDiff_circularReciprocal (γ : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ∞ (circularReciprocal γ z) :=
  (contDiff_scaledRegularizedReciprocal γ).comp (contDiff_deriv_circularPhase z)

theorem circularReciprocal_mul_deriv_eq_one (z : EuclideanSpace ℝ (Fin 2))
    {γ θ : ℝ} (hγ : 0 < γ) (hθ : γ ≤ |deriv (circularPhase z) θ|) :
    circularReciprocal γ z θ * deriv (circularPhase z) θ = 1 :=
  scaledRegularizedReciprocal_mul_eq_one hγ hθ

theorem circularReciprocal_mul_deriv_eq_one_of_transverse
    (z : EuclideanSpace ℝ (Fin 2)) {γ θ θ₀ δ : ℝ} (hγ : 0 < γ)
    (htrans : γ + ‖z‖ * δ ≤ |⟪z, angularDirection (θ₀ + Real.pi / 2)⟫|)
    (hθ : |θ - θ₀| ≤ δ) :
    circularReciprocal γ z θ * deriv (circularPhase z) θ = 1 :=
  circularReciprocal_mul_deriv_eq_one z hγ
    (le_abs_deriv_circularPhase_of_transverse z htrans hθ)

/-- A finite combinatorial bound for all Faà di Bruno sums through order `N`. -/
noncomputable def circularReciprocalPartitionBound (N : ℕ) : ℝ :=
  1 + ∑ k ∈ range (N + 1), (Fintype.card (OrderedFinpartition k) : ℝ)

theorem circularReciprocalPartitionBound_pos (N : ℕ) :
    0 < circularReciprocalPartitionBound N := by
  unfold circularReciprocalPartitionBound
  positivity

theorem card_orderedFinpartition_le_circularReciprocalPartitionBound
    {k N : ℕ} (hk : k ≤ N) :
    (Fintype.card (OrderedFinpartition k) : ℝ) ≤ circularReciprocalPartitionBound N := by
  have h := single_le_sum
    (fun j (_ : j ∈ range (N + 1)) ↦
      (show 0 ≤ (Fintype.card (OrderedFinpartition j) : ℝ) by positivity))
    (show k ∈ range (N + 1) from Finset.mem_range.mpr (by omega))
  unfold circularReciprocalPartitionBound
  linarith

/-- This constant depends only on the order and the spatial radius, never on the angular scales. -/
noncomputable def circularReciprocalDerivativeBound (N : ℕ) (R : ℝ) : ℝ :=
  circularReciprocalPartitionBound N * regularizedReciprocalOrderBound N * (max 1 R) ^ N

theorem circularReciprocalDerivativeBound_pos (N : ℕ) (R : ℝ) :
    0 < circularReciprocalDerivativeBound N R := by
  have h₁ := circularReciprocalPartitionBound_pos N
  have h₂ := regularizedReciprocalOrderBound_pos N
  unfold circularReciprocalDerivativeBound
  positivity

/-- All derivatives of the constructed circular reciprocal have a uniform inverse-scale bound. -/
theorem norm_iteratedDeriv_circularReciprocal_le
    (z : EuclideanSpace ℝ (Fin 2)) {γ R : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1)
    (hz : ‖z‖ ≤ R) {k N : ℕ} (hk : k ≤ N) (θ : ℝ) :
    ‖iteratedDeriv k (circularReciprocal γ z) θ‖ ≤
      circularReciprocalDerivativeBound N R * γ⁻¹ ^ (k + 1) := by
  have hγinv : 1 ≤ γ⁻¹ := (one_le_inv₀ hγ).mpr hγ₁
  have hR : 1 ≤ max 1 R := le_max_left _ _
  have hC : 0 ≤ regularizedReciprocalOrderBound N :=
    (regularizedReciprocalOrderBound_pos N).le
  change ‖iteratedDeriv k (scaledRegularizedReciprocal γ ∘ deriv (circularPhase z)) θ‖ ≤ _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    (contDiff_scaledRegularizedReciprocal γ).contDiffAt
    (contDiff_deriv_circularPhase z).contDiffAt (by exact_mod_cast le_top)]
  calc
    _ ≤ ∑ c : OrderedFinpartition k,
        ‖iteratedDeriv c.length (scaledRegularizedReciprocal γ)
          (deriv (circularPhase z) θ) *
          ∏ j, iteratedDeriv (c.partSize j) (deriv (circularPhase z)) θ‖ := norm_sum_le _ _
    _ ≤ ∑ _c : OrderedFinpartition k,
        regularizedReciprocalOrderBound N * γ⁻¹ ^ (k + 1) * (max 1 R) ^ N := by
      apply sum_le_sum
      intro c _
      have hcl : c.length ≤ N := c.length_le.trans hk
      have hout : ‖iteratedDeriv c.length (scaledRegularizedReciprocal γ)
          (deriv (circularPhase z) θ)‖ ≤ regularizedReciprocalOrderBound N * γ⁻¹ ^ (k + 1) :=
        (norm_iteratedDeriv_scaledRegularizedReciprocal_le_orderBound hγ hcl _).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hγinv (Nat.add_le_add_right c.length_le 1)) hC)
      have hprod : ‖∏ j, iteratedDeriv (c.partSize j) (deriv (circularPhase z)) θ‖ ≤
          (max 1 R) ^ N := by
        rw [norm_prod]
        calc
          _ ≤ ∏ _j : Fin c.length, max 1 R := by
            apply prod_le_prod (fun _ _ ↦ norm_nonneg _)
            intro j _
            rw [← iteratedDeriv_succ', Real.norm_eq_abs]
            exact (abs_iteratedDeriv_circularPhase_le z _ θ).trans (hz.trans (le_max_right _ _))
          _ = (max 1 R) ^ c.length := by simp
          _ ≤ (max 1 R) ^ N := pow_le_pow_right₀ hR hcl
      rw [norm_mul]
      exact mul_le_mul hout hprod (norm_nonneg _) (by positivity)
    _ = (Fintype.card (OrderedFinpartition k) : ℝ) *
        (regularizedReciprocalOrderBound N * γ⁻¹ ^ (k + 1) * (max 1 R) ^ N) := by simp
    _ ≤ circularReciprocalPartitionBound N *
        (regularizedReciprocalOrderBound N * γ⁻¹ ^ (k + 1) * (max 1 R) ^ N) :=
      mul_le_mul_of_nonneg_right
        (card_orderedFinpartition_le_circularReciprocalPartitionBound hk) (by positivity)
    _ = _ := by unfold circularReciprocalDerivativeBound; ring

/-- When the phase scale dominates the amplitude scale, the transport hypotheses follow. -/
theorem norm_iteratedDeriv_circularReciprocal_scale_le
    (z : EuclideanSpace ℝ (Fin 2)) {δ γ R : ℝ} (hδ : 0 < δ) (hδγ : δ ≤ γ)
    (hγ₁ : γ ≤ 1) (hz : ‖z‖ ≤ R) {k N : ℕ} (hk : k ≤ N) (θ : ℝ) :
    ‖iteratedDeriv k (circularReciprocal γ z) θ‖ ≤
      circularReciprocalDerivativeBound N R * γ⁻¹ * δ⁻¹ ^ k := by
  have hγ : 0 < γ := hδ.trans_le hδγ
  have hi : γ⁻¹ ≤ δ⁻¹ := (inv_le_inv₀ hγ hδ).mpr hδγ
  calc
    _ ≤ circularReciprocalDerivativeBound N R * γ⁻¹ ^ (k + 1) :=
      norm_iteratedDeriv_circularReciprocal_le z hγ hγ₁ hz hk θ
    _ = (circularReciprocalDerivativeBound N R * γ⁻¹) * γ⁻¹ ^ k := by
      rw [pow_succ]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi k)
      (by have := (circularReciprocalDerivativeBound_pos N R).le; positivity)

/-- Actual circular-phase decay on an arc with a transverse margin; the reciprocal and all
its derivative estimates are supplied by the construction, rather than assumed. -/
theorem norm_integral_circularPhase_mul_le
    (z : EuclideanSpace ℝ (Fin 2)) {a : ℝ → ℂ}
    (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) {δ γ R A θ₀ : ℝ}
    (hδ : 0 < δ) (hδγ : δ ≤ γ) (hγ₁ : γ ≤ 1) (hz : ‖z‖ ≤ R) (hA : 0 ≤ A)
    (hs : tsupport a ⊆ Icc (θ₀ - δ) (θ₀ + δ))
    (htrans : γ + ‖z‖ * δ ≤ |⟪z, angularDirection (θ₀ + Real.pi / 2)⟫|)
    (N : ℕ) (haA : ∀ k ≤ N, ∀ θ, ‖iteratedDeriv k a θ‖ ≤ A * δ⁻¹ ^ k)
    {t : ℝ} (ht : t ≠ 0) :
    ‖∫ θ, oscillatoryPhase (circularPhase z) t θ * a θ‖ ≤
      (2 * δ) * (2 ^ N * circularReciprocalDerivativeBound N R) ^ N * A *
        (|t| * δ * γ)⁻¹ ^ N := by
  have hγ : 0 < γ := hδ.trans_le hδγ
  have hqφ : ∀ θ ∈ tsupport a,
      circularReciprocal γ z θ * deriv (circularPhase z) θ = 1 := by
    intro θ hθ
    have hmem := hs hθ
    apply circularReciprocal_mul_deriv_eq_one_of_transverse z hγ htrans
    exact abs_le.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have h := norm_integral_oscillatoryPhase_mul_scale_le (contDiff_circularPhase z)
    (contDiff_circularReciprocal γ z) ha hac hqφ
    (circularReciprocalDerivativeBound_pos N R).le hA hδ hγ hs N
    (fun k hk θ ↦ norm_iteratedDeriv_circularReciprocal_scale_le z hδ hδγ hγ₁ hz hk θ)
    haA ht
  have hlen : max (θ₀ + δ - (θ₀ - δ)) 0 = 2 * δ := by
    rw [show θ₀ + δ - (θ₀ - δ) = 2 * δ by ring, max_eq_left (by positivity)]
  simpa only [hlen] using h

end FalconerPacking
