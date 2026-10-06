/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AngularDerivativeEnergy
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Explicit derivatives and nonstationarity of the circular phase

Every derivative of the actual circular phase is a quarter-turn of the direction.
Transverse separation at one angle controls the derivative on a whole arc.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

@[fun_prop]
theorem contDiff_angularDirection : ContDiff ℝ ∞ angularDirection := by
  exact Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.comp
    ((Complex.ofRealCLM.contDiff.comp Real.contDiff_cos).add
      ((Complex.ofRealCLM.contDiff.comp Real.contDiff_sin).mul contDiff_const))

/-- The actual circle phase associated to a displacement vector. -/
def circularPhase (z : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) : ℝ :=
  ⟪z, angularDirection θ⟫

@[fun_prop]
theorem contDiff_circularPhase (z : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ∞ (circularPhase z) :=
  (innerSL ℝ z).contDiff.comp contDiff_angularDirection

/-- Coordinate formula for the actual circular phase. -/
theorem circularPhase_eq_coordinates (z : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) :
    circularPhase z θ = z 0 * Real.cos θ + z 1 * Real.sin θ := by
  simp only [circularPhase, angularDirection, Complex.orthonormalBasisOneI_repr_apply,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    mul_one, zero_add, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Differentiation is exactly a quarter-turn of the angular parameter. -/
theorem hasDerivAt_circularPhase (z : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) :
    HasDerivAt (circularPhase z) (circularPhase z (θ + Real.pi / 2)) θ := by
  have he : circularPhase z = fun t ↦ z 0 * Real.cos t + z 1 * Real.sin t :=
    funext (circularPhase_eq_coordinates z)
  rw [he]
  convert ((Real.hasDerivAt_cos θ).const_mul (z 0)).add
    ((Real.hasDerivAt_sin θ).const_mul (z 1)) using 1 <;> try rfl
  simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
    mul_zero, mul_one, zero_sub, zero_add]

theorem deriv_circularPhase (z : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) :
    deriv (circularPhase z) θ = circularPhase z (θ + Real.pi / 2) :=
  (hasDerivAt_circularPhase z θ).deriv

/-- The actual first derivative is globally smooth. -/
theorem contDiff_deriv_circularPhase (z : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ∞ (deriv (circularPhase z)) := by
  rw [show deriv (circularPhase z) = (fun θ ↦ circularPhase z (θ + Real.pi / 2)) from
    funext (deriv_circularPhase z)]
  exact (contDiff_circularPhase z).comp (contDiff_id.add contDiff_const)

/-- All iterated derivatives have an explicit quarter-turn formula. -/
theorem iteratedDeriv_circularPhase (z : EuclideanSpace ℝ (Fin 2)) (n : ℕ) (θ : ℝ) :
    iteratedDeriv n (circularPhase z) θ = circularPhase z (θ + n * (Real.pi / 2)) := by
  induction n generalizing θ with
  | zero => simp only [iteratedDeriv_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, show iteratedDeriv n (circularPhase z) =
      (fun t ↦ circularPhase z (t + n * (Real.pi / 2))) from funext ih]
    have h := (hasDerivAt_circularPhase z (θ + n * (Real.pi / 2))).comp θ
      ((hasDerivAt_id θ).add_const (n * (Real.pi / 2)))
    rw [show deriv (fun t ↦ circularPhase z (t + n * (Real.pi / 2))) θ =
      circularPhase z (θ + n * (Real.pi / 2) + Real.pi / 2) by
        simpa only [Function.comp_def, id_eq, mul_one] using h.deriv]
    congr 1
    push_cast
    ring

/-- The sharp elementary bound for every phase derivative. -/
theorem abs_iteratedDeriv_circularPhase_le
    (z : EuclideanSpace ℝ (Fin 2)) (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n (circularPhase z) θ| ≤ ‖z‖ := by
  rw [iteratedDeriv_circularPhase, circularPhase]
  simpa only [norm_angularDirection, mul_one] using
    abs_real_inner_le_norm z (angularDirection (θ + n * (Real.pi / 2)))

/-- The actual phase is globally Lipschitz with constant `‖z‖`. -/
theorem lipschitzWith_circularPhase (z : EuclideanSpace ℝ (Fin 2)) :
    LipschitzWith ‖z‖₊ (circularPhase z) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun θ ↦ (hasDerivAt_circularPhase z θ).differentiableAt)
  intro θ
  change |deriv (circularPhase z) θ| ≤ ‖z‖
  simpa only [iteratedDeriv_one] using abs_iteratedDeriv_circularPhase_le z 1 θ

/-- The derivative has the same Lipschitz constant. -/
theorem abs_deriv_circularPhase_sub_le
    (z : EuclideanSpace ℝ (Fin 2)) (θ θ₀ : ℝ) :
    |deriv (circularPhase z) θ - deriv (circularPhase z) θ₀| ≤ ‖z‖ * |θ - θ₀| := by
  rw [deriv_circularPhase, deriv_circularPhase]
  simpa only [Real.dist_eq, coe_nnnorm, add_sub_add_right_eq_sub] using
    (lipschitzWith_circularPhase z).dist_le_mul (θ + Real.pi / 2) (θ₀ + Real.pi / 2)

/-- A transverse component at the central angle gives an explicit lower bound over the arc. -/
theorem abs_deriv_circularPhase_ge
    (z : EuclideanSpace ℝ (Fin 2)) {θ θ₀ δ : ℝ} (hθ : |θ - θ₀| ≤ δ) :
    |⟪z, angularDirection (θ₀ + Real.pi / 2)⟫| - ‖z‖ * δ ≤
      |deriv (circularPhase z) θ| := by
  have h := (abs_deriv_circularPhase_sub_le z θ θ₀).trans
    (mul_le_mul_of_nonneg_left hθ (norm_nonneg z))
  have hr := abs_sub_abs_le_abs_sub (deriv (circularPhase z) θ₀) (deriv (circularPhase z) θ)
  rw [abs_sub_comm] at hr
  rw [deriv_circularPhase z θ₀, circularPhase] at hr h
  linarith

/-- A fixed transverse margin certifies nonstationarity on the whole specified arc. -/
theorem le_abs_deriv_circularPhase_of_transverse
    (z : EuclideanSpace ℝ (Fin 2)) {θ θ₀ δ γ : ℝ}
    (htrans : γ + ‖z‖ * δ ≤ |⟪z, angularDirection (θ₀ + Real.pi / 2)⟫|)
    (hθ : |θ - θ₀| ≤ δ) : γ ≤ |deriv (circularPhase z) θ| := by
  have h := abs_deriv_circularPhase_ge z hθ
  linarith

end FalconerPacking
