/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.UniformDyadicCapSymbols
import FalconerPacking.UniformSchwartzTails

/-!
# Uniform bounds for the actual rescaled cap kernels

The caps here are the previously constructed normalized smooth angular partition of the actual
dyadic annular multiplier. Their support and derivative bounds have already been proved, so
continuity of inverse Fourier transformation gives genuine kernel estimates, uniformly in the
annular scale and cap index.
-/

noncomputable section

open Set Metric MeasureTheory Bornology FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Actual rescaled dyadic caps form a bounded Schwartz family at the standard angular scale. -/
theorem isVonNBounded_rescaledDyadicAngularCap_range {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i))) :
    IsVonNBounded ℝ (range (fun i ↦ rescaledDyadicAngularCap T (n i) (N i) (hN i) (j i))) := by
  apply isVonNBounded_schwartz_range_of_derivatives _
    ((12 * Real.pi + 3) * (2 : ℝ) ^ T)
  · intro i
    exact rescaledDyadicAngularCap_tsupport_ball T (n i) (N i) (hN i) (hwidth i) (j i)
  · intro m
    obtain ⟨C, hC, hc⟩ := rescaledDyadicAngularCap_derivative_bound T hK m
    exact ⟨C, hC.le, fun i x ↦ hc (n i) (N i) (hN i) (j i) x
      (hwidth i) (hsmall i) (hupper i)⟩

/-- The actual inverse Fourier kernels of the rescaled caps form a bounded Schwartz family. -/
theorem isVonNBounded_rescaledDyadicCapKernel_range {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i))) :
    IsVonNBounded ℝ (range (fun i ↦ (𝓕⁻
      (rescaledDyadicAngularCap T (n i) (N i) (hN i) (j i)) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ))) :=
  isVonNBounded_fourierInv_range _
    (isVonNBounded_rescaledDyadicAngularCap_range T hK n N j hN hwidth hsmall hupper)

/-- Uniform rapid decay and all spatial first moments hold for the actual cap kernels. -/
theorem rescaledDyadicCapKernel_uniform_bounds {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i)))
    (m : ℕ) :
    (∃ C > 0, ∀ i x,
      ‖(𝓕⁻ (rescaledDyadicAngularCap T (n i) (N i) (hN i) (j i)) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ ≤ C / (1 + ‖x‖) ^ m) ∧
    (∃ C > 0, ∀ i,
      (∫ x, ‖x‖ ^ m * ‖(𝓕⁻ (rescaledDyadicAngularCap T (n i) (N i) (hN i) (j i)) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖) ≤ C) := by
  have hb := isVonNBounded_rescaledDyadicCapKernel_range T hK n N j hN hwidth hsmall hupper
  exact ⟨exists_uniform_schwartz_decay _ hb m, exists_uniform_schwartz_moment _ hb m⟩

/-- Whole-space first norms and transverse tails have constants independent of the cap scale. -/
theorem rescaledDyadicCapKernel_uniform_integral_bounds {ι : Type*} (T : ℕ) {K : ℝ}
    (hK : 0 ≤ K) (n N j : ι → ℕ) (hN : ∀ i, 0 < N i)
    (hwidth : ∀ i, Real.sqrt ((2 : ℝ) ^ (T * n i)) ≤ N i)
    (hsmall : ∀ i, 4 * Real.pi ≤ N i)
    (hupper : ∀ i, (N i : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n i)))
    (m : ℕ) :
    (∃ C > 0, ∀ i,
      (∫⁻ x, ‖(𝓕⁻ (rescaledDyadicAngularCap T (n i) (N i) (hN i) (j i)) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤ ENNReal.ofReal C) ∧
    (∃ C > 0, ∀ i (e : EuclideanSpace ℝ (Fin 2)), ‖e‖ ≤ 1 → ∀ L : ℝ, 0 < L →
      (∫⁻ x in {x | L ≤ |⟪e, x⟫|},
        ‖(𝓕⁻ (rescaledDyadicAngularCap T (n i) (N i) (hN i) (j i)) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤ ENNReal.ofReal (C / L ^ m)) := by
  have hb := isVonNBounded_rescaledDyadicCapKernel_range T hK n N j hN hwidth hsmall hupper
  exact ⟨exists_uniform_schwartz_lintegral_enorm _ hb,
    exists_uniform_schwartz_transverse_tail _ hb m⟩

end FalconerPacking
