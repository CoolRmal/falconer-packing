/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PhysicalDyadicCapKernels
public import FalconerPacking.StandardAngularGrid

/-!
# Kernel estimates on the concrete dividing cap grid

The explicit grid discharges every geometric hypothesis of the uniform cap construction.
The constants below are uniform in annular scale, direction, and physical strip width.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Uniform first norms and transverse tails for the actual caps on the standard dyadic grid. -/
theorem exists_uniform_standardCapKernel_bounds (T m : ℕ) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ n j : ℕ,
      let N := 64 * 2 ^ (2 * T * n)
      let hN : 0 < N := by dsimp only [N]; positivity
      (∫⁻ x, ‖(𝓕⁻ (dyadicAngularCap (4 * T) n N hN j) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤ ENNReal.ofReal C₀ ∧
      ∀ w : ℝ, 0 < w →
        (∫⁻ x in {x | w ≤ |⟪sourceWavePacketNormal N j, x⟫|},
          ‖(𝓕⁻ (dyadicAngularCap (4 * T) n N hN j) :
            SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ₑ) ≤
          ENNReal.ofReal (C₁ / (Real.sqrt ((2 : ℝ) ^ ((4 * T) * n)) * w) ^ m) := by
  let n (i : ℕ × ℕ) := i.1
  let N (i : ℕ × ℕ) := 64 * 2 ^ (2 * T * i.1)
  let j (i : ℕ × ℕ) := i.2
  have hN (i : ℕ × ℕ) : 0 < N i := (standard_fourfold_angular_grid_bounds T i.1).1
  have hw (i : ℕ × ℕ) : Real.sqrt ((2 : ℝ) ^ ((4 * T) * n i)) ≤ N i :=
    (standard_fourfold_angular_grid_bounds T i.1).2.1
  have hs (i : ℕ × ℕ) : 4 * Real.pi ≤ N i :=
    (standard_fourfold_angular_grid_bounds T i.1).2.2.1
  have hu (i : ℕ × ℕ) : (N i : ℝ) ≤
      2 * Real.pi * 32 * Real.sqrt ((2 : ℝ) ^ ((4 * T) * n i)) :=
    (standard_fourfold_angular_grid_bounds T i.1).2.2.2
  obtain ⟨C₀, hC₀, h₀⟩ := dyadicCapKernel_uniform_lintegral
    (4 * T) (by norm_num : (0 : ℝ) ≤ 32) n N j hN hw hs hu
  obtain ⟨C₁, hC₁, h₁⟩ := dyadicCapKernel_uniform_transverse_tail
    (4 * T) (by norm_num : (0 : ℝ) ≤ 32) n N j hN hw hs hu m
  exact ⟨C₀, C₁, hC₀, hC₁, fun a b ↦ ⟨h₀ (a, b), h₁ (a, b)⟩⟩

end FalconerPacking
