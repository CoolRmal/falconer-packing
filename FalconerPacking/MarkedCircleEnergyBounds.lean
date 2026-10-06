/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.MarkedCircleChain
public import FalconerPacking.InheritedCircleEnergy
public import FalconerPacking.GridEnergyBounds

/-!
# Actual terminal and error energies from the source circle spectrum

The uniform multiplier bound controls every marked parent's full-space energy.
The proved finite-grid mass bound then controls the global errors, and exact normalized
square areas give the terminal local-energy estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap
open scoped ENNReal Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 < r)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ Metric.closedBall 0 1)
    (s t : ℕ) (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (K : ℕ) (σ : Measure (EuclideanSpace ℝ (Fin 2)))
    (I : Finset (Fin 2 → ℤ)) {L : ℝ} (hL : 1 ≤ L)

include hr hkball hL

/-- Every actual chain error is controlled by the source circle energy, uniformly in future marks. -/
theorem markedCircleErrorEnergy_le_source (j : ℕ) :
    markedCircleErrorEnergy ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
      k hk n e good K σ I L j ≤
      ENNReal.ofReal (49 * (L ^ (2 * j + 2)) ^ 2) * σ univ *
        (ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
          ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
          ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
            ∂radialAngularProbability) := by
  apply sum_grid_global_energy_le σ (by positivity) (one_le_pow₀ hL)
  intro Q _
  exact sum_markedDyadicCircle_energy_le ψ hψ hzero μ hr (by norm_num) k hk hkball
    s t n e good j K Q

/-- The actual normalized energy, in particular the terminal one, has no enlargement loss. -/
theorem markedCircleLocalEnergy_le_source (j : ℕ) :
    markedCircleLocalEnergy ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
      k hk n e good K σ I L j ≤
      ENNReal.ofReal (49 * ((2 : ℝ) ^ n j) ^ 2) * σ univ *
        (ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
          ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
          ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
            ∂radialAngularProbability) := by
  have h := sum_grid_local_energy_le σ
    (a := ((2 : ℝ) ^ n j)⁻¹) (t := L ^ (2 * j + 2)) (by positivity) (one_le_pow₀ hL)
    (dyadicChainCubes n I j) (dyadicCapLabels s (e j))
    (fun Q α x ↦ ‖markedDyadicCircle ψ hψ hzero s t r
      (integrable_circle_planarMeasureFourier μ r) k hk n e good j K Q α x‖ₑ ^ 2) _
    (fun Q _ ↦ sum_markedDyadicCircle_energy_le ψ hψ hzero μ hr (by norm_num)
      k hk hkball s t n e good j K Q)
  simpa only [markedCircleLocalEnergy, inv_pow, inv_inv] using h

end FalconerPacking
