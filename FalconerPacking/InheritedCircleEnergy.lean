/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.InheritedCapMultiplier
public import FalconerPacking.CircleCellTerminal

/-!
# Uniform energy of actual surviving circle functions

The inherited physical functions are exactly the smoothed extension of their constructed
multiplier times the common source spectrum. The multiplier square sum and circle
convolution estimate therefore give the full global bound, uniformly in every mark.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal Topology FourierTransform

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (S : ℕ) (hS : 0 < S)

/-- Actual inherited physical pieces are the cutoff extension of their actual multiplier. -/
theorem inheritedCapCircle_apply {κ : Type*} (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (T : ℕ) (label : ℕ × ℕ → κ) (keep : ℕ × ℕ → Prop) (α : κ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    inheritedLabelSum (fineCapLabels S T) label α keep
      (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk T) x =
      (𝓕⁻ k) x * circleSpectralExtension r
        (fun ξ ↦ inheritedCapMultiplier ψ hψ hzero S hS T label keep α ξ * g ξ) x := by
  change (∑ p ∈ (fineCapLabels S T).filter (fun p ↦ label p = α ∧ keep p),
    circlePhysicalSchwartz r (integrable_fineStandardCapData ψ hψ hzero S hS hg T p) k hk) x = _
  rw [sum_circlePhysicalSchwartz_data, circlePhysicalSchwartz_apply]
  congr 1
  apply congrArg (fun v ↦ circleSpectralExtension r v x)
  funext ξ
  exact (inheritedCapMultiplier_mul ψ hψ hzero S hS T label keep α g ξ).symm

/-- Uniform global energy for any inherited partition and any set of later deletions. -/
theorem sum_inheritedCapCircle_energy_le {κ : Type*}
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ Metric.closedBall 0 a)
    {T : ℕ} (hT : 0 < T) (A : Finset κ) (label : ℕ × ℕ → κ) (keep : ℕ × ℕ → Prop) :
    (∑ α ∈ A, ∫⁻ x,
      ‖inheritedLabelSum (fineCapLabels S T) label α keep
        (fineCapCircleSchwartz ψ hψ hzero S hS r (integrable_circle_planarMeasureFourier μ r)
          k hk T) x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
        ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability := by
  simp_rw [inheritedCapCircle_apply]
  exact sum_circleSpectralExtension_cutoff_energy_le μ hr ha A
    (inheritedCapMultiplier ψ hψ hzero S hS T label keep)
    (fun α _ ↦ measurable_inheritedCapMultiplier ψ hψ hzero S hS T label keep α)
    k hkball (sum_norm_sq_inheritedCapMultiplier_le ψ hψ hzero S hS hT A label keep)

/-- In particular the actual spatially marked dyadic circle family has this same uniform bound. -/
theorem sum_markedDyadicCircle_energy_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ Metric.closedBall 0 a)
    (s t : ℕ) (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (j K : ℕ) (Q : Fin 2 → ℤ) :
    (∑ α ∈ dyadicCapLabels s (e j), ∫⁻ x,
      ‖markedDyadicCircle ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
        k hk n e good j K Q α x‖ₑ ^ 2) ≤
      ENNReal.ofReal (a / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
        ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
        ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
          ∂radialAngularProbability :=
  sum_inheritedCapCircle_energy_le ψ hψ hzero (2 ^ s) (by positivity) μ hr ha k hk hkball
    (by positivity) (dyadicCapLabels s (e j)) (dyadicCapAncestor s t (e j))
    (dyadicCapSpatialSurvives s t n e good j K Q)

end FalconerPacking
