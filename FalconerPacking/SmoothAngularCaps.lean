/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularCapWeights
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# A constructed smooth angular partition of an annular multiplier

The multiplier vanishes in a neighborhood of the origin. Multiplying it by the explicit
normalized direction bumps therefore gives globally smooth compactly supported caps.
Their sum, norm control, angular support, and finite overlap are all proved directly.
-/

noncomputable section

open Set Metric Filter SchwartzMap Classical
open scoped ContDiff Topology

namespace FalconerPacking

/-- The actual angularly restricted multiplier before bundling as a Schwartz function. -/
def smoothAngularCapFunction (N : ℕ) (hN : 0 < N) (j : ℕ)
    (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  angularCapWeight N hN j ξ • ψ ξ

/-- Vanishing near the origin removes the only singularity of the direction map. -/
theorem contDiff_smoothAngularCapFunction (N : ℕ) (hN : 0 < N) (j : ℕ)
    {ψ : EuclideanSpace ℝ (Fin 2) → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hzero : ψ =ᶠ[𝓝 0] 0) : ContDiff ℝ ∞ (smoothAngularCapFunction N hN j ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hzero] with x hx
    simp only [smoothAngularCapFunction, hx, Pi.zero_apply, smul_zero]
  · exact (contDiffAt_angularCapWeight N hN j hξ).smul hψ.contDiffAt

/-- The cap retains the compact support of the original multiplier. -/
theorem hasCompactSupport_smoothAngularCapFunction (N : ℕ) (hN : 0 < N) (j : ℕ)
    {ψ : EuclideanSpace ℝ (Fin 2) → ℂ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (smoothAngularCapFunction N hN j ψ) :=
  hψ.smul_left (f := angularCapWeight N hN j)

/-- The constructed compact smooth cap, with no partition hypothesis. -/
def smoothAngularCap (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (j : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  (hasCompactSupport_smoothAngularCapFunction N hN j hψ).toSchwartzMap
    (contDiff_smoothAngularCapFunction N hN j (ψ.smooth ⊤) hzero)

@[simp]
theorem smoothAngularCap_apply (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (j : ℕ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    smoothAngularCap ψ hψ hzero N hN j ξ = angularCapWeight N hN j ξ • ψ ξ := rfl

/-- The bundled caps retain actual compact support. -/
theorem hasCompactSupport_smoothAngularCap
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (j : ℕ) :
    HasCompactSupport (smoothAngularCap ψ hψ hzero N hN j) :=
  hasCompactSupport_smoothAngularCapFunction N hN j hψ

/-- The actual partition identity, including the zero frequency. -/
theorem sum_smoothAngularCapFunction (N : ℕ) (hN : 0 < N)
    {ψ : EuclideanSpace ℝ (Fin 2) → ℂ} (hzero : ψ 0 = 0)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, smoothAngularCapFunction N hN j ψ ξ = ψ ξ := by
  by_cases hξ : ξ = 0
  · simp [hξ, smoothAngularCapFunction, hzero]
  · simp only [smoothAngularCapFunction, ← Finset.sum_smul, sum_angularCapWeight N hN hξ,
      one_smul]

/-- The finite family sums to the given Schwartz multiplier exactly. -/
theorem sum_smoothAngularCap (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) :
    ∑ j ∈ Finset.range N, smoothAngularCap ψ hψ hzero N hN j = ψ := by
  ext ξ
  simp only [sum_apply]
  exact sum_smoothAngularCapFunction N hN hzero.eq_of_nhds ξ

/-- Individual cap amplitudes never exceed the original amplitude. -/
theorem norm_smoothAngularCap_le (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) {j : ℕ} (hj : j < N) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ ≤ ‖ψ ξ‖ := by
  rw [smoothAngularCap_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (angularCapWeight_nonneg N hN j ξ)]
  exact (mul_le_mul_of_nonneg_right (angularCapWeight_le_one N hN hj ξ)
    (norm_nonneg _)).trans_eq (one_mul _)

/-- Nonnegative angular weights conserve the total absolute multiplier amplitude. -/
theorem sum_norm_smoothAngularCap (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ = ‖ψ ξ‖ := by
  by_cases hξ : ξ = 0
  · simp [hξ, hzero.eq_of_nhds]
  · simp only [smoothAngularCap_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (angularCapWeight_nonneg N hN _ _), ← Finset.sum_mul,
      sum_angularCapWeight N hN hξ, one_mul]

/-- The actual smooth caps have squared multiplier sum bounded by the original square. -/
theorem sum_norm_sq_smoothAngularCap (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ ^ 2 ≤ ‖ψ ξ‖ ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖ψ ξ‖ * ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have h := norm_smoothAngularCap_le ψ hψ hzero N hN (Finset.mem_range.mp hj) ξ
      nlinarith [norm_nonneg (smoothAngularCap ψ hψ hzero N hN j ξ)]
    _ = _ := by rw [← Finset.mul_sum, sum_norm_smoothAngularCap]; ring

/-- Every cap has support inside that of the original annular multiplier. -/
theorem support_smoothAngularCap_subset (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (j : ℕ) :
    Function.support (smoothAngularCap ψ hψ hzero N hN j) ⊆ Function.support ψ := by
  intro ξ hξ hψzero
  exact hξ (by simp only [smoothAngularCap_apply, hψzero, smul_zero])

/-- The directional support has width twice the covering radius. -/
theorem smoothAngularCap_direction_support
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (j : ℕ) {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : ξ ∈ Function.support (smoothAngularCap ψ hψ hzero N hN j)) :
    ‖ξ‖⁻¹ • ξ ∈ ball (angularDirection (angularGridPoint N j)) (4 * Real.pi / N) := by
  apply angularCapWeight_direction_support N hN j
  intro he
  exact hξ (by simp only [smoothAngularCap_apply, he, zero_smul])

/-- The constructed cap partition has an absolute support overlap bound. -/
theorem card_smoothAngularCap_support_le
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hψ : HasCompactSupport ψ) (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun j ↦
      ξ ∈ Function.support (smoothAngularCap ψ hψ hzero N hN j))).card ≤
        Nat.ceil (6 * Real.pi) := by
  apply (Finset.card_le_card ?_).trans (card_angularCapWeight_support_le N hN ξ)
  intro j hj
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, ?_⟩
  intro he
  exact (Finset.mem_filter.mp hj).2 (by simp only [smoothAngularCap_apply, he, zero_smul])

end FalconerPacking
