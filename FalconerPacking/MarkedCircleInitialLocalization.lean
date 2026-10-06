/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.MarkedCircleEnergyBounds
public import FalconerPacking.InitialFourierLocalization

/-!
# Initial pin localization of the actual inherited circle functions

All marked functions have their actual Fourier support in the circle thickened by the
fixed spectral cutoff. Restricting pins to a dyadic cell therefore gives the proved
bandlimited localization estimate with no extra spectral-support assumption.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap FourierTransform
open scoped ENNReal Topology FourierTransform

namespace FalconerPacking

/-- The actual cube pin support is within one side length of its center. -/
theorem dist_gridSquareCenter_le_of_mem_dyadicCube {n : ℕ} {Q : Fin 2 → ℤ}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ dyadicCube n Q) :
    dist x (gridSquareCenter ((2 : ℝ) ^ n)⁻¹ Q) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  simpa only [dist_eq_norm, one_mul] using norm_sub_gridSquareCenter_le
    (dyadicCube_subset_enlargedGridSquare Q le_rfl hx)

/-- A ball of half the side length is contained in the actual coordinate square. -/
theorem ball_subset_enlargedGridSquare (a t : ℝ) (Q : Fin 2 → ℤ) :
    ball (gridSquareCenter a Q) (t * a / 2) ⊆ enlargedGridSquare a t Q := by
  intro x hx
  rw [mem_enlargedGridSquare_iff]
  intro i
  exact (abs_sub_coord_le_dist x (gridSquareCenter a Q) i).trans
    (mem_ball.mp hx).le

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (s t : ℕ) {R r : ℝ} (hR : 1 ≤ R) (hr : 0 < r) (hrR : r ≤ 2 * R)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1)
    (n e : ℕ → ℕ) (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)

include hR hr hrR hkball

/-- Every actual marked circle piece lies in a common frequency ball, uniformly in all marks. -/
theorem markedDyadicCircle_fourier_global_ball (j K : ℕ) (Q : Fin 2 → ℤ)
    (α : ℕ ⊕ (ℕ × ℕ)) :
    Function.support (fun ξ ↦
      𝓕 (markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α) ξ) ⊆ ball 0 (4 * R) := by
  apply fourier_support_inheritedLabelSum
  intro p _ _ _
  apply circleCellPhysicalSchwartz_fourier_support_of_thickening hr
    (integrable_standardCapData ψ hψ hzero (2 ^ s) (by positivity) hg p.1)
    (2 ^ t) p.2 k hk hkball
  intro θ _ z hz
  rw [mem_ball, dist_zero_right]
  have hn : ‖r • angularDirection θ‖ = r := by simp [norm_smul, hr.le]
  have h := norm_add_le (r • angularDirection θ) z
  rw [hn] at h
  linarith

omit hR hr hrR hkball in
/-- Initial localization for the actual marked function and actual dyadic pin restriction. -/
theorem markedDyadicCircle_pin_cube_localization (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (s t : ℕ) (R r : ℝ), 1 ≤ R → 0 < r → r ≤ 2 * R →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → ℂ)
        (hg : Integrable g (normalizedCircleMeasure r))
        (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k),
        Function.support k ⊆ closedBall 0 1 →
      ∀ (n e : ℕ → ℕ) (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
        (j K : ℕ) (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ))
        (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (τ : ℝ), 2 ≤ τ →
        let a := ((2 : ℝ) ^ n j)⁻¹
        let U := enlargedGridSquare a τ Q
        let f := markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α
        (∫⁻ x in dyadicCube (n j) Q, ‖f x‖ₑ ^ 2 ∂σ) ≤
          (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
            ((ENNReal.ofReal ((4 * R) ^ 2) * 81 *
              ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
                SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
              ENNReal.ofReal (τ * a) ^ 2) * σ U *
                (∫⁻ x, ‖f x‖ₑ ^ 2 ∂((volume U)⁻¹ • volume.restrict U)) +
              ENNReal.ofReal ((4 * R) ^ 2 * C / (1 + 4 * R * (τ * a / 2 - a)) ^ m) *
                σ (dyadicCube (n j) Q) * ∫⁻ x, ‖f x‖ₑ ^ 2) := by
  obtain ⟨C, hC, hloc⟩ := initial_fourier_localization m
  refine ⟨C, hC, ?_⟩
  intro ψ hψ hzero s t R r hR hr hrR g hg k hk hkball n e good j K Q α σ hσ τ hτ
  dsimp only
  let a := ((2 : ℝ) ^ n j)⁻¹
  let U := enlargedGridSquare a τ Q
  let f := markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α
  have ha : 0 < a := by dsimp [a]; positivity
  have hτ₀ : 0 < τ := by linarith
  have hv0 : volume U ≠ 0 := by
    rw [volume_enlargedGridSquare]
    positivity
  have hvtop : volume U ≠ ∞ := by rw [volume_enlargedGridSquare]; finiteness
  have hnorm : (∫⁻ x in U, ‖f x‖ₑ ^ 2) =
      ENNReal.ofReal (τ * a) ^ 2 *
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂((volume U)⁻¹ • volume.restrict U) := by
    rw [lintegral_smul_measure, smul_eq_mul, ← volume_enlargedGridSquare a τ Q,
      ← mul_assoc, ENNReal.mul_inv_cancel hv0 hvtop, one_mul]
  have hpin : ∀ᵐ x ∂σ.restrict (dyadicCube (n j) Q),
      dist x (gridSquareCenter a Q) ≤ a := by
    filter_upwards [ae_restrict_mem (measurableSet_dyadicCube (n j) Q)] with x hx
    exact dist_gridSquareCenter_le_of_mem_dyadicCube hx
  have hb := hloc (σ.restrict (dyadicCube (n j) Q)) f 0 (gridSquareCenter a Q)
    (4 * R) a (τ * a / 2) (by positivity) (by nlinarith) hpin
    (markedDyadicCircle_fourier_global_ball ψ hψ hzero s t hR hr hrR hg k hk hkball
      n e good j K Q α)
  simp only [Measure.restrict_apply_univ] at hb
  apply hb.trans
  apply mul_le_mul_right
  apply add_le_add
  · have hmass : σ (dyadicCube (n j) Q) ≤ σ U :=
      measure_mono (dyadicCube_subset_enlargedGridSquare Q (by linarith))
    have hi : (∫⁻ x in ball (gridSquareCenter a Q) (τ * a / 2), ‖f x‖ₑ ^ 2) ≤
        ENNReal.ofReal (τ * a) ^ 2 *
          ∫⁻ x, ‖f x‖ₑ ^ 2 ∂((volume U)⁻¹ • volume.restrict U) := by
      rw [← hnorm]
      exact lintegral_mono_set (ball_subset_enlargedGridSquare a τ Q)
    calc
      _ ≤ (ENNReal.ofReal ((4 * R) ^ 2) * 81 *
          ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
            SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * σ U) *
          (ENNReal.ofReal (τ * a) ^ 2 *
            ∫⁻ x, ‖f x‖ₑ ^ 2 ∂((volume U)⁻¹ • volume.restrict U)) := by gcongr
      _ = _ := by ring
  · gcongr
    exact Measure.restrict_le_self

end FalconerPacking
