/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CircleCellSchwartz
import FalconerPacking.CircleCapGeometry

/-!
# Fourier support of actual angular-cell pieces

The defining convolution gives the spectral support. Circular arc geometry then gives
both the anisotropic rectangle and an actual family of frequency balls of finite overlap.
-/

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Classical
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Every actual cell Fourier piece is supported in any set containing its thickened arc.
The containing set need not have a smooth or measurable boundary. -/
theorem circleCellPhysicalSchwartz_fourier_support_of_thickening {r ε : ℝ} (hr : 0 < r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (N j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 ε)
    (T : Set (EuclideanSpace ℝ (Fin 2)))
    (hT : ∀ θ ∈ angularGridCell N j, ∀ z, ‖z‖ ≤ ε → r • angularDirection θ + z ∈ T) :
    Function.support
        (𝓕 (circleCellPhysicalSchwartz r hg N j k hk) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ⊆ T := by
  intro z hz
  by_contra hbad
  apply Function.mem_support.mp hz
  rw [fourier_circleCellPhysicalSchwartz_apply]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_circle_radial_representation hr] with ξ hξ
  by_cases hcell : ξ ∈ circleAngularCell N j
  · by_cases hkzero : k (z - ξ) = 0
    · simp only [hkzero, mul_zero, Pi.zero_apply]
    · have hknorm : ‖z - ξ‖ ≤ ε := by
        simpa only [mem_closedBall, dist_zero_right] using hkball hkzero
      have hb := hT (radialAngle ξ 0) hcell (z - ξ) hknorm
      rw [← hξ, add_sub_cancel] at hb
      exact (hbad hb).elim
  · simp only [circleCellData, indicator_of_notMem hcell, zero_mul, Pi.zero_apply]

/-- The actual Fourier transform of a cell piece lies in its thickened arc rectangle. -/
theorem circleCellPhysicalSchwartz_fourier_rectangle {r ε : ℝ} (hr : 0 < r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (N j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 ε)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Function.support
      (𝓕 (circleCellPhysicalSchwartz r hg N j k hk) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) :
    |circleCapFrame (angularGridPoint N j)
        (z - r • angularDirection (angularGridPoint N j)) 0| ≤
        r * (2 * Real.pi / N) + ε ∧
      |circleCapFrame (angularGridPoint N j)
        (z - r • angularDirection (angularGridPoint N j)) 1| ≤
        r * (2 * Real.pi / N) ^ 2 / 2 + ε :=
  circleCellPhysicalSchwartz_fourier_support_of_thickening hr hg N j k hk hkball
    {z | |circleCapFrame (angularGridPoint N j)
        (z - r • angularDirection (angularGridPoint N j)) 0| ≤
          r * (2 * Real.pi / N) + ε ∧
      |circleCapFrame (angularGridPoint N j)
        (z - r • angularDirection (angularGridPoint N j)) 1| ≤
          r * (2 * Real.pi / N) ^ 2 / 2 + ε}
    (fun _ hθ z hz ↦ circleCapFrame_thickened_bounds hr.le
      (angularGridCell_angle_bound hθ) z hz) hz

/-- The defining convolution gives the thickened arc's enclosing frequency ball. -/
theorem circleCellPhysicalSchwartz_fourier_closedBall {r ε : ℝ} (hr : 0 < r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (N j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 ε) :
    Function.support
        (𝓕 (circleCellPhysicalSchwartz r hg N j k hk) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ⊆
      closedBall (r • angularDirection (angularGridPoint N j))
        (r * (2 * Real.pi / N) + ε) := by
  apply circleCellPhysicalSchwartz_fourier_support_of_thickening hr hg N j k hk hkball
  intro θ hθ z hz
  have hd := circleGridCell_dist_le hr.le hθ
  have ht := dist_triangle (r • angularDirection θ + z) (r • angularDirection θ)
    (r • angularDirection (angularGridPoint N j))
  have he : dist (r • angularDirection θ + z) (r • angularDirection θ) = ‖z‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  rw [he] at ht
  exact ht.trans (by linarith)

/-- Any containing angular interval can be used for the admissible Fourier rectangle.
This permits a fine cell to inherit its coarse ancestor's frame. -/
theorem circleCellPhysicalSchwartz_admissible_rectangle_of_angle {R C r a b φ : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hr : 0 < r) (hrR : r ≤ C * R)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) {N j : ℕ}
    (hangle : ∀ θ ∈ angularGridCell N j, |θ - φ| ≤ (R * a)⁻¹)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Function.support
      (𝓕 (circleCellPhysicalSchwartz r hg N j k hk) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) :
    |circleCapFrame φ (z - r • angularDirection φ) 0| ≤ (C + 1) / a ∧
      |circleCapFrame φ (z - r • angularDirection φ) 1| ≤ (C + 1) / b :=
  circleCellPhysicalSchwartz_fourier_support_of_thickening hr hg N j k hk hkball
    {z | |circleCapFrame φ (z - r • angularDirection φ) 0| ≤ (C + 1) / a ∧
      |circleCapFrame φ (z - r • angularDirection φ) 1| ≤ (C + 1) / b}
    (fun θ hθ z hz ↦ circleCapFrame_admissible_rectangle hR hC hr.le hrR ha ha₁ hb hb₁
      hab (hangle θ hθ) z hz) hz

/-- Actual admissibility controls the Fourier rectangle, including the unit smoothing. -/
theorem circleCellPhysicalSchwartz_admissible_rectangle {R C r a b : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hr : 0 < r) (hrR : r ≤ C * R)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) {N : ℕ}
    (hwidth : 2 * Real.pi / N ≤ (R * a)⁻¹)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Function.support
      (𝓕 (circleCellPhysicalSchwartz r hg N j k hk) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) :
    |circleCapFrame (angularGridPoint N j)
        (z - r • angularDirection (angularGridPoint N j)) 0| ≤ (C + 1) / a ∧
      |circleCapFrame (angularGridPoint N j)
        (z - r • angularDirection (angularGridPoint N j)) 1| ≤ (C + 1) / b :=
  circleCellPhysicalSchwartz_admissible_rectangle_of_angle hR hC hr hrR ha ha₁ hb hb₁ hab
    (fun _ hθ ↦ (angularGridCell_angle_bound hθ).trans hwidth) hg k hk hkball hz

/-- Integral refinement gives actual coarse frames for every fine cell. -/
theorem circleCellPhysicalSchwartz_ancestor_rectangle {R C r a b : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hr : 0 < r) (hrR : r ≤ C * R)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hwidth : 2 * Real.pi / N ≤ (R * a)⁻¹)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1)
    {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Function.support
      (𝓕 (circleCellPhysicalSchwartz r hg (M * N) j k hk) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) :
    |circleCapFrame (angularGridPoint N (j / M))
        (z - r • angularDirection (angularGridPoint N (j / M))) 0| ≤ (C + 1) / a ∧
      |circleCapFrame (angularGridPoint N (j / M))
        (z - r • angularDirection (angularGridPoint N (j / M))) 1| ≤ (C + 1) / b :=
  circleCellPhysicalSchwartz_admissible_rectangle_of_angle hR hC hr hrR ha ha₁ hb hb₁ hab
    (fun _ hθ ↦ (angularGridCell_angle_bound
      (angularGridCell_refinement_subset hM hN j hθ)).trans hwidth) hg k hk hkball hz

/-- The actual spectral pieces fit in open frequency balls of uniform grid overlap. -/
theorem circleCellPhysicalSchwartz_fourier_ball {r C : ℝ} (hr : 0 < r)
    {N : ℕ} (hN : 0 < N) (hscale : (N : ℝ) ≤ C * r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hg : Integrable g (normalizedCircleMeasure r)) (j : ℕ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1) :
    Function.support
        (𝓕 (circleCellPhysicalSchwartz r hg N j k hk) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ⊆
      ball (r • angularDirection (angularGridPoint N j))
        ((2 * Real.pi + C + 1) * r / N) := by
  intro z hz
  have hd := circleCellPhysicalSchwartz_fourier_closedBall hr hg N j k hk hkball hz
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : r * (2 * Real.pi / N) + 1 < (2 * Real.pi + C + 1) * r / N := by
    rw [lt_div_iff₀ hN₀]
    have he : (r * (2 * Real.pi / N) + 1) * N = 2 * Real.pi * r + N := by
      field_simp
    rw [he]
    nlinarith
  exact lt_of_le_of_lt hd hh

/-- No frequency-ball overlap hypothesis is needed for the actual equal angular grid. -/
theorem circleCell_frequency_ball_overlap {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    {N : ℕ} (hN : 0 < N) (z : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun j ↦
      z ∈ ball (r • angularDirection (angularGridPoint N j))
        ((2 * Real.pi + C + 1) * r / N))).card ≤
      Nat.ceil (4 * Real.pi + C + 1) := by
  convert card_circle_grid_balls_le N hN hr (by positivity : 0 ≤ 2 * Real.pi + C + 1) z
    using 1
  congr 1
  ring

end FalconerPacking
