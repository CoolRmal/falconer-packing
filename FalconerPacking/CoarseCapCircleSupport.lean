/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.StandardCapCircleSchwartz

/-!
# Actual Fourier support of grouped coarse labels

Grouping whole standard caps enlarges their nominal ancestor by only a fixed factor.
After compact spectral smoothing there is one enclosing ball per coarse ancestor,
with overlap independent of the number of standard caps grouped there.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Filter Classical
open scoped FourierTransform Topology

namespace FalconerPacking

/-- The exact smoothed circle convolution is supported in the thickening of its actual data. -/
theorem circlePhysicalSchwartz_fourier_support_of_data {r ε : ℝ} (hr : 0 < r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 ε)
    (T : Set (EuclideanSpace ℝ (Fin 2)))
    (hT : ∀ ξ, ‖ξ‖ = r → g ξ ≠ 0 → ∀ z, ‖z‖ ≤ ε → ξ + z ∈ T) :
    Function.support (𝓕 (circlePhysicalSchwartz r hg k hk) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ⊆ T := by
  intro z hz
  by_contra hn
  apply hz
  rw [fourier_circlePhysicalSchwartz, circleSpectralSchwartz_apply]
  change (∫ ξ, g ξ * k (z - ξ) ∂normalizedCircleMeasure r) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [ae_circle_radial_representation hr] with ξ hξ
  by_cases hgzero : g ξ = 0
  · simp only [hgzero, zero_mul, Pi.zero_apply]
  by_cases hkzero : k (z - ξ) = 0
  · simp only [hkzero, mul_zero, Pi.zero_apply]
  have hnorm : ‖ξ‖ = r := by
    conv_lhs => rw [hξ]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_angularDirection, mul_one]
  have hzξ : ‖z - ξ‖ ≤ ε := by
    simpa only [mem_closedBall, dist_zero_right] using hkball hkzero
  have hmem := hT ξ hnorm hgzero (z - ξ) hzξ
  rw [add_sub_cancel] at hmem
  exact (hn hmem).elim

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)

/-- Actual grouped data occupy only the enlarged nominal coarse arc. -/
theorem coarseStandardCapData_circle_support {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (c : ℕ) {r : ℝ} (hr : 0 < r) (g : EuclideanSpace ℝ (Fin 2) → ℂ)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hnorm : ‖ξ‖ = r)
    (hξ : coarseStandardCapData ψ hψ hzero (M * N) (Nat.mul_pos hM hN) M c g ξ ≠ 0) :
    dist ξ (r • angularDirection (angularGridPoint N c)) < r * (6 * Real.pi / N) := by
  obtain ⟨j, hj, hdata⟩ : ∃ j ∈ (Finset.range (M * N)).filter (fun j ↦ j / M = c),
      standardCapData ψ hψ hzero (M * N) (Nat.mul_pos hM hN) j g ξ ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hξ (Finset.sum_eq_zero hn)
  have hcap := (mul_ne_zero_iff.mp hdata).1
  have hd := smoothAngularCap_direction_support ψ hψ hzero (M * N) (Nat.mul_pos hM hN) j hcap
  simp only [mem_ball, Nat.cast_mul] at hd
  have hc := standardCap_coarse_direction_bound hM hN j hd
  rw [(Finset.mem_filter.mp hj).2] at hc
  have he : r • (‖ξ‖⁻¹ • ξ) = ξ := by
    rw [hnorm, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  calc
    _ = dist (r • (‖ξ‖⁻¹ • ξ)) (r • angularDirection (angularGridPoint N c)) := by rw [he]
    _ = r * dist (‖ξ‖⁻¹ • ξ) (angularDirection (angularGridPoint N c)) := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
    _ < _ := mul_lt_mul_of_pos_left hc hr

/-- Every grouped coarse Fourier function is supported in one actual enclosing ancestor ball. -/
theorem coarseCapCircleSchwartz_fourier_ball {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    {r C : ℝ} (hr : 0 < r) (hscale : (N : ℝ) ≤ C * r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1) (c : ℕ) :
    Function.support (𝓕 (coarseCapCircleSchwartz ψ hψ hzero (M * N) (Nat.mul_pos hM hN)
      r hg k hk M c) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ⊆
      ball (r • angularDirection (angularGridPoint N c))
        ((6 * Real.pi + C + 1) * r / N) := by
  rw [coarseCapCircleSchwartz_eq_data]
  apply circlePhysicalSchwartz_fourier_support_of_data hr _ k hk hkball
  intro ξ hnorm hξ z hz
  have hd := coarseStandardCapData_circle_support ψ hψ hzero hM hN c hr g hnorm hξ
  have ht := dist_triangle (ξ + z) ξ (r • angularDirection (angularGridPoint N c))
  have he : dist (ξ + z) ξ = ‖z‖ := by rw [dist_eq_norm, add_sub_cancel_left]
  rw [he] at ht
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlast : r * (6 * Real.pi / N) + 1 < (6 * Real.pi + C + 1) * r / N := by
    rw [lt_div_iff₀ hN']
    have hmul : (r * (6 * Real.pi / N) + 1) * N = 6 * Real.pi * r + N := by field_simp
    rw [hmul]
    nlinarith
  exact (ht.trans (by linarith)).trans_lt hlast

/-- Actual grouped coarse Fourier supports have uniform overlap with no standard-label factor. -/
theorem coarseCapCircleSchwartz_fourier_overlap {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (hscale : (N : ℝ) ≤ C * r)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (hkball : Function.support k ⊆ closedBall 0 1) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun c ↦
      𝓕 (coarseCapCircleSchwartz ψ hψ hzero (M * N) (Nat.mul_pos hM hN) r hg k hk M c) ξ ≠ 0)).card ≤
        Nat.ceil (8 * Real.pi + C + 1) := by
  have hsub : (Finset.range N).filter (fun c ↦
      𝓕 (coarseCapCircleSchwartz ψ hψ hzero (M * N) (Nat.mul_pos hM hN) r hg k hk M c) ξ ≠ 0) ⊆
      (Finset.range N).filter (fun c ↦
        ξ ∈ ball (r • angularDirection (angularGridPoint N c))
          ((6 * Real.pi + C + 1) * r / N)) := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,
      coarseCapCircleSchwartz_fourier_ball ψ hψ hzero hM hN hr hscale hg k hk hkball c
        (Finset.mem_filter.mp hc).2⟩
  apply (Finset.card_le_card hsub).trans
  simpa only [add_assoc] using
    coarseCapLabels_ball_overlap hN hr (by positivity : 0 ≤ C + 1) ξ

end FalconerPacking
