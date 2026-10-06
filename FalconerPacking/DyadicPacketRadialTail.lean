/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourcePacketRadialTail
public import FalconerPacking.DyadicInitialReconstruction

/-!
# Off-annulus Fourier bounds for every shell of the actual dyadic packet family

The packet parameter is arbitrary. In particular it can be the product of the angular
parameter and the regularization block length, while the shell index still ranges over
all natural numbers.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The actual dyadic multiplier has uniform radial margins inside the enlarged annulus. -/
theorem dyadicAnnularKernel_radial_margins (J n : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : ξ ∈ Function.support (𝓕 (dyadicAnnularKernel (4 * J) n) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) :
    2 * (2 : ℝ) ^ (4 * J * n) ≤ ‖ξ‖ ∧
      ‖ξ‖ ≤ (2 : ℝ) ^ (4 * J + 2) * 2 ^ (4 * J * n) := by
  constructor
  · exact (lt_of_not_ge fun he ↦
      hξ (fourier_dyadicAnnularKernel_eq_zero (4 * J) n (Or.inl he))).le
  · have h := lt_of_not_ge fun he ↦
      hξ (fourier_dyadicAnnularKernel_eq_zero (4 * J) n (Or.inr he))
    have he : 3 * (2 : ℝ) ^ (4 * J * (n + 1)) =
        3 * 2 ^ (4 * J) * 2 ^ (4 * J * n) := by
      rw [Nat.mul_add, Nat.mul_one, pow_add]
      ring
    rw [he] at h
    rw [pow_add]
    norm_num only [pow_two]
    nlinarith [show 0 < (2 : ℝ) ^ (4 * J) * 2 ^ (4 * J * n) by positivity]

/-- A single constant controls every actual retained source on every dyadic shell,
uniformly in the pin-dependent choices of standard labels and spatial strips. -/
theorem exists_dyadic_retained_fourier_radial_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {J : ℕ} (hJ : 0 < J) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M) (n : ℕ),
        let N := 64 * 2 ^ (2 * J * n)
        let hN : 0 < N := by dsimp only [N]; positivity
        let w := (2 : ℝ) ^ n / ((2 : ℝ) ^ n) ^ (2 * J)
        let ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
          𝓕 (dyadicAnnularKernel (4 * J) n)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) n
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) n
        let R := (2 : ℝ) ^ (4 * J * n)
        let U := (2 : ℝ) ^ (4 * J + 2) * R
        ∀ (G : Finset ℕ) (remote : ℕ → Finset ℤ), G ⊆ Finset.range N →
          (∀ j ∈ Finset.range N \ G, remote j ⊆ sourceWavePacketIndices χ hχ w) →
          ∀ ζ : EuclideanSpace ℝ (Fin 2), ‖ζ‖ ∉ Ioo R (2 * U) →
            ‖(𝓕 (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote)) ζ‖ ≤
              (C * μ.real univ * ((2 : ℝ) ^ n) ^ (10 * J + 2 * J * m)) *
                (R + ‖ζ‖) ^ (-(m : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := exists_initialRetainedSource_radial_tail_bound χ hχ m
  let F := ((2 : ℝ) ^ (8 * J) + 1) * ∫ ξ, ‖unitFrequencyCutoff ξ‖
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨64 * C * (F + 1), by positivity, ?_⟩
  intro μ _ M hμ n
  dsimp only
  intro G remote hG hremote ζ hζ
  let x : ℝ := 2 ^ n
  let N := 64 * 2 ^ (2 * J * n)
  have hN : 0 < N := by dsimp [N]; positivity
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hNreal : (N : ℝ) = 64 * x ^ (2 * J) := by
    dsimp [N, x]
    push_cast
    rw [← pow_mul]
    congr 2
    ring
  have hR : 0 < (2 : ℝ) ^ (4 * J * n) := by positivity
  have hRU : (2 : ℝ) ^ (4 * J * n) ≤
      (2 : ℝ) ^ (4 * J + 2) * 2 ^ (4 * J * n) := by
    exact le_mul_of_one_le_left hR.le (one_le_pow₀ (by norm_num))
  have hw := dyadic_initial_width_bounds hJ hx
  have hb := hc μ M hμ (𝓕 (dyadicAnnularKernel (4 * J) n))
    (hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) n)
    (fourier_dyadicAnnularKernel_eventually_zero (4 * J) n)
    N hN (x / x ^ (2 * J)) hw.1 hw.2.1 G remote hG hremote
    _ _ hR hRU (fun ξ hξ ↦ dyadicAnnularKernel_radial_margins J n hξ) ζ hζ
  have hf : (∫ ξ, ‖(𝓕 (dyadicAnnularKernel (4 * J) n)) ξ‖) ≤
      (F + 1) * x ^ (8 * J) := by
    have h := integral_norm_fourier_dyadicAnnularKernel_le (4 * J) n
    have he : (2 : ℝ) ^ (2 * (4 * J) * n) = x ^ (8 * J) := by
      dsimp [x]
      rw [← pow_mul]
      congr 1
      ring
    rw [he] at h
    apply h.trans
    dsimp [F]
    gcongr
    rw [show 2 * (4 * J) = 8 * J by omega]
    linarith
  have hwinv : (x / x ^ (2 * J))⁻¹ ^ m ≤ x ^ (2 * J * m) := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity) hw.2.2.2 m
  apply hb.trans
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, hNreal]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ C * (64 * x ^ (2 * J)) * x ^ (2 * J * m) * μ.real univ *
        ((F + 1) * x ^ (8 * J)) := by
      gcongr
    _ = _ := by
      rw [show 10 * J + 2 * J * m = 2 * J + 2 * J * m + 8 * J by omega,
        pow_add, pow_add]
      ring

end FalconerPacking
