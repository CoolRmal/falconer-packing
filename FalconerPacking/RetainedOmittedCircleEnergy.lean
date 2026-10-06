/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicPacketRadialTail
public import FalconerPacking.OmittedCircleEnergy

/-!
# Arbitrarily rapid omitted radial energy for actual retained packets

The spatially cut off packets have nonzero Fourier tails. Their proved radial envelopes
are integrated over the whole omitted radial region, uniformly in all retained subsets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The radial envelope estimate for finite pin measures, with the exact pin mass. -/
theorem lintegral_omitted_circle_energy_le_of_fourier_envelope_finite
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {S : Set ℝ} (hS : MeasurableSet S) {R p D : ℝ} (hR : 0 < R) (hp : 1 < p)
    (hD : 0 ≤ D)
    (hfourier : ∀ᵐ y ∂ν, ∀ ξ : EuclideanSpace ℝ (Fin 2), ‖ξ‖ ∈ Ioi 0 \ S →
      ‖𝓕 (f y : EuclideanSpace ℝ (Fin 2) → ℂ) ξ‖ ≤ D * (R + ‖ξ‖) ^ (-p)) :
    (∫⁻ r in Ioi (0 : ℝ) \ S, ENNReal.ofReal r *
      ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
        ν univ * ENNReal.ofReal (D ^ 2 * R ^ (2 - 2 * p) / (2 * p - 2)) := by
  calc
    _ ≤ ∫⁻ r in Ioi (0 : ℝ) \ S, (ENNReal.ofReal r *
        ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2)) * ν univ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.diff hS)] with r hr
      rw [mul_assoc]
      apply mul_le_mul_right
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2) ∂ν := by
          apply lintegral_mono_ae
          filter_upwards [hfourier] with y hy
          have hb : ‖pinnedSpectralCircleAverage (f y) y r‖ ≤
              D * (R + r) ^ (-p) := by
            apply norm_pinnedSpectralCircleAverage_le
            intro θ
            have hn : ‖r • angularDirection θ‖ = r := by
              rw [norm_smul, Real.norm_eq_abs, norm_angularDirection, mul_one,
                abs_of_pos hr.1]
            simpa only [hn] using hy (r • angularDirection θ) (by simpa only [hn] using hr)
          exact ENNReal.ofReal_le_ofReal
            ((sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg hD (Real.rpow_nonneg
                (add_nonneg hR.le (show 0 < r from hr.1).le) _))).mpr hb)
        _ = _ := lintegral_const _
    _ = (∫⁻ r in Ioi (0 : ℝ) \ S, ENNReal.ofReal r *
        ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2)) * ν univ :=
      lintegral_mul_const' _ _ (measure_ne_top ν univ)
    _ ≤ (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r *
        ENNReal.ofReal ((D * (R + r) ^ (-p)) ^ 2)) * ν univ :=
      mul_le_mul_left (lintegral_mono_set sdiff_subset) _
    _ ≤ _ := by
      rw [mul_comm (ν univ)]
      exact mul_le_mul_left (lintegral_radial_power_envelope_le hR hp) _

/-- The actual dyadic envelope has enough decay to absorb every polynomial cap count.
The derivative order `q + 7` already gives any requested power `q`. -/
theorem dyadic_radial_envelope_energy_le {x : ℝ} (hx : 1 ≤ x) {J : ℕ} (hJ : 0 < J)
    (q : ℕ) (C : ℝ) :
    (C * x ^ (10 * J + 2 * J * (q + 7))) ^ 2 *
        (x ^ (4 * J)) ^ (2 - 2 * ((q + 7 : ℕ) : ℝ)) /
          (2 * ((q + 7 : ℕ) : ℝ) - 2) ≤ C ^ 2 / x ^ q := by
  let m := q + 7
  have hx₀ : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hden : 1 ≤ 2 * (m : ℝ) - 2 := by dsimp [m]; push_cast; linarith
  have he : (x ^ (4 * J)) ^ (2 - 2 * (m : ℝ)) =
      x ^ (8 * J) / x ^ (8 * J * m) := by
    rw [show 2 - 2 * (m : ℝ) = (2 : ℝ) - ((2 * m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_sub (by positivity)]
    simp only [Real.rpow_natCast, Real.rpow_two, ← pow_mul]
    rw [show 4 * J * 2 = 8 * J by ring, show 4 * J * (2 * m) = 8 * J * m by ring]
  have hpow : 28 * J + 4 * J * m + q ≤ 8 * J * m := by
    have hJq : q ≤ J * q := by nlinarith
    dsimp [m]
    nlinarith
  calc
    _ ≤ (C * x ^ (10 * J + 2 * J * m)) ^ 2 *
        (x ^ (4 * J)) ^ (2 - 2 * (m : ℝ)) := div_le_self (by positivity) hden
    _ = C ^ 2 * (x ^ (28 * J + 4 * J * m) / x ^ (8 * J * m)) := by
      rw [he, mul_pow, ← pow_mul]
      rw [show 28 * J + 4 * J * m = (10 * J + 2 * J * m) * 2 + 8 * J by ring,
        pow_add]
      ring
    _ ≤ C ^ 2 * (1 / x ^ q) :=
      mul_le_mul_of_nonneg_left (dyadic_initial_power_ratio hx hpow) (sq_nonneg C)
    _ = _ := by ring

/-- Every pin-dependent choice of actual retained packets has arbitrarily rapid omitted
radial energy. The zero option allows the family to vanish outside its chosen pin cells.
No spatial measurability or Fourier-tail hypothesis is substituted for the packet construction. -/
theorem exists_retained_omitted_circle_energy_rapid
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {J : ℕ} (hJ : 0 < J) (q : ℕ) :
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
        ∀ (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
          (f : EuclideanSpace ℝ (Fin 2) → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ),
          (∀ᵐ y ∂ν, f y = 0 ∨ ∃ (G : Finset ℕ) (remote : ℕ → Finset ℤ),
            G ⊆ Finset.range N ∧
            (∀ j ∈ Finset.range N \ G, remote j ⊆ sourceWavePacketIndices χ hχ w) ∧
            f y = initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote) →
          (∫⁻ r in Ioi (0 : ℝ) \ Ioo R (2 * U), ENNReal.ofReal r *
            ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
              ν univ * ENNReal.ofReal (C * (μ.real univ) ^ 2 / ((2 : ℝ) ^ n) ^ q) := by
  let m := q + 7
  obtain ⟨C, hC, hc⟩ := exists_dyadic_retained_fourier_radial_bound χ hχ hJ m
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro μ _ M hμ n
  dsimp only
  intro ν _ f hfamily
  let x : ℝ := 2 ^ n
  let R : ℝ := 2 ^ (4 * J * n)
  let U : ℝ := 2 ^ (4 * J + 2) * R
  let D := C * μ.real univ * x ^ (10 * J + 2 * J * m)
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hm : (1 : ℝ) < m := by dsimp [m]; push_cast; linarith
  have hfourier : ∀ᵐ y ∂ν, ∀ ξ : EuclideanSpace ℝ (Fin 2),
      ‖ξ‖ ∈ Ioi 0 \ Ioo R (2 * U) →
      ‖𝓕 (f y : EuclideanSpace ℝ (Fin 2) → ℂ) ξ‖ ≤ D * (R + ‖ξ‖) ^ (-(m : ℝ)) := by
    filter_upwards [hfamily] with y hy
    intro ξ hξ
    rcases hy with he | ⟨G, remote, hG, hremote, he⟩
    · rw [he, ← SchwartzMap.fourier_coe, FourierTransform.fourier_zero]
      simp only [FunLike.coe_zero, Pi.zero_apply, norm_zero]
      exact mul_nonneg hD (Real.rpow_nonneg (by positivity) _)
    · rw [he, ← SchwartzMap.fourier_coe]
      exact hc μ M hμ n G remote hG hremote ξ hξ.2
  apply (lintegral_omitted_circle_energy_le_of_fourier_envelope_finite ν f
    measurableSet_Ioo hR hm hD hfourier).trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  have hRreal : R = x ^ (4 * J) := by
    dsimp [R, x]
    rw [← pow_mul]
    congr 1
    ring
  have hx : 1 ≤ x := one_le_pow₀ (by norm_num)
  simpa only [D, hRreal, mul_pow] using
    dyadic_radial_envelope_energy_le hx hJ q (C * μ.real univ)

end FalconerPacking
