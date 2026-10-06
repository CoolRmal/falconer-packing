/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.StandardCapKernelBounds
public import FalconerPacking.PhysicalCapRadialTails

/-!
# Actual spectral first norms and radial tails on the standard dyadic grid
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped ENNReal FourierTransform

namespace FalconerPacking

theorem integral_norm_fourier_lowpassSchwartzKernel (a : ℝ) (ha : 0 < a) :
    (∫ ξ, ‖(𝓕 (lowpassSchwartzKernel a ha) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ‖) =
      a ^ 2 * ∫ ξ, ‖unitFrequencyCutoff ξ‖ := by
  simp_rw [fourier_lowpassSchwartzKernel]
  simpa only [finrank_euclideanSpace, Fintype.card_fin, abs_of_nonneg (sq_nonneg a),
    smul_eq_mul] using Measure.integral_comp_inv_smul volume (fun ξ ↦ ‖unitFrequencyCutoff ξ‖) a

/-- A rough quadratic spectral norm bound follows from the actual low-pass rescaling. -/
theorem integral_norm_fourier_dyadicAnnularKernel_le (T n : ℕ) :
    (∫ ξ, ‖(𝓕 (dyadicAnnularKernel T n) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ‖) ≤
      ((2 : ℝ) ^ (2 * T) + 1) * (∫ ξ, ‖unitFrequencyCutoff ξ‖) * 2 ^ (2 * T * n) := by
  have he : (𝓕 (dyadicAnnularKernel T n) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) =
      𝓕 (lowpassSchwartzKernel (2 ^ (T * (n + 1))) (by positivity)) -
      𝓕 (lowpassSchwartzKernel (2 ^ (T * n)) (by positivity)) := by
    exact map_sub (SchwartzMap.fourierTransformCLM ℂ) _ _
  rw [he]
  calc
    _ ≤ (∫ ξ, ‖(𝓕 (lowpassSchwartzKernel (2 ^ (T * (n + 1))) (by positivity)) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ‖) +
        ∫ ξ, ‖(𝓕 (lowpassSchwartzKernel (2 ^ (T * n)) (by positivity)) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ξ‖ := by
      rw [← integral_add (𝓕 (lowpassSchwartzKernel _ _)).integrable.norm
        (𝓕 (lowpassSchwartzKernel _ _)).integrable.norm]
      exact integral_mono ((𝓕 (lowpassSchwartzKernel _ _) -
          𝓕 (lowpassSchwartzKernel _ _) :
            SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ).integrable.norm)
        ((𝓕 (lowpassSchwartzKernel _ _)).integrable.norm.add
          (𝓕 (lowpassSchwartzKernel _ _)).integrable.norm) (fun _ ↦ norm_sub_le _ _)
    _ = _ := by
      rw [integral_norm_fourier_lowpassSchwartzKernel, integral_norm_fourier_lowpassSchwartzKernel]
      rw [Nat.mul_add, pow_add]
      simp only [Nat.mul_one, mul_pow]
      rw [← pow_mul, ← pow_mul, show T * n * 2 = 2 * T * n by ring,
        show T * 2 = 2 * T by ring]
      ring

theorem integral_norm_dyadicAngularCap_le (T n N : ℕ) (hN : 0 < N) {j : ℕ} (hj : j < N) :
    (∫ ξ, ‖dyadicAngularCap T n N hN j ξ‖) ≤
      ((2 : ℝ) ^ (2 * T) + 1) * (∫ ξ, ‖unitFrequencyCutoff ξ‖) * 2 ^ (2 * T * n) :=
  (integral_mono (dyadicAngularCap T n N hN j).integrable.norm
    (𝓕 (dyadicAnnularKernel T n)).integrable.norm
    (norm_smoothAngularCap_le _ _ _ N hN hj)).trans
    (integral_norm_fourier_dyadicAnnularKernel_le T n)

/-- Real first-norm and radial-tail constants are uniform on the constructed standard grid. -/
theorem exists_standard_dyadic_kernel_real_bounds (J m : ℕ) :
    ∃ C₀ C₁ : ℝ, 0 < C₀ ∧ 0 < C₁ ∧ ∀ n j : ℕ,
      let N := 64 * 2 ^ (2 * J * n)
      let hN : 0 < N := by dsimp only [N]; positivity
      (∫ x, ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j) :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖) ≤ C₀ ∧
      ∀ δ : ℝ, 0 < δ →
        (∫ x in {x | δ ≤ ‖x‖}, ‖(𝓕⁻ (dyadicAngularCap (4 * J) n N hN j) :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖) ≤
          C₁ / ((2 : ℝ) ^ (2 * J * n) * δ) ^ m := by
  obtain ⟨C₀, _, hC₀, _, hc₀⟩ := exists_uniform_standardCapKernel_bounds J m
  let ni (i : ℕ × ℕ) := i.1
  let Ni (i : ℕ × ℕ) := 64 * 2 ^ (2 * J * i.1)
  let ji (i : ℕ × ℕ) := i.2
  have hNi (i : ℕ × ℕ) : 0 < Ni i := (standard_fourfold_angular_grid_bounds J i.1).1
  obtain ⟨C₁, hC₁, hc₁⟩ := dyadicCapKernel_uniform_radial_tail (4 * J)
    (by norm_num : (0 : ℝ) ≤ 32) ni Ni ji hNi
    (fun i ↦ (standard_fourfold_angular_grid_bounds J i.1).2.1)
    (fun i ↦ (standard_fourfold_angular_grid_bounds J i.1).2.2.1)
    (fun i ↦ (standard_fourfold_angular_grid_bounds J i.1).2.2.2) m
  refine ⟨C₀, C₁, hC₀, hC₁, fun n j ↦ ⟨?_, ?_⟩⟩
  · have h := (hc₀ n j).1
    rw [← ofReal_integral_norm_eq_lintegral_enorm (𝓕⁻ (dyadicAngularCap _ _ _ _ _)).integrable]
      at h
    exact (ENNReal.ofReal_le_ofReal_iff hC₀.le).mp h
  · intro δ hδ
    have h := hc₁ (n, j) δ hδ
    dsimp only [ni, Ni, ji] at h
    rw [← ofReal_integral_norm_eq_lintegral_enorm
      (𝓕⁻ (dyadicAngularCap _ _ _ _ _)).integrable.restrict] at h
    rw [show (4 * J) * n = 2 * (2 * J * n) by ring,
      sqrt_even_dyadic_frequency] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end FalconerPacking
