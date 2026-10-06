/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicAnnularKernel
public import FalconerPacking.InitialCircleMultiplierRadius

/-!
# Fixed constants in the retained-energy estimate

The annular multiplier's zeroth seminorm is uniform over all scales and block sizes.
The other Fourier multipliers are fixed Schwartz functions, so their displayed integrals
are actual finite real constants.
-/

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

theorem norm_unitFrequencyCutoff_le_one (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖unitFrequencyCutoff ξ‖ ≤ 1 := by
  change ‖(unitFrequencyBump ξ : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg unitFrequencyBump.nonneg]
  exact unitFrequencyBump.le_one

/-- Each full annular multiplier has uniform size, independently of the block and shell. -/
theorem norm_fourier_dyadicAnnularKernel_le_two (T k : ℕ)
    (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖(𝓕 (dyadicAnnularKernel T k)) ξ‖ ≤ 2 := by
  rw [fourier_dyadicAnnularKernel]
  exact (norm_sub_le _ _).trans (by
    linarith [norm_unitFrequencyCutoff_le_one
      (((2 : ℝ) ^ (T * (k + 1)))⁻¹ • ξ),
      norm_unitFrequencyCutoff_le_one (((2 : ℝ) ^ (T * k))⁻¹ • ξ)])

theorem seminorm_fourier_dyadicAnnularKernel_zero_le_two (T k : ℕ) :
    SchwartzMap.seminorm ℝ 0 0 (𝓕 (dyadicAnnularKernel T k)) ≤ 2 := by
  apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (by norm_num)
  intro ξ
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
    norm_fourier_dyadicAnnularKernel_le_two T k ξ

theorem ofReal_sq_seminorm_fourier_dyadicAnnularKernel_le (T k : ℕ) :
    ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 (𝓕 (dyadicAnnularKernel T k))) ^ 2) ≤ 4 := by
  have hn := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (𝓕 (dyadicAnnularKernel T k))
  have hb := seminorm_fourier_dyadicAnnularKernel_zero_le_two T k
  have hh : (SchwartzMap.seminorm ℝ 0 0 (𝓕 (dyadicAnnularKernel T k))) ^ 2 ≤ 4 := by
    nlinarith
  exact_mod_cast ENNReal.ofReal_le_ofReal hh

theorem lintegral_enorm_unitReproducingKernel_eq_ofReal :
    (∫⁻ x, ‖unitReproducingKernel x‖ₑ) =
      ENNReal.ofReal (∫ x, ‖unitReproducingKernel x‖) := by
  exact (ofReal_integral_norm_eq_lintegral_enorm unitReproducingKernel.integrable).symm

theorem lintegral_sq_initialCircleMultiplierRadius_eq_ofReal (B : ℝ) :
    (∫⁻ x, ‖initialCircleMultiplierRadius B x‖ₑ ^ 2) =
      ENNReal.ofReal (∫ x, ‖initialCircleMultiplierRadius B x‖ ^ 2) := by
  have hi := ((initialCircleMultiplierRadius B).memLp 2 volume).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ ↦ sq_nonneg _)]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end FalconerPacking
