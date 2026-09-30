/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicBandSum
import FalconerPacking.ProjectionFourier

/-!
# From dyadic band estimates to a full Fourier integral

The integer dyadic bands cover the positive half-line. Their scalar estimates therefore
control the full integral of an even nonnegative Fourier energy.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

theorem positive_subset_iUnion_dyadic_band :
    Ioi (0 : ℝ) ⊆ ⋃ n : ℤ, Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n) := by
  intro x hx
  obtain ⟨n, hn, hn'⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)
  refine mem_iUnion.mpr ⟨n, ?_, ?_⟩
  · have hpos : 0 < (2 : ℝ) ^ n := zpow_pos (by norm_num) _
    linarith
  · simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hn'

/-- A dyadic gain bound gives a quantitative positive-frequency integral estimate. -/
theorem lintegral_Ioi_le_of_dyadicBandTerm {f : ℝ → ℝ≥0∞} {s δ B : ℝ}
    {A : ℝ≥0∞} (hs : 1 < s) (hs' : s < 3) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hband : ∀ n : ℤ,
      ∫⁻ τ in Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n), f τ ≤
        A * ENNReal.ofReal (B * dyadicBandTerm δ s n)) :
    ∫⁻ τ in Ioi (0 : ℝ), f τ ≤
      A * ENNReal.ofReal (B * dyadicBandSumConstant s * δ ^ (s - 1)) := by
  obtain ⟨hsm, hsum⟩ := summable_dyadicBandTerm_and_tsum_le hs hs' hδ
  calc
    _ ≤ ∫⁻ τ in ⋃ n : ℤ, Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n), f τ :=
      lintegral_mono_set positive_subset_iUnion_dyadic_band
    _ ≤ ∑' n : ℤ, ∫⁻ τ in Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n), f τ :=
      lintegral_iUnion_le _ f
    _ ≤ ∑' n : ℤ, A * ENNReal.ofReal (B * dyadicBandTerm δ s n) :=
      ENNReal.tsum_le_tsum hband
    _ = A * ENNReal.ofReal (B * ∑' n : ℤ, dyadicBandTerm δ s n) := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
        (fun n ↦ mul_nonneg hB (dyadicBandTerm_nonneg δ s n)) (hsm.mul_left B),
        tsum_mul_left]
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hB))

/-- Evenness doubles the positive half-line integral; the origin has zero measure. -/
theorem lintegral_eq_two_mul_Ioi_of_even {f : ℝ → ℝ≥0∞}
    (hf : ∀ x, f (-x) = f x) : ∫⁻ x, f x = 2 * ∫⁻ x in Ioi (0 : ℝ), f x := by
  rw [← lintegral_add_compl f measurableSet_Ioi, compl_Ioi,
    ← setLIntegral_congr Iio_ae_eq_Iic, lintegral_Iio_eq_Ioi_of_even hf, two_mul]

/-- Even Fourier energies inherit the full displacement power from their dyadic bands. -/
theorem lintegral_le_of_even_of_dyadicBandTerm {f : ℝ → ℝ≥0∞} {s δ B : ℝ}
    {A : ℝ≥0∞} (hs : 1 < s) (hs' : s < 3) (hδ : 0 < δ) (hB : 0 ≤ B)
    (heven : ∀ x, f (-x) = f x)
    (hband : ∀ n : ℤ,
      ∫⁻ τ in Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n), f τ ≤
        A * ENNReal.ofReal (B * dyadicBandTerm δ s n)) :
    ∫⁻ τ, f τ ≤
      A * ENNReal.ofReal (2 * B * dyadicBandSumConstant s * δ ^ (s - 1)) := by
  rw [lintegral_eq_two_mul_Ioi_of_even heven]
  refine (mul_le_mul' le_rfl
    (lintegral_Ioi_le_of_dyadicBandTerm hs hs' hδ hB hband)).trans_eq ?_
  rw [show 2 * B * dyadicBandSumConstant s * δ ^ (s - 1) =
    2 * (B * dyadicBandSumConstant s * δ ^ (s - 1)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  ring

/-- The same bound holds after integrating over a possibly correlated parameter space. -/
theorem lintegral_joint_le_of_even_of_dyadicBandTerm
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    {f : α → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f)) {s δ B : ℝ}
    {A : ℝ≥0∞} (hs : 1 < s) (hs' : s < 3) (hδ : 0 < δ) (hB : 0 ≤ B)
    (heven : ∀ z x, f z (-x) = f z x)
    (hband : ∀ n : ℤ,
      ∫⁻ z, ∫⁻ τ in Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n), f z τ ∂volume ∂κ ≤
        A * ENNReal.ofReal (B * dyadicBandTerm δ s n)) :
    ∫⁻ z, ∫⁻ τ, f z τ ∂volume ∂κ ≤
      A * ENNReal.ofReal (2 * B * dyadicBandSumConstant s * δ ^ (s - 1)) := by
  rw [lintegral_lintegral_swap hf.aemeasurable]
  apply lintegral_le_of_even_of_dyadicBandTerm hs hs' hδ hB
    (fun x ↦ lintegral_congr (fun z ↦ heven z x))
  intro n
  rw [← lintegral_lintegral_swap hf.aemeasurable]
  exact hband n

end FalconerPacking
