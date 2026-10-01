/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AngularBumpDerivatives
import FalconerPacking.CircularPacketAmplitude
import FalconerPacking.LocalCompositionBounds

/-!
# A smooth periodic selector for enlarged angular caps

The selector is a fixed compact smooth bump of the normalized frequency direction. It is one
on chord distance at most `8π/S` and supported where that distance is less than `16π/S`.
Its restrictions to positive-radius circles have uniform derivative bounds of order `S^k`.
-/

noncomputable section

open Set Metric Function SchwartzMap
open scoped ContDiff

namespace FalconerPacking

/-- The periodic angular window with center vector `c`. -/
def angularSpectralWindow (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) : ℝ :=
  angularUnitSchwartz ((S / (8 * Real.pi)) • (angularDirection θ - c))

/-- The corresponding actual multiplier on frequency space, defined measurably also at zero. -/
def angularSpectralSelector (S : ℝ) (c ξ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  angularUnitSchwartz ((S / (8 * Real.pi)) • (‖ξ‖⁻¹ • ξ - c))

theorem measurable_angularSpectralSelector (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) :
    Measurable (angularSpectralSelector S c) := by
  unfold angularSpectralSelector
  fun_prop

theorem angularSpectralSelector_mem_Icc (S : ℝ) (c ξ : EuclideanSpace ℝ (Fin 2)) :
    angularSpectralSelector S c ξ ∈ Icc (0 : ℝ) 1 :=
  ⟨angularUnitBump.nonneg, angularUnitBump.le_one⟩

theorem angularSpectralSelector_circle (S : ℝ) (c : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    angularSpectralSelector S c (r • angularDirection θ) = angularSpectralWindow S c θ := by
  simp only [angularSpectralSelector, angularSpectralWindow, norm_smul, Real.norm_eq_abs,
    norm_angularDirection, mul_one, abs_of_pos hr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem contDiff_angularSpectralWindow (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ∞ (angularSpectralWindow S c) := by
  exact (angularUnitSchwartz.smooth ⊤).comp
    ((contDiff_angularDirection.sub contDiff_const).const_smul _)

theorem periodic_angularSpectralWindow (S : ℝ) (c : EuclideanSpace ℝ (Fin 2)) :
    Periodic (angularSpectralWindow S c) (2 * Real.pi) := by
  intro θ
  simp [angularSpectralWindow, angularDirection, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- The inner closed chord cap is selected without any loss. -/
theorem angularSpectralSelector_eq_one {S : ℝ} (hS : 0 < S)
    {c ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ‖‖ξ‖⁻¹ • ξ - c‖ ≤ 8 * Real.pi / S) :
    angularSpectralSelector S c ξ = 1 := by
  apply angularUnitBump.one_of_mem_closedBall
  change ‖(S / (8 * Real.pi)) • (‖ξ‖⁻¹ • ξ - c) - 0‖ ≤ 1
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc
    _ ≤ (S / (8 * Real.pi)) * (8 * Real.pi / S) := by gcongr
    _ = 1 := by field_simp

/-- Every nonzero selected frequency lies in the enlarged chord cap. -/
theorem angularSpectralSelector_support {S : ℝ} (hS : 0 < S)
    {c ξ : EuclideanSpace ℝ (Fin 2)} (hξ : angularSpectralSelector S c ξ ≠ 0) :
    ‖‖ξ‖⁻¹ • ξ - c‖ < 16 * Real.pi / S := by
  have hb : (S / (8 * Real.pi)) • (‖ξ‖⁻¹ • ξ - c) ∈ support angularUnitBump := hξ
  rw [angularUnitBump.support_eq] at hb
  change ‖(S / (8 * Real.pi)) • (‖ξ‖⁻¹ • ξ - c) - 0‖ < 2 at hb
  rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hb
  have he : S / (8 * Real.pi) * (16 * Real.pi / S) = 2 := by field_simp; ring
  exact (mul_lt_mul_iff_right₀ (by positivity : 0 < S / (8 * Real.pi))).mp (he ▸ hb)

/-- All angular derivatives have uniform constants, independent of the center and circle radius. -/
theorem angularSpectralWindow_derivative_bound (m : ℕ) :
    ∃ C > 0, ∀ S : ℝ, 1 ≤ S → ∀ (c : EuclideanSpace ℝ (Fin 2)) (θ : ℝ),
      ‖iteratedDeriv m (angularSpectralWindow S c) θ‖ ≤ C * S ^ m := by
  let B := 1 + ∑ k ∈ Finset.range (m + 1), SchwartzMap.seminorm ℝ 0 k angularUnitSchwartz
  have hB : 0 < B := by
    have := Finset.sum_nonneg (fun k (_ : k ∈ Finset.range (m + 1)) ↦
      apply_nonneg (SchwartzMap.seminorm ℝ 0 k) angularUnitSchwartz)
    dsimp [B]
    linarith
  have hBk (k : ℕ) (hk : k ≤ m) : SchwartzMap.seminorm ℝ 0 k angularUnitSchwartz ≤ B := by
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.range (m + 1)) ↦
        apply_nonneg (SchwartzMap.seminorm ℝ 0 j) angularUnitSchwartz)
      (show k ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
    dsimp [B]
    linarith
  refine ⟨m.factorial * B, by positivity, ?_⟩
  intro S hS c θ
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have ha : 0 < S / (8 * Real.pi) := by positivity
  have haS : S / (8 * Real.pi) ≤ S := by
    apply div_le_self hS₀.le
    nlinarith [Real.two_le_pi]
  have hf : ContDiff ℝ ∞ (fun y ↦ angularUnitSchwartz ((S / (8 * Real.pi)) • (y - c))) :=
    (angularUnitSchwartz.smooth ⊤).comp ((contDiff_id.sub contDiff_const).const_smul _)
  have h := norm_iteratedFDeriv_comp_le_at (x := θ) hf contDiff_angularDirection.contDiffAt m
    (C := B * S ^ m) (D := 1) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h
    change ‖iteratedDeriv m ((fun y ↦ angularUnitSchwartz
      ((S / (8 * Real.pi)) • (y - c))) ∘ angularDirection) θ‖ ≤ _
    simpa only [one_pow, mul_one, mul_assoc] using h
  · intro k hk
    apply (norm_iteratedFDeriv_schwartz_dilate_translate_le _ k _ _ _).trans
    rw [abs_of_pos ha]
    apply mul_le_mul (hBk k hk) _ (pow_nonneg ha.le k) hB.le
    exact (pow_le_pow_left₀ ha.le haS k).trans (pow_le_pow_right₀ hS hk)
  · intro k hk hkm
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_angularDirection,
      norm_angularDirection, one_pow]

end FalconerPacking
