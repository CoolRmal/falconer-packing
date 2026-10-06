/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RescaledAnnularFactor
public import FalconerPacking.RescaledAngularDerivatives

/-!
# Uniform derivative bounds for the actual rescaled dyadic caps

The angular estimates and the fixed radial factor give all derivatives on the positive radial
chart. The common compact support and its positive radial margin handle the rest of the plane.
-/

@[expose] public section

noncomputable section

open Set Metric SchwartzMap FourierTransform Classical
open scoped ContDiff

namespace FalconerPacking

/-- The actual angular factor has uniform derivatives on any bounded positive radial chart. -/
theorem capUnitAngular_derivative_bound (T : ℕ) {K : ℝ} (hK : 0 ≤ K) (M : ℝ) (m : ℕ) :
    ∃ C > 0, ∀ (n N : ℕ) (hN : 0 < N) (j : ℕ) (z : EuclideanSpace ℝ (Fin 2)),
      (N : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n)) →
      ‖z‖ ≤ M → 1 ≤ z 1 →
      ‖iteratedFDeriv ℝ m (fun w ↦ angularCapWeight N hN j
        (capUnitRescaling T n N j w)) z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := angularCapWeight_anisotropic_derivative_bound
    (by norm_num : (0 : ℝ) < 1 / 2) (max 1 M) hK m
  refine ⟨C, hC, ?_⟩
  intro n N hN j z hupper hz hz₁
  let ε := (Real.sqrt ((2 : ℝ) ^ (T * n)))⁻¹
  let ρ := ε / (2 * Real.pi / N)
  have hδ : 0 < 2 * Real.pi / (N : ℝ) := by positivity
  have hroot : 0 < Real.sqrt ((2 : ℝ) ^ (T * n)) := by positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hε₁ : ε ≤ 1 := inv_le_one_of_one_le₀
    (Real.one_le_sqrt.mpr (one_le_pow₀ (by norm_num)))
  have hρ : |ρ| ≤ K := by
    have he : ρ = (N : ℝ) / (2 * Real.pi * Real.sqrt ((2 : ℝ) ^ (T * n))) := by
      dsimp [ρ, ε]
      field_simp
    rw [he, abs_of_nonneg (by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [hupper]
  have hscale : (2 * Real.pi / N) * ρ = ε := by dsimp [ρ]; field_simp
  have hp : ‖(ε, z)‖ ≤ max 1 M := by
    rw [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hε]
    exact max_le (hε₁.trans (le_max_left _ _)) (hz.trans (le_max_right _ _))
  have he := hbound N hN j (circleCapFrame (angularGridPoint N j)).symm ε ρ z
    hscale hρ hp (by linarith)
  simpa only [capUnitRescaling_apply, ε] using he

/-- Common compact support remains valid after taking closures. -/
theorem rescaledDyadicAngularCap_tsupport_ball (T n N : ℕ) (hN : 0 < N)
    (hwidth : Real.sqrt ((2 : ℝ) ^ (T * n)) ≤ N) (j : ℕ) :
    tsupport (rescaledDyadicAngularCap T n N hN j) ⊆
      closedBall 0 ((12 * Real.pi + 3) * (2 : ℝ) ^ T) :=
  closure_minimal (rescaledDyadicAngularCap_support_ball T n N hN hwidth j) isClosed_closedBall

private theorem capUnitAngular_contDiffAt (T n N : ℕ) (hN : 0 < N) (j : ℕ)
    {z : EuclideanSpace ℝ (Fin 2)} (hz : 1 ≤ z 1) :
    ContDiffAt ℝ ∞ (fun w ↦ angularCapWeight N hN j (capUnitRescaling T n N j w)) z := by
  have hz₀ : z ≠ 0 := by
    intro he
    simp only [he, PiLp.zero_apply] at hz
    norm_num at hz
  have he := (capUnitRescaling T n N j).map_ne_zero_iff.mpr hz₀
  exact (contDiffAt_angularCapWeight N hN j he).comp z
    (capUnitRescaling T n N j).contDiff.contDiffAt

/-- Every derivative of the actual rescaled Schwartz symbol is uniformly bounded. -/
theorem rescaledDyadicAngularCap_derivative_bound (T : ℕ) {K : ℝ} (hK : 0 ≤ K) (m : ℕ) :
    ∃ C > 0, ∀ (n N : ℕ) (hN : 0 < N) (j : ℕ) (z : EuclideanSpace ℝ (Fin 2)),
      Real.sqrt ((2 : ℝ) ^ (T * n)) ≤ N → 4 * Real.pi ≤ N →
      (N : ℝ) ≤ 2 * Real.pi * K * Real.sqrt ((2 : ℝ) ^ (T * n)) →
      ‖iteratedFDeriv ℝ m (rescaledDyadicAngularCap T n N hN j) z‖ ≤ C := by
  let M := (12 * Real.pi + 3) * (2 : ℝ) ^ T
  choose A hA hAb using fun k ↦ capUnitAngular_derivative_bound T hK M k
  let ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ := 𝓕 (dyadicAnnularKernel T 0)
  let C := ∑ k ∈ Finset.range (m + 1),
    (m.choose k : ℝ) * A k * SchwartzMap.seminorm ℂ 0 (m - k) ψ
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hA k).le) (apply_nonneg _ _))
  refine ⟨C + 1, by positivity, ?_⟩
  intro n N hN j z hwidth hsmall hupper
  by_cases hd : iteratedFDeriv ℝ m (rescaledDyadicAngularCap T n N hN j) z = 0
  · simp only [hd, norm_zero]
    positivity
  have hz := support_iteratedFDeriv_subset m hd
  have hz₁ := rescaledDyadicAngularCap_tsupport_radial T n N hN hsmall j hz
  have hzM : ‖z‖ ≤ M := by
    simpa only [mem_closedBall, dist_zero_right] using
      rescaledDyadicAngularCap_tsupport_ball T n N hN hwidth j hz
  have he : (rescaledDyadicAngularCap T n N hN j : EuclideanSpace ℝ (Fin 2) → ℂ) =
      fun w ↦ angularCapWeight N hN j (capUnitRescaling T n N j w) •
        ψ (capUnitRescaling T n N j w) := funext (rescaledDyadicAngularCap_factor T n N hN j)
  rw [he]
  have hψ : ContDiffAt ℝ ∞ (fun w ↦ ψ (capUnitRescaling T n N j w)) z :=
    (ψ.smooth ⊤).contDiffAt.comp z (capUnitRescaling T n N j).contDiff.contDiffAt
  apply (norm_iteratedFDeriv_smul_le_at (capUnitAngular_contDiffAt T n N hN j hz₁) hψ m).trans
  apply le_trans (Finset.sum_le_sum fun k _ ↦ ?_) (show C ≤ C + 1 by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hAb k n N hN j z hupper hzM hz₁)
    (by positivity)) (rescaledAnnularFactor_derivative_bound T (m - k) n N j z)
    (norm_nonneg _) (mul_nonneg (by positivity) (hA k).le)

end FalconerPacking
