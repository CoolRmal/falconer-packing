/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.BandlimitedCutoff
import FalconerPacking.OrientedReproducingKernel

/-!
# Translated and rescaled spatial cutoffs

The constructed cutoff is transported to any spatial ball. Its Fourier radius is the
reciprocal spatial radius, and its rapid decay constants are independent of center and scale.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform SchwartzMap
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The Fourier transform under an arbitrary invertible real linear change of coordinates. -/
theorem fourier_comp_continuousLinearEquiv
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (f ∘ A) ξ = |A.toLinearEquiv.toLinearMap.det|⁻¹ •
      𝓕 f (A.symm.toContinuousLinearMap.adjoint ξ) := by
  let g : EuclideanSpace ℝ (Fin 2) → ℂ := fun z ↦
    𝐞 (-⟪z, A.symm.toContinuousLinearMap.adjoint ξ⟫) • f z
  have hinner (x : EuclideanSpace ℝ (Fin 2)) :
      ⟪A x, A.symm.toContinuousLinearMap.adjoint ξ⟫ = ⟪x, ξ⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp
  calc
    _ = ∫ x, g (A x) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by simp only [g, Function.comp_apply, hinner]
    _ = _ := integral_comp_continuousLinearEquiv_det A g

/-- The actual cutoff transported to the ball of radius s around c. -/
def scaledFourierCutoff (s : ℝ) (hs : 0 < s) (c : EuclideanSpace ℝ (Fin 2)) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  compSubConstCLM ℂ c (compCLMOfContinuousLinearEquiv ℂ
    (orientedRectangleDilation (LinearIsometryEquiv.refl ℝ _) s s hs hs) localFourierCutoff)

/-- The constructed cutoff has the intended elementary spatial formula. -/
theorem scaledFourierCutoff_apply (s : ℝ) (hs : 0 < s)
    (c x : EuclideanSpace ℝ (Fin 2)) :
    scaledFourierCutoff s hs c x = localFourierCutoff (s⁻¹ • (x - c)) := by
  change localFourierCutoff
    (orientedRectangleDilation (LinearIsometryEquiv.refl ℝ _) s s hs hs (x - c)) = _
  congr 1
  ext i
  fin_cases i
  · simp [orientedRectangleDilation_apply_zero, div_eq_mul_inv]
    ring
  · simp [orientedRectangleDilation_apply_one, div_eq_mul_inv]
    ring

/-- The cutoff is at least one in modulus on the prescribed spatial ball. -/
theorem one_le_norm_scaledFourierCutoff (s : ℝ) (hs : 0 < s)
    (c x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x - c‖ ≤ s) :
    1 ≤ ‖scaledFourierCutoff s hs c x‖ := by
  rw [scaledFourierCutoff_apply]
  apply one_le_norm_localFourierCutoff
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  calc
    s⁻¹ * ‖x - c‖ ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hs.le)
    _ = 1 := inv_mul_cancel₀ hs.ne'

/-- The spatial scale gives the exact reciprocal upper bound for the Fourier support. -/
theorem support_fourier_scaledFourierCutoff (s : ℝ) (hs : 0 < s)
    (c : EuclideanSpace ℝ (Fin 2)) :
    Function.support (fun ξ ↦ 𝓕 (scaledFourierCutoff s hs c) ξ) ⊆ ball 0 s⁻¹ := by
  intro ξ hξ
  by_contra hnot
  let A := orientedRectangleDilation (LinearIsometryEquiv.refl ℝ
    (EuclideanSpace ℝ (Fin 2))) s s hs hs
  let w := compCLMOfContinuousLinearEquiv ℂ A localFourierCutoff
  have hdual : A.symm.toContinuousLinearMap.adjoint ξ = s • ξ := by
    rw [orientedRectangleDilation_dual]
    ext i
    fin_cases i <;> simp
  have hzero : 𝓕 localFourierCutoff (s • ξ) = 0 := by
    by_contra hne
    have hmem := support_fourier_localFourierCutoff hne
    have hnorm : s * ‖ξ‖ < 1 := by
      simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs] using hmem
    apply hnot
    rw [mem_ball, dist_zero_right]
    rw [← one_div]
    exact (lt_div_iff₀ hs).mpr (by simpa only [mul_comm] using hnorm)
  have hFw : 𝓕 w ξ = 0 := by
    rw [fourier_coe, compCLMOfContinuousLinearEquiv_apply,
      fourier_comp_continuousLinearEquiv, hdual]
    change |A.toLinearEquiv.toLinearMap.det|⁻¹ •
      (𝓕 localFourierCutoff (s • ξ)) = 0
    rw [hzero, smul_zero]
  have ht := congrFun (VectorFourier.fourierIntegral_comp_add_right 𝐞 volume
    (innerₗ (EuclideanSpace ℝ (Fin 2))) (w : EuclideanSpace ℝ (Fin 2) → ℂ) (-c)) ξ
  apply hξ
  change 𝓕 (fun x ↦ w (x + -c)) ξ = _ at ht
  change 𝓕 (fun x ↦ w (x - c)) ξ = 0
  simp only [sub_eq_add_neg]
  rw [ht]
  change 𝐞 ⟪-c, ξ⟫ • 𝓕 w ξ = 0
  rw [hFw, smul_zero]

/-- The decay constants are uniform over all centers and positive spatial scales. -/
theorem scaledFourierCutoff_decay (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s (hs : 0 < s) c x,
      ‖scaledFourierCutoff s hs c x‖ ≤ C / (1 + ‖x - c‖ / s) ^ m := by
  let C := 2 ^ m * (Finset.Iic (m, 0)).sup
    (fun p ↦ SchwartzMap.seminorm ℝ p.1 p.2) localFourierCutoff
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro s hs c x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (m, 0))
    le_rfl le_rfl localFourierCutoff (s⁻¹ • (x - c))
  rw [scaledFourierCutoff_apply]
  apply (le_div_iff₀ (by positivity : 0 < (1 + ‖x - c‖ / s) ^ m)).mpr
  have heq : ‖s⁻¹ • (x - c)‖ = ‖x - c‖ / s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), div_eq_mul_inv, mul_comm]
  simp only [norm_iteratedFDeriv_zero, heq] at h
  calc
    _ ≤ C := by simpa only [mul_comm] using h
    _ ≤ |C| + 1 := by linarith [le_abs_self C]

end FalconerPacking
