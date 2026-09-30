/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.GaussianEnergy

/-!
# Gaussian energy of bounded signed weights

The coordinate measures in the angular derivative estimate are signed. Their Gaussian
energy comparison follows from the positive spatial kernel, with the weight retained
inside both source integrals.
-/

noncomputable section

open MeasureTheory ComplexConjugate
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- The characteristic transform of a real weight with respect to a positive measure. -/
def weightedCharFun (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  ∫ x, (w x : ℂ) * Complex.exp (⟪x, ξ⟫ * Complex.I) ∂μ

/-- Real weights preserve conjugation under frequency reversal. -/
theorem weightedCharFun_neg (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    weightedCharFun μ w (-ξ) = conj (weightedCharFun μ w ξ) := by
  simp [weightedCharFun, ← integral_conj, ← Complex.exp_conj]

/-- Expanding the squared modulus leaves the two real weights inside the difference law. -/
theorem weightedCharFun_norm_sq_eq_integral
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    (‖weightedCharFun μ w ξ‖ ^ 2 : ℝ) =
      ∫ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        (w p.1 * w p.2 : ℝ) * Complex.exp (⟪p.1 - p.2, ξ⟫ * Complex.I) ∂μ.prod μ := by
  have hp (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      ((w p.1 * w p.2 : ℝ) : ℂ) * Complex.exp (⟪p.1 - p.2, ξ⟫ * Complex.I) =
        ((w p.1 : ℂ) * Complex.exp (⟪p.1, ξ⟫ * Complex.I)) *
          ((w p.2 : ℂ) * Complex.exp (⟪p.2, -ξ⟫ * Complex.I)) := by
    have he : Complex.exp (⟪p.1 - p.2, ξ⟫ * Complex.I) =
        Complex.exp (⟪p.1, ξ⟫ * Complex.I) *
          Complex.exp (⟪p.2, -ξ⟫ * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      simp only [inner_sub_left, inner_neg_right, Complex.ofReal_sub, Complex.ofReal_neg]
      ring
    rw [he, Complex.ofReal_mul]
    ring
  simp_rw [hp]
  rw [integral_prod_mul
    (fun x : EuclideanSpace ℝ (Fin 2) ↦
      (w x : ℂ) * Complex.exp (⟪x, ξ⟫ * Complex.I))
    (fun x : EuclideanSpace ℝ (Fin 2) ↦
      (w x : ℂ) * Complex.exp (⟪x, -ξ⟫ * Complex.I))]
  change _ = weightedCharFun μ w ξ * weightedCharFun μ w (-ξ)
  rw [weightedCharFun_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A bounded real weight can be included in the Gaussian duality formula. -/
theorem integral_gaussian_weighted_character {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    {θ : α → EuclideanSpace ℝ (Fin 2)} (hθ : Measurable θ)
    {w : α → ℝ} (hw : Measurable w) {C : ℝ} (hbound : ∀ x, |w x| ≤ C)
    {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2), Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) *
        ∫ x, (w x : ℂ) * Complex.exp (⟪θ x, ξ⟫ * Complex.I) ∂μ =
      (Real.pi / b : ℝ) *
        ∫ x, (w x : ℂ) * Complex.exp (-(‖θ x‖ ^ 2 / (4 * b) : ℝ)) ∂μ := by
  have hg : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) ↦
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2)) volume := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by exact hb : 0 < (b : ℂ).re) 0 (0 : EuclideanSpace ℝ (Fin 2))
  have hint : Integrable
      (fun p : EuclideanSpace ℝ (Fin 2) × α ↦ Complex.exp (-(b : ℂ) * ‖p.1‖ ^ 2) *
        ((w p.2 : ℂ) * Complex.exp (⟪θ p.2, p.1⟫ * Complex.I))) (volume.prod μ) := by
    apply ((hg.norm.const_mul C).comp_fst μ).mono' (by
      apply Measurable.aestronglyMeasurable
      fun_prop)
    exact Filter.Eventually.of_forall fun p ↦ by
      simpa [norm_mul, Real.norm_eq_abs, mul_comm] using
        mul_le_mul_of_nonneg_left (hbound p.2) (norm_nonneg
          (Complex.exp (-(b : ℂ) * ‖p.1‖ ^ 2)))
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hint]
  have hkernel (x : α) :
      ∫ ξ : EuclideanSpace ℝ (Fin 2), Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) *
          ((w x : ℂ) * Complex.exp (⟪θ x, ξ⟫ * Complex.I)) =
        (Real.pi / b : ℝ) * ((w x : ℂ) *
          Complex.exp (-(‖θ x‖ ^ 2 / (4 * b) : ℝ))) := by
    simp_rw [show ∀ z t : ℂ, z * ((w x : ℂ) * t) = (w x : ℂ) * (z * t) by
      intros; ring]
    rw [integral_const_mul, integral_gaussian_mul_character hb]
  simp_rw [hkernel]

/-- The squared weighted Fourier transform has the same positive spatial kernel, with both
real weights retained. -/
theorem integral_gaussian_weightedCharFun_norm_sq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : Measurable w)
    {C : ℝ} (hbound : ∀ x, |w x| ≤ C) {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2 =
      Real.pi / b * ∫ p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        (w p.1 * w p.2) * Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b))) ∂μ.prod μ := by
  have hC : 0 ≤ C := (abs_nonneg (w 0)).trans (hbound 0)
  have hprod (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      |w p.1 * w p.2| ≤ C ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hbound p.1) (hbound p.2) (abs_nonneg _) hC
  have h := integral_gaussian_weighted_character (μ.prod μ)
    (measurable_fst.sub measurable_snd) ((hw.comp measurable_fst).mul
      (hw.comp measurable_snd)) hprod hb
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply] at h
  simp_rw [← weightedCharFun_norm_sq_eq_integral] at h
  have hexp (ξ : EuclideanSpace ℝ (Fin 2)) :
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2) = (Real.exp (-b * ‖ξ‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  simp_rw [hexp] at h
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp h

/-- A bounded signed weight increases Gaussian Fourier energy by at most the square of its
bound. Positivity is used in the spatial kernel, not assumed for the weight. -/
theorem integral_gaussian_weightedCharFun_norm_sq_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : Measurable w)
    {C : ℝ} (hbound : ∀ x, |w x| ≤ C) {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2 ≤
      C ^ 2 * ∫ ξ : EuclideanSpace ℝ (Fin 2),
        Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 := by
  have hC : 0 ≤ C := (abs_nonneg (w 0)).trans (hbound 0)
  let k := fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
    Real.exp (-(‖p.1 - p.2‖ ^ 2 / (4 * b)))
  have hk₀ (p) : 0 ≤ k p := (Real.exp_pos _).le
  have hk₁ (p) : k p ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by positivity))
  have hprod (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
      |w p.1 * w p.2| ≤ C ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (hbound p.1) (hbound p.2) (abs_nonneg _) hC
  have hki : Integrable k (μ.prod μ) := by
    apply (integrable_const (1 : ℝ)).mono' (by dsimp [k]; fun_prop)
    exact Filter.Eventually.of_forall fun p ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hk₀ p)] using hk₁ p
  have hwi : Integrable (fun p ↦ (w p.1 * w p.2) * k p) (μ.prod μ) := by
    apply (hki.const_mul (C ^ 2)).mono' (by dsimp [k]; fun_prop)
    exact Filter.Eventually.of_forall fun p ↦ by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk₀ p)] using
        mul_le_mul_of_nonneg_right (hprod p) (hk₀ p)
  rw [integral_gaussian_weightedCharFun_norm_sq μ hw hbound hb,
    integral_gaussian_charFun_norm_sq μ hb]
  change Real.pi / b * (∫ p, (w p.1 * w p.2) * k p ∂μ.prod μ) ≤
    C ^ 2 * (Real.pi / b * ∫ p, k p ∂μ.prod μ)
  calc
    Real.pi / b * (∫ p, (w p.1 * w p.2) * k p ∂μ.prod μ) ≤
        Real.pi / b * ∫ p, C ^ 2 * k p ∂μ.prod μ := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg Real.pi_pos.le hb.le)
      apply integral_mono hwi (hki.const_mul _)
      intro p
      exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hprod p)) (hk₀ p)
    _ = C ^ 2 * (Real.pi / b * ∫ p, k p ∂μ.prod μ) := by
      rw [integral_const_mul]
      ring

/-- Changing a real weight on a null set leaves its characteristic transform unchanged. -/
theorem weightedCharFun_congr_ae
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {w v : EuclideanSpace ℝ (Fin 2) → ℝ} (h : w =ᵐ[μ] v)
    (ξ : EuclideanSpace ℝ (Fin 2)) : weightedCharFun μ w ξ = weightedCharFun μ v ξ := by
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

/-- The energy comparison requires the weight bound only almost everywhere on the source. -/
theorem integral_gaussian_weightedCharFun_norm_sq_le_ae
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {w : EuclideanSpace ℝ (Fin 2) → ℝ} (hw : Measurable w)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, |w x| ≤ C) {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ w ξ‖ ^ 2 ≤
      C ^ 2 * ∫ ξ : EuclideanSpace ℝ (Fin 2),
        Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 := by
  let v := fun x ↦ max (-C) (min C (w x))
  have hv : Measurable v := measurable_const.max (measurable_const.min hw)
  have hvC (x) : |v x| ≤ C := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hvw : v =ᵐ[μ] w := by
    filter_upwards [hbound] with x hx
    obtain ⟨hl, hu⟩ := abs_le.mp hx
    simp only [v, min_eq_right hu, max_eq_right hl]
  have heq : weightedCharFun μ v = weightedCharFun μ w :=
    funext (weightedCharFun_congr_ae μ hvw)
  rw [← heq]
  exact integral_gaussian_weightedCharFun_norm_sq_le μ hv hvC hb

/-- A unit coordinate on a source of radius `r` has Gaussian energy at most `r²` times the
unweighted energy. This is the signed-coordinate estimate in the angular derivative bound. -/
theorem integral_gaussian_coordinate_energy_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    (v : EuclideanSpace ℝ (Fin 2)) (hv : ‖v‖ ≤ 1) {b : ℝ} (hb : 0 < b) :
    ∫ ξ : EuclideanSpace ℝ (Fin 2),
      Real.exp (-b * ‖ξ‖ ^ 2) * ‖weightedCharFun μ (fun x ↦ ⟪v, x⟫) ξ‖ ^ 2 ≤
      r ^ 2 * ∫ ξ : EuclideanSpace ℝ (Fin 2),
        Real.exp (-b * ‖ξ‖ ^ 2) * ‖charFun μ ξ‖ ^ 2 := by
  apply integral_gaussian_weightedCharFun_norm_sq_le_ae μ (by fun_prop) hr _ hb
  filter_upwards [hsource] with x hx
  calc
    |⟪v, x⟫| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * r := mul_le_mul hv hx (norm_nonneg _) (by norm_num)
    _ = r := one_mul r

end FalconerPacking
