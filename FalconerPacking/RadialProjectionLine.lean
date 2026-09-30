/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjectionRay
import Mathlib.Analysis.Complex.Isometry

/-!
# Full-line integrals as orthogonal projection densities

A rotated Cartesian change of variables gives an explicit density of the orthogonal
projection of a Lebesgue-density source. The identity is pointwise on each line, which
is necessary when that density is later integrated against a singular pin projection.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The line integral in an orthonormal Cartesian frame. -/
def orthogonalLineDensity (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ r : ℝ, f (e (t + r * Complex.I))

@[fun_prop]
theorem measurable_orthogonalLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (orthogonalLineDensity e f) := by
  unfold orthogonalLineDensity
  fun_prop

/-- The first Cartesian coordinate in an isometric frame is its orthogonal projection. -/
theorem re_symm_eq_inner (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 2)) : (e.symm x).re = ⟪x, e 1⟫ := by
  rw [← e.symm.inner_map_map x (e 1), LinearIsometryEquiv.symm_apply_apply]
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply, RCLike.re_eq_complex_re]
  simp

/-- Line integration is constant along the parallel fibers, pointwise at every base point. -/
theorem lineIntegral_eq_orthogonalLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∫⁻ r : ℝ, f (x - r • e Complex.I)) =
      orthogonalLineDensity e f ⟪x, e 1⟫ := by
  let z := e.symm x
  have heq (r : ℝ) : x - r • e Complex.I =
      e ((z.re : ℂ) + ((z.im - r : ℝ) : ℂ) * Complex.I) := by
    apply e.symm.injective
    simp only [map_sub, map_smul, LinearIsometryEquiv.symm_apply_apply]
    change z - r • Complex.I = _
    rw [Complex.real_smul]
    apply Complex.ext <;> simp
  simp_rw [heq]
  rw [lintegral_sub_left_eq_self (fun r : ℝ ↦ f (e (z.re + r * Complex.I))) z.im]
  rw [orthogonalLineDensity, ← re_symm_eq_inner]

/-- Cartesian integration in an orthonormal frame, tested against a nonnegative coordinate function. -/
theorem lintegral_orthogonalLineDensity
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ t : ℝ, g t * orthogonalLineDensity e f t) =
      ∫⁻ x, g ⟪x, e 1⟫ * f x := by
  calc
    (∫⁻ t : ℝ, g t * orthogonalLineDensity e f t) =
        ∫⁻ z : ℝ × ℝ, g z.1 * f (e (z.1 + z.2 * Complex.I)) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro t
      simpa only [orthogonalLineDensity] using
        (lintegral_const_mul (g t) (f := fun r : ℝ ↦ f (e (t + r * Complex.I)))
          (by fun_prop)).symm
    _ = ∫⁻ z : ℂ, g z.re * f (e z) := by
      have h := Complex.volume_preserving_equiv_real_prod.symm.lintegral_comp_emb
        Complex.measurableEquivRealProd.symm.measurableEmbedding
        (fun z : ℂ ↦ g z.re * f (e z))
      simpa [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I] using h
    _ = ∫⁻ x, g ⟪x, e 1⟫ * f x := by
      have h := e.measurePreserving.lintegral_comp_emb e.toHomeomorph.measurableEmbedding
        (fun x ↦ g ⟪x, e 1⟫ * f x)
      simpa only [← re_symm_eq_inner, LinearIsometryEquiv.symm_apply_apply] using h

/-- The explicit line integral is a density of the actual orthogonal pushforward. -/
theorem map_orthogonal_withDensity_eq
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (fun x ↦ ⟪x, e 1⟫) =
      volume.withDensity (orthogonalLineDensity e f) := by
  apply Measure.ext
  intro S hS
  have hproj : Measurable (fun x : EuclideanSpace ℝ (Fin 2) ↦ ⟪x, e 1⟫) := by fun_prop
  rw [Measure.map_apply hproj hS, withDensity_apply _ (hproj hS), withDensity_apply _ hS]
  have h := lintegral_orthogonalLineDensity e hf
    (g := S.indicator 1) (measurable_const.indicator hS)
  rw [← lintegral_indicator hS, ← lintegral_indicator (hproj hS)]
  convert h.symm using 1
  · apply lintegral_congr
    intro y
    by_cases hy : ⟪y, e 1⟫ ∈ S <;> simp [hy]
  · apply lintegral_congr
    intro t
    by_cases ht : t ∈ S <;> simp [ht]

/-- The Cartesian isometric frame whose first vector has angle `θ`. -/
def angularCartesianFrame (θ : ℝ) : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (rotation (Circle.exp θ)).trans Complex.orthonormalBasisOneI.repr

theorem angularCartesianFrame_apply (θ : ℝ) (z : ℂ) :
    angularCartesianFrame θ z =
      Complex.orthonormalBasisOneI.repr (Complex.exp (θ * Complex.I) * z) := rfl

@[simp]
theorem angularCartesianFrame_one (θ : ℝ) :
    angularCartesianFrame θ 1 = angularDirection θ := by
  simp only [angularCartesianFrame_apply, mul_one, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, angularDirection]

@[simp]
theorem angularCartesianFrame_I (θ : ℝ) :
    angularCartesianFrame θ Complex.I = angularDirection (θ + Real.pi / 2) := by
  rw [angularCartesianFrame_apply, Complex.exp_mul_I]
  unfold angularDirection
  congr 1
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext <;> simp [Real.cos_add, Real.sin_add]

/-- The explicit orthogonal projection densities form a jointly measurable angular family. -/
theorem measurable_angularLineDensity {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hf : Measurable f) :
    Measurable (fun z : ℝ × ℝ ↦ orthogonalLineDensity (angularCartesianFrame z.1) f z.2) := by
  unfold orthogonalLineDensity
  simp only [angularCartesianFrame_apply]
  fun_prop

/-- The full-line moment uses the actual orthogonal pushforward of the pin measure. -/
theorem lintegral_lineIntegral_rpow_eq
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) (θ p : ℝ) :
    (∫⁻ x, (∫⁻ r : ℝ, f (x - r • angularDirection θ)) ^ p ∂ν) =
      ∫⁻ t : ℝ, orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t ^ p
        ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫) := by
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  apply lintegral_congr
  intro x
  congr 1
  have h := lineIntegral_eq_orthogonalLineDensity
    (angularCartesianFrame (θ - Real.pi / 2)) f x
  simpa only [angularCartesianFrame_I, angularCartesianFrame_one,
    sub_add_cancel] using h

/-- The full radial-to-orthogonal moment reduction, retaining singular pin measures. -/
theorem lintegral_radialRayDensity_rpow_le_orthogonal
    {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} (hf : Measurable f)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] {R p : ℝ} (hp : 0 ≤ p)
    (hR : ∀ᵐ x ∂ν, ∀ y, f y ≠ 0 → dist x y ≤ R) :
    (∫⁻ x, ∫⁻ θ, radialRayDensity f x θ ^ p ∂radialAngularMeasure ∂ν) ≤
      ENNReal.ofReal R ^ p * ∫⁻ θ,
        ∫⁻ t : ℝ, orthogonalLineDensity (angularCartesianFrame (θ - Real.pi / 2)) f t ^ p
          ∂ν.map (fun x ↦ ⟪x, angularDirection (θ - Real.pi / 2)⟫)
          ∂radialAngularMeasure := by
  simpa only [lintegral_lineIntegral_rpow_eq hf ν] using
    lintegral_radialRayDensity_rpow_le hf ν hp hR

end FalconerPacking
