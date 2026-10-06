/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.LocalProjectionL1
public import FalconerPacking.AffineProjectionGeometry

/-!
# Integrated comparison of actual affine distance laws

The Radon--Nikodym density at each center is chosen independently of any comparison
center. The geometric projection identities identify these canonical densities almost
everywhere. Lebesgue translation invariance then removes their common distance offset.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The affine distance law, as a measurable kernel in the pin. -/
def affineDistanceKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    (b : EuclideanSpace ℝ (Fin 2)) : Kernel (EuclideanSpace ℝ (Fin 2)) ℝ :=
  (Kernel.id ×ₖ Kernel.const (EuclideanSpace ℝ (Fin 2)) μ).map
    (fun p ↦ affineDistance b p.2 p.1)

instance affineDistanceKernel.instIsFiniteKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (b : EuclideanSpace ℝ (Fin 2)) : IsFiniteKernel (affineDistanceKernel μ b) := by
  rw [affineDistanceKernel]
  infer_instance

instance affineDistanceKernel.instIsMarkovKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (b : EuclideanSpace ℝ (Fin 2)) : IsMarkovKernel (affineDistanceKernel μ b) := by
  rw [affineDistanceKernel]
  exact Kernel.IsMarkovKernel.map _ (by unfold affineDistance; fun_prop)

/-- Each kernel fiber is the original affine pushforward of the source measure. -/
theorem affineDistanceKernel_apply
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    (b y : EuclideanSpace ℝ (Fin 2)) :
    affineDistanceKernel μ b y = μ.map (fun x ↦ affineDistance b x y) := by
  rw [affineDistanceKernel, Kernel.map_apply _ (by unfold affineDistance; fun_prop),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by unfold affineDistance; fun_prop) (by fun_prop)]
  rfl

/-- A canonical jointly measurable density of the affine law at the specified center. -/
def affineDistanceDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    (b y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : ℝ :=
  kernelDensity (affineDistanceKernel μ b) volume y t

@[fun_prop]
theorem measurable_affineDistanceDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    (b : EuclideanSpace ℝ (Fin 2)) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      affineDistanceDensity μ b p.1 p.2) := measurable_kernelDensity _ _

/-- The chosen densities are nonnegative, also on exceptional fibers. -/
theorem affineDistanceDensity_nonneg
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    (b y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) : 0 ≤ affineDistanceDensity μ b y t :=
  ENNReal.toReal_nonneg

/-- At a Fourier-regular direction, the affine law has its stated translated projection
density, for any source translation center. -/
theorem map_affineDistance_eq_withDensity_projection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (b : EuclideanSpace ℝ (Fin 2)) {c y : EuclideanSpace ℝ (Fin 2)} (hcy : c ≠ y)
    (hchar : MemLp (fun τ : ℝ ↦ charFun (μ.map (fun x ↦ x - b))
      (τ • angularDirection (radialAngle c y))) 2 volume) :
    μ.map (fun x ↦ affineDistance c x y) = volume.withDensity (fun t ↦ ENNReal.ofReal
      (orthogonalProjectionDensity (μ.map (fun x ↦ x - b)) (radialAngle c y)
        ((t - dist b y) - affineProjectionShift b c y))) := by
  let ν := μ.map (fun x ↦ x - b)
  have hchar' : MemLp (charFun (orthogonalProjectionKernel ν (radialAngle c y)))
      2 volume := by
    change MemLp (fun τ ↦ charFun (orthogonalProjectionKernel ν (radialAngle c y)) τ)
      2 volume
    simpa only [orthogonalProjectionKernel_apply, charFun_orthogonalProjection] using hchar
  have hd := (kernelDensity_L2_of_memLp_charFun (orthogonalProjectionKernel ν)
    hchar').2.2.1
  have hm : Measurable (orthogonalProjectionDensity ν (radialAngle c y)) :=
    (measurable_orthogonalProjectionDensity ν).comp
      (measurable_const.prodMk measurable_id)
  rw [map_affineDistance_eq_shifted_projection_translate μ hcy]
  have he : (fun t : ℝ ↦ (t + affineProjectionShift b c y) + dist b y) =
      (fun t ↦ t + (affineProjectionShift b c y + dist b y)) := by ext t; ring
  rw [he, map_add_const_eq_withDensity _ hm hd]
  congr 1
  ext t
  congr 2
  ring

/-- The canonical affine density agrees with the projection formula for every regular fiber. -/
theorem affineDistanceDensity_ae_eq_projection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (b : EuclideanSpace ℝ (Fin 2)) {c y : EuclideanSpace ℝ (Fin 2)} (hcy : c ≠ y)
    (hchar : MemLp (fun τ : ℝ ↦ charFun (μ.map (fun x ↦ x - b))
      (τ • angularDirection (radialAngle c y))) 2 volume) :
    affineDistanceDensity μ c y =ᵐ[volume] fun t ↦
      orthogonalProjectionDensity (μ.map (fun x ↦ x - b)) (radialAngle c y)
        ((t - dist b y) - affineProjectionShift b c y) := by
  apply kernelDensity_ae_eq_of_density
  · exact ((measurable_orthogonalProjectionDensity (μ.map (fun x ↦ x - b))).comp
      (measurable_const.prodMk (by fun_prop))).aemeasurable
  · exact fun _ ↦ orthogonalProjectionDensity_nonneg _ _ _
  · rw [affineDistanceKernel_apply]
    exact map_affineDistance_eq_withDensity_projection μ b hcy hchar

/-- These are densities of the full affine laws, not merely of their absolutely continuous parts. -/
theorem map_affineDistance_eq_withDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (b : EuclideanSpace ℝ (Fin 2)) {c y : EuclideanSpace ℝ (Fin 2)} (hcy : c ≠ y)
    (hchar : MemLp (fun τ : ℝ ↦ charFun (μ.map (fun x ↦ x - b))
      (τ • angularDirection (radialAngle c y))) 2 volume) :
    μ.map (fun x ↦ affineDistance c x y) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (affineDistanceDensity μ c y t)) := by
  have hd := map_affineDistance_eq_withDensity_projection μ b hcy hchar
  rw [hd]
  apply withDensity_congr_ae
  exact (affineDistanceDensity_ae_eq_projection μ b hcy hchar).symm.fun_comp ENNReal.ofReal

/-- The common offset disappears from the L¹ difference of the actual densities. -/
theorem lintegral_affineDistanceDensity_sub_abs_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {b c y : EuclideanSpace ℝ (Fin 2)} (hby : b ≠ y) (hcy : c ≠ y)
    (hb : MemLp (fun τ : ℝ ↦ charFun (μ.map (fun x ↦ x - b))
      (τ • angularDirection (radialAngle b y))) 2 volume)
    (hc : MemLp (fun τ : ℝ ↦ charFun (μ.map (fun x ↦ x - b))
      (τ • angularDirection (radialAngle c y))) 2 volume) :
    (∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
      affineDistanceDensity μ b y t|) =
      ∫⁻ t : ℝ, ENNReal.ofReal
        |orthogonalProjectionDensity (μ.map (fun x ↦ x - b)) (radialAngle c y)
          (t - affineProjectionShift b c y) -
          orthogonalProjectionDensity (μ.map (fun x ↦ x - b)) (radialAngle b y) t| := by
  have hshift : affineProjectionShift b b y = 0 := by
    rw [affineProjectionShift, affineDistance_self hby, sub_self]
  have heq := lintegral_congr_ae (Filter.EventuallyEq.fun_comp
    ((affineDistanceDensity_ae_eq_projection μ b hcy hc).sub
      (affineDistanceDensity_ae_eq_projection μ b hby hb)) (fun x ↦ ENNReal.ofReal |x|))
  simp only [Function.comp_apply, Pi.sub_apply] at heq
  rw [heq]
  simp_rw [hshift, sub_zero]
  simpa only [sub_eq_add_neg] using lintegral_add_right_eq_self (μ := volume)
    (fun t : ℝ ↦ ENNReal.ofReal
      |orthogonalProjectionDensity (μ.map (fun x ↦ x - b)) (radialAngle c y)
        (t - affineProjectionShift b c y) -
        orthogonalProjectionDensity (μ.map (fun x ↦ x - b)) (radialAngle b y) t|)
    (-dist b y)

/-- A dominated radial-angle law gives the full affine pushforward density for almost every pin. -/
theorem ae_map_affineDistance_eq_withDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (κ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite κ]
    (b c : EuclideanSpace ℝ (Fin 2)) (A : ℝ≥0∞)
    (hdom : κ.map (radialAngle c) ≤ A • (volume : Measure ℝ))
    (hsep : ∀ᵐ y ∂κ, c ≠ y) :
    ∀ᵐ y ∂κ, μ.map (fun x ↦ affineDistance c x y) =
      volume.withDensity (fun t ↦ ENNReal.ofReal (affineDistanceDensity μ c y t)) := by
  letI : IsProbabilityMeasure (μ.map (fun x ↦ x - b)) :=
    inferInstance
  have hchar := ae_memLp_charFun_composed_angle (μ.map (fun x ↦ x - b)) hs hs₂
    (hfr.map_sub_const b) κ (radialAngle c) A (by fun_prop) hdom
    (ae_of_all _ fun y ↦ ⟨(radialAngle_mem c y).1.le, (radialAngle_mem c y).2⟩)
  filter_upwards [hchar, hsep] with y hy hy'
  exact map_affineDistance_eq_withDensity μ b hy' hy

/-- Actual nearby affine distance laws obey the uniform local L¹ estimate. -/
theorem affineDistanceDensity_L1_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C δ r : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (κ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure κ]
    (b c : EuclideanSpace ℝ (Fin 2)) (A : ℝ≥0∞)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hrδ : r ≤ δ / 16)
    (hbc : dist b c ≤ r) (hsource : ∀ᵐ x ∂μ, dist x b ≤ r)
    (hsep : ∀ᵐ y ∂κ, δ ≤ dist b y)
    (hbdom : κ.map (radialAngle b) ≤ A • (volume : Measure ℝ))
    (hcdom : κ.map (radialAngle c) ≤ A • (volume : Measure ℝ)) :
    (∫⁻ y, ∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
      affineDistanceDensity μ b y t| ∂volume ∂κ) ≤
      (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A *
        ENNReal.ofReal (max C 1) * κ univ) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((affineComparisonRadius δ r) ^ (s - 1 / 2)) := by
  obtain ⟨hR, hR₁, hprob, hfr', hsource', hgeom⟩ :=
    affineProjection_comparison_inputs hδ hδ₁ hr hrδ hbc hfr hsource hsep
  letI := hprob
  have hrange := hgeom.mono fun _ h ↦ h.1
  have hclose := hgeom.mono fun _ h ↦ h.2.1
  have hshift := hgeom.mono fun _ h ↦ h.2.2.1
  have hbound := local_projectionDensity_L1_bound (μ.map (fun x ↦ x - b)) hs hs₂ hfr'
    (affineComparisonRadius δ r) hR hR₁ hsource' κ (radialAngle b) (radialAngle c)
    (affineProjectionShift b c) A (by fun_prop) (by fun_prop)
    (measurable_affineProjectionShift b c) hbdom hcdom hrange hclose hshift
  have hb := ae_memLp_charFun_composed_angle (μ.map (fun x ↦ x - b)) hs hs₂ hfr'
    κ (radialAngle b) A (by fun_prop) hbdom (hrange.mono fun _ h ↦ h.1)
  have hc := ae_memLp_charFun_composed_angle (μ.map (fun x ↦ x - b)) hs hs₂ hfr'
    κ (radialAngle c) A (by fun_prop) hcdom (hrange.mono fun _ h ↦ h.2)
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hbound
  filter_upwards [hb, hc, hsep] with y hby hcy hy
  have hby' : b ≠ y := dist_pos.mp (hδ.trans_le hy)
  have hcsep := half_separation_le_dist_center hy hbc (by linarith)
  have hcy' : c ≠ y := dist_pos.mp (lt_of_lt_of_le (by linarith : 0 < δ / 2) hcsep)
  exact lintegral_affineDistanceDensity_sub_abs_eq μ hby' hcy' hby hcy

/-- The separation factor is fixed, while the source radius has exponent `s - 1/2`. -/
theorem affineDistanceDensity_L1_scale_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C δ r : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (κ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure κ]
    (b c : EuclideanSpace ℝ (Fin 2)) (A : ℝ≥0∞)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hrδ : r ≤ δ / 16)
    (hbc : dist b c ≤ r) (hsource : ∀ᵐ x ∂μ, dist x b ≤ r)
    (hsep : ∀ᵐ y ∂κ, δ ≤ dist b y)
    (hbdom : κ.map (radialAngle b) ≤ A • (volume : Measure ℝ))
    (hcdom : κ.map (radialAngle c) ≤ A • (volume : Measure ℝ)) :
    (∫⁻ y, ∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
      affineDistanceDensity μ b y t| ∂volume ∂κ) ≤
      (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A *
        ENNReal.ofReal (max C 1) * κ univ) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((1 + 8 / δ) ^ (s - 1 / 2)) *
            ENNReal.ofReal (r ^ (s - 1 / 2)) := by
  have h := affineDistanceDensity_L1_bound μ hs hs₂ hfr κ b c A hδ hδ₁ hr hrδ
    hbc hsource hsep hbdom hcdom
  have he : ENNReal.ofReal ((affineComparisonRadius δ r) ^ (s - 1 / 2)) =
      ENNReal.ofReal ((1 + 8 / δ) ^ (s - 1 / 2)) *
        ENNReal.ofReal (r ^ (s - 1 / 2)) := by
    rw [affineComparisonRadius, Real.mul_rpow (by positivity) hr.le]
    exact ENNReal.ofReal_mul (by positivity)
  rwa [he, ← mul_assoc] at h

/-- Multiplying a conditional comparison by its mass leaves the square root of that mass. -/
theorem affine_mass_sqrt_algebra {C m : ℝ} (hC : 0 ≤ C) (hm : 0 < m)
    (K A M : ℝ≥0∞) :
    ENNReal.ofReal m * (K * A * ENNReal.ofReal (C / m) * M) ^ (1 / 2 : ℝ) =
      (K * A * ENNReal.ofReal C * M) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal m ^ (1 / 2 : ℝ) := by
  have hmroot : (ENNReal.ofReal m ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal m := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have he : ENNReal.ofReal m ^ 2 * ENNReal.ofReal (C / m) =
      ENNReal.ofReal C * ENNReal.ofReal m := by
    rw [← ENNReal.ofReal_pow hm.le, ← ENNReal.ofReal_mul (sq_nonneg m),
      ← ENNReal.ofReal_mul hC]
    congr 1
    field_simp
  calc
    _ = (ENNReal.ofReal m ^ 2 * (K * A * ENNReal.ofReal (C / m) * M)) ^
        (1 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal m ^ 2)
        (K * A * ENNReal.ofReal (C / m) * M) (by norm_num), hmroot]
    _ = ((K * A * ENNReal.ofReal C * M) * ENNReal.ofReal m) ^ (1 / 2 : ℝ) := by
      congr 1
      calc
        _ = K * A * M * (ENNReal.ofReal m ^ 2 * ENNReal.ofReal (C / m)) := by ring
        _ = _ := by rw [he]; ring
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

/-- The weighted conditional law has the required square-root mass gain, uniformly over
all probability measures satisfying the normalized Frostman estimate. -/
theorem affineDistanceDensity_weighted_L1_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C δ r m : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hC : 1 ≤ C) (hm : 0 < m) (hm₁ : m ≤ 1)
    (hfr : IsFrostman μ s (C / m))
    (κ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure κ]
    (b c : EuclideanSpace ℝ (Fin 2)) (A : ℝ≥0∞)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hrδ : r ≤ δ / 16)
    (hbc : dist b c ≤ r) (hsource : ∀ᵐ x ∂μ, dist x b ≤ r)
    (hsep : ∀ᵐ y ∂κ, δ ≤ dist b y)
    (hbdom : κ.map (radialAngle b) ≤ A • (volume : Measure ℝ))
    (hcdom : κ.map (radialAngle c) ≤ A • (volume : Measure ℝ)) :
    ENNReal.ofReal m *
      (∫⁻ y, ∫⁻ t : ℝ, ENNReal.ofReal |affineDistanceDensity μ c y t -
        affineDistanceDensity μ b y t| ∂volume ∂κ) ≤
      (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A *
        ENNReal.ofReal C * κ univ) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal m ^ (1 / 2 : ℝ) *
            ENNReal.ofReal ((1 + 8 / δ) ^ (s - 1 / 2)) *
              ENNReal.ofReal (r ^ (s - 1 / 2)) := by
  have hCm : 1 ≤ C / m := (le_div_iff₀ hm).mpr (by linarith)
  have h := affineDistanceDensity_L1_scale_bound μ hs hs₂ hfr κ b c A hδ hδ₁ hr hrδ
    hbc hsource hsep hbdom hcdom
  rw [max_eq_left hCm] at h
  have hw := mul_le_mul_right h (ENNReal.ofReal m)
  simpa only [← mul_assoc, affine_mass_sqrt_algebra (by linarith : 0 ≤ C) hm] using hw

end FalconerPacking
