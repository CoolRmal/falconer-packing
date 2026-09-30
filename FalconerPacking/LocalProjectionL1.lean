/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.UniformProjectionEnergy
import FalconerPacking.CorrelatedAngularCharts
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Local integrated comparison of projection densities

Support of the source implies support of its actual Radon--Nikodym projection density.
Cauchy--Schwarz on the resulting finite interval changes the uniform squared comparison
into an integrated `L¹` estimate.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- An actual nonnegative density vanishes almost everywhere outside a set carrying its law. -/
theorem density_zero_ae_outside (μ : Measure ℝ) {f : ℝ → ℝ} {S : Set ℝ}
    (hf : Measurable f) (hf₀ : ∀ x, 0 ≤ f x) (hS : MeasurableSet S)
    (hd : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hsupport : ∀ᵐ x ∂μ, x ∈ S) :
    ∀ᵐ x ∂volume, x ∉ S → f x = 0 := by
  have hz : μ Sᶜ = 0 := by simpa only [ae_iff, mem_compl_iff] using! hsupport
  have hi : ∫⁻ x in Sᶜ, ENNReal.ofReal (f x) = 0 := by
    rw [← withDensity_apply _ hS.compl, ← hd]
    exact hz
  have ha := (lintegral_eq_zero_iff hf.ennreal_ofReal).mp hi
  have hb := (ae_restrict_iff' hS.compl).mp ha
  filter_upwards [hb] with x hx
  intro hxs
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp (hx hxs)) (hf₀ x)

/-- The actual chosen projection density inherits the radius of the source support. -/
theorem orthogonalProjectionDensity_zero_ae_outside
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {r θ : ℝ}
    (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    (hθ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection θ)) 2 volume) :
    ∀ᵐ t ∂volume, t ∉ Icc (-r) r → orthogonalProjectionDensity μ θ t = 0 := by
  have hθ' : MemLp (charFun (orthogonalProjectionKernel μ θ)) 2 volume := by
    change MemLp (fun τ ↦ charFun (orthogonalProjectionKernel μ θ) τ) 2 volume
    simpa only [orthogonalProjectionKernel_apply, charFun_orthogonalProjection] using hθ
  have hd := (kernelDensity_L2_of_memLp_charFun (orthogonalProjectionKernel μ) hθ').2.2.1
  apply density_zero_ae_outside (orthogonalProjectionKernel μ θ)
    ((measurable_orthogonalProjectionDensity μ).comp
      (measurable_const.prodMk measurable_id))
    (orthogonalProjectionDensity_nonneg μ θ) measurableSet_Icc hd
  rw [orthogonalProjectionKernel_apply]
  apply (ae_map_iff (by fun_prop) measurableSet_Icc).mpr
  filter_upwards [hsource] with x hx
  exact abs_le.mp ((abs_real_inner_le_norm x (angularDirection θ)).trans
    (by simpa only [norm_angularDirection, mul_one] using hx))

/-- With shifts at most r² and r≤1, both densities are supported in the interval [-2r,2r]. -/
theorem orthogonalProjectionDensity_sub_zero_ae_outside
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) (hr₁ : r ≤ 1) (θ φ v : ℝ)
    (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r) (hv : |v| ≤ r ^ 2)
    (hθ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection θ)) 2 volume)
    (hφ : MemLp (fun τ : ℝ ↦ charFun μ (τ • angularDirection φ)) 2 volume) :
    ∀ᵐ t ∂volume, t ∉ Icc (-2 * r) (2 * r) →
      orthogonalProjectionDensity μ φ (t - v) - orthogonalProjectionDensity μ θ t = 0 := by
  have hφs := orthogonalProjectionDensity_zero_ae_outside μ hsource hφ
  have hshift := (measurePreserving_add_right volume (-v)).quasiMeasurePreserving.ae hφs
  filter_upwards [orthogonalProjectionDensity_zero_ae_outside μ hsource hθ, hshift]
    with t ht ht'
  intro houtside
  have hv' : |v| ≤ r := by nlinarith
  have htr : t ∉ Icc (-r) r := by
    intro hin
    exact houtside ⟨by linarith [hin.1], by linarith [hin.2]⟩
  have htv : t - v ∉ Icc (-r) r := by
    intro hin
    have hvt := abs_le.mp hv'
    exact houtside ⟨by linarith [hin.1, hvt.1], by linarith [hin.2, hvt.2]⟩
  rw [ht htr, show orthogonalProjectionDensity μ φ (t - v) = 0 from
    ht' (by simpa only [sub_eq_add_neg] using htv), sub_self]

/-- Cauchy--Schwarz for a nonnegative function supported almost everywhere on a measurable set. -/
theorem lintegral_le_sqrt_energy_mul_sqrt_mass
    {X : Type*} [MeasurableSpace X] (ν : Measure X) {f : X → ℝ≥0∞} {S : Set X}
    (hf : Measurable f) (hS : MeasurableSet S)
    (hsupport : ∀ᵐ x ∂ν, x ∉ S → f x = 0) :
    ∫⁻ x, f x ∂ν ≤ (∫⁻ x, f x ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (ν S) ^ (1 / 2 : ℝ) := by
  have heq : f =ᵐ[ν] f * S.indicator (fun _ ↦ 1) := by
    filter_upwards [hsupport] with x hx
    by_cases hxs : x ∈ S
    · simp only [Pi.mul_apply, indicator_of_mem hxs, mul_one]
    · simp only [Pi.mul_apply, indicator_of_notMem hxs, mul_zero, hx hxs]
  rw [lintegral_congr_ae heq]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (g := S.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    hf.aemeasurable (measurable_const.indicator hS).aemeasurable
  have hpow (x : X) : S.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ^ 2 =
      S.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ S <;> simp [hx]
  simpa only [ENNReal.rpow_two, hpow, lintegral_indicator hS,
    lintegral_one, Measure.restrict_apply_univ] using h

/-- Circular rather than literal angle closeness preserves the uniform density coefficient. -/
theorem uniform_circular_projectionDensity_energy_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 < r) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [SFinite κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hv : Measurable v) (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ,
      (Real.pi / 2) * ‖angularDirection (φ z) - angularDirection (θ z)‖ ≤ r)
    (hvbound : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    (∫⁻ z, ∫⁻ t : ℝ, ENNReal.ofReal ((orthogonalProjectionDensity μ (φ z) (t - v z) -
      orthogonalProjectionDensity μ (θ z) t) ^ 2) ∂volume ∂κ) ≤
        A * ENNReal.ofReal (3 * uniformProjectionCoefficient s * max C 1 *
          r ^ (2 * s - 2)) := by
  have hbound := circular_correlated_shifted_charFun_energy_bound_of_chart μ
    (uniform_correlated_shifted_charFun_energy_bound μ hs hs₂ hfr r hr hsource)
    κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound
  rw [lintegral_correlated_projectionDensity_sub_sq μ hs hs₂ hfr κ θ φ v A hθ hφ
    hθdom hφdom hrange]
  refine (mul_le_mul' le_rfl hbound).trans_eq ?_
  have hconst : ENNReal.ofReal
      (3 * uniformProjectionCoefficient s * max C 1 * r ^ (2 * s - 2)) =
      ENNReal.ofReal (2 * Real.pi)⁻¹ * ENNReal.ofReal
        (3 * ((160 * uniformFourierBandCoefficient s * dyadicBandSumConstant s) * max C 1) *
          r ^ (2 * s - 2)) := by
    calc
      _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          (3 * ((160 * uniformFourierBandCoefficient s * dyadicBandSumConstant s) * max C 1) *
            r ^ (2 * s - 2))) := by
        congr 1
        unfold uniformProjectionCoefficient
        ring
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
          ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [hconst]
  ac_rfl

/-- Cauchy--Schwarz yields a local integrated L¹ comparison for the actual densities. -/
theorem lintegral_local_projectionDensity_sub_abs_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [IsFiniteMeasure κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hv : Measurable v) (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ,
      (Real.pi / 2) * ‖angularDirection (φ z) - angularDirection (θ z)‖ ≤ r)
    (hvbound : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    (∫⁻ z, ∫⁻ t : ℝ, ENNReal.ofReal |orthogonalProjectionDensity μ (φ z) (t - v z) -
      orthogonalProjectionDensity μ (θ z) t| ∂volume ∂κ) ≤
        (A * ENNReal.ofReal (3 * uniformProjectionCoefficient s * max C 1 *
          r ^ (2 * s - 2))) ^ (1 / 2 : ℝ) *
            (κ univ * ENNReal.ofReal (4 * r)) ^ (1 / 2 : ℝ) := by
  let D (p : α × ℝ) := orthogonalProjectionDensity μ (φ p.1) (p.2 - v p.1) -
    orthogonalProjectionDensity μ (θ p.1) p.2
  let f (p : α × ℝ) := ENNReal.ofReal |D p|
  let S : Set (α × ℝ) := univ ×ˢ Icc (-2 * r) (2 * r)
  have hD : Measurable D := measurable_correlated_projectionDensity_sub μ hθ hφ hv
  have hf : Measurable f := by
    simpa only [Real.norm_eq_abs] using hD.norm.ennreal_ofReal
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Icc
  have hsupport : ∀ᵐ p ∂κ.prod volume, p ∉ S → f p = 0 := by
    have hm : MeasurableSet {p | p ∉ S → f p = 0} := by
      have he : {p | p ∉ S → f p = 0} = S ∪ {p | f p = 0} := by
        ext p
        simp only [mem_union, mem_setOf_eq]
        tauto
      rw [he]
      exact hS.union (measurableSet_eq_fun hf measurable_const)
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [ae_memLp_charFun_composed_angle μ hs hs₂ hfr κ θ A hθ hθdom
      (hrange.mono fun _ h ↦ h.1),
      ae_memLp_charFun_composed_angle μ hs hs₂ hfr κ φ A hφ hφdom
        (hrange.mono fun _ h ↦ h.2), hvbound] with z hz hz' hvz
    filter_upwards [orthogonalProjectionDensity_sub_zero_ae_outside μ hr.le hr₁
      (θ z) (φ z) (v z) hsource hvz hz hz'] with t ht
    intro houtside
    have ht' : t ∉ Icc (-2 * r) (2 * r) := by
      simpa only [S, mem_prod, mem_univ, true_and] using houtside
    dsimp only [f, D]
    rw [ht ht', abs_zero, ENNReal.ofReal_zero]
  have h := lintegral_le_sqrt_energy_mul_sqrt_mass (κ.prod volume) hf hS hsupport
  have hsq (p : α × ℝ) : f p ^ 2 = ENNReal.ofReal (D p ^ 2) := by
    dsimp only [f]
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp_rw [hsq] at h
  rw [lintegral_prod _ hf.aemeasurable,
    lintegral_prod _ (hD.pow_const 2).ennreal_ofReal.aemeasurable,
    show (κ.prod volume) S = κ univ * ENNReal.ofReal (4 * r) by
      dsimp only [S]
      rw [Measure.prod_prod, Real.volume_Icc]
      congr 2
      ring] at h
  have henergy := uniform_circular_projectionDensity_energy_bound μ hs hs₂ hfr r hr hsource
    κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound
  exact h.trans (mul_le_mul' (ENNReal.rpow_le_rpow henergy (by norm_num)) le_rfl)

/-- The two square-root factors have the required curvature-scale exponent. -/
theorem local_projection_sqrt_algebra {K C r s : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hr : 0 < r) (A M : ℝ≥0∞) :
    (A * ENNReal.ofReal (3 * K * C * r ^ (2 * s - 2))) ^ (1 / 2 : ℝ) *
        (M * ENNReal.ofReal (4 * r)) ^ (1 / 2 : ℝ) =
      (ENNReal.ofReal (12 * K) * A * ENNReal.ofReal C * M) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (r ^ (s - 1 / 2)) := by
  have he : (3 * K * C * r ^ (2 * s - 2)) * (4 * r) =
      (12 * K * C) * r ^ (2 * s - 1) := by
    rw [show 2 * s - 1 = (2 * s - 2) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
    ring
  have he' : (A * ENNReal.ofReal (3 * K * C * r ^ (2 * s - 2))) *
      (M * ENNReal.ofReal (4 * r)) =
      (ENNReal.ofReal (12 * K) * A * ENNReal.ofReal C * M) *
        ENNReal.ofReal (r ^ (2 * s - 1)) := by
    calc
      _ = A * M * (ENNReal.ofReal (3 * K * C * r ^ (2 * s - 2)) *
          ENNReal.ofReal (4 * r)) := by ring
      _ = A * M * ENNReal.ofReal ((12 * K * C) * r ^ (2 * s - 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity), he]
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 12 * K * C),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 12 * K)]
        ring
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), he',
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _), ← Real.rpow_mul hr.le]
  congr 2
  ring

/-- The local L¹ estimate has exponent s−1/2 and square-root dependence on pin mass. -/
theorem local_projectionDensity_L1_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (r : ℝ) (hr : 0 < r) (hr₁ : r ≤ 1) (hsource : ∀ᵐ x ∂μ, ‖x‖ ≤ r)
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [IsFiniteMeasure κ]
    (θ φ v : α → ℝ) (A : ℝ≥0∞) (hθ : Measurable θ) (hφ : Measurable φ)
    (hv : Measurable v) (hθdom : κ.map θ ≤ A • (volume : Measure ℝ))
    (hφdom : κ.map φ ≤ A • (volume : Measure ℝ))
    (hrange : ∀ᵐ z ∂κ, θ z ∈ Icc (-Real.pi) Real.pi ∧ φ z ∈ Icc (-Real.pi) Real.pi)
    (hclose : ∀ᵐ z ∂κ,
      (Real.pi / 2) * ‖angularDirection (φ z) - angularDirection (θ z)‖ ≤ r)
    (hvbound : ∀ᵐ z ∂κ, |v z| ≤ r ^ 2) :
    (∫⁻ z, ∫⁻ t : ℝ, ENNReal.ofReal |orthogonalProjectionDensity μ (φ z) (t - v z) -
      orthogonalProjectionDensity μ (θ z) t| ∂volume ∂κ) ≤
        (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * A *
          ENNReal.ofReal (max C 1) * κ univ) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (r ^ (s - 1 / 2)) := by
  have h := lintegral_local_projectionDensity_sub_abs_le μ hs hs₂ hfr r hr hr₁ hsource
    κ θ φ v A hθ hφ hv hθdom hφdom hrange hclose hvbound
  rwa [local_projection_sqrt_algebra (uniformProjectionCoefficient_pos hs hs₂).le
    (by positivity) hr] at h

end FalconerPacking
