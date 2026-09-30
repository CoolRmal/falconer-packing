/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PolarFourierEnergy
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurable radial projections and their canonical densities

The angular projection is defined at every source/pin pair, including the diagonal.
Its pushforwards form an actual finite kernel. Kernel Radon--Nikodym derivatives then
give one jointly measurable candidate density, without separate choices at each pin.
The absolute continuity and averaged moment estimate are distinct analytic obligations.
-/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace FalconerPacking

/-- The angle of the vector from the source point `y` toward the pin `x`. -/
def radialAngle (x y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm (x - y))

@[fun_prop]
theorem measurable_radialAngle :
    Measurable (Function.uncurry radialAngle) := by
  unfold Function.uncurry radialAngle
  fun_prop

theorem radialAngle_mem (x y : EuclideanSpace ℝ (Fin 2)) :
    radialAngle x y ∈ Ioc (-Real.pi) Real.pi :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

/-- Away from the diagonal the angular coordinate gives the usual unit radial vector. -/
theorem angularDirection_radialAngle {x y : EuclideanSpace ℝ (Fin 2)} (hxy : x ≠ y) :
    angularDirection (radialAngle x y) = ‖x - y‖⁻¹ • (x - y) := by
  have h := congrArg Complex.orthonormalBasisOneI.repr
    (Complex.norm_mul_cos_add_sin_mul_I
      (Complex.orthonormalBasisOneI.repr.symm (x - y)))
  have hnorm : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have he : ‖x - y‖ • angularDirection (radialAngle x y) = x - y := by
    simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.real_smul,
      map_smul, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.apply_symm_apply,
      angularDirection, radialAngle] using h
  simpa only [smul_smul, inv_mul_cancel₀ hnorm, one_smul] using
    congrArg (fun v ↦ ‖x - y‖⁻¹ • v) he

/-- Each pin is sent to the angular pushforward of the fixed source measure. -/
def radialProjectionKernel (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] :
    Kernel (EuclideanSpace ℝ (Fin 2)) ℝ where
  toFun x := ν.map (radialAngle x)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.map_apply measurable_radialAngle.of_uncurry_left hS]
    exact measurable_measure_prodMk_left (measurable_radialAngle hS)

@[simp]
theorem radialProjectionKernel_apply (ν : Measure (EuclideanSpace ℝ (Fin 2)))
    [SFinite ν] (x : EuclideanSpace ℝ (Fin 2)) :
    radialProjectionKernel ν x = ν.map (radialAngle x) := rfl

/-- The angular law is carried by the chosen single-turn interval. -/
theorem radialProjectionKernel_compl_interval
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (x : EuclideanSpace ℝ (Fin 2)) :
    radialProjectionKernel ν x (Ioc (-Real.pi) Real.pi)ᶜ = 0 := by
  rw [radialProjectionKernel_apply,
    Measure.map_apply measurable_radialAngle.of_uncurry_left measurableSet_Ioc.compl]
  have h : radialAngle x ⁻¹' (Ioc (-Real.pi) Real.pi)ᶜ = ∅ := by
    ext y
    simp [radialAngle_mem x y]
  rw [h, measure_empty]

/-- Angular and unit-vector pushforwards agree when the source puts no mass at the pin. -/
theorem map_angularDirection_radialProjectionKernel
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (x : EuclideanSpace ℝ (Fin 2)) (hx : ν {x} = 0) :
    (radialProjectionKernel ν x).map angularDirection =
      ν.map (fun y ↦ ‖x - y‖⁻¹ • (x - y)) := by
  rw [radialProjectionKernel_apply,
    Measure.map_map continuous_angularDirection.measurable
      measurable_radialAngle.of_uncurry_left]
  apply Measure.map_congr
  have hae : ∀ᵐ y ∂ν, y ≠ x := by simpa [ae_iff] using hx
  filter_upwards [hae] with y hy
  exact angularDirection_radialAngle (Ne.symm hy)

instance (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν] :
    IsFiniteKernel (radialProjectionKernel ν) := by
  refine ⟨ν univ, measure_lt_top _ _, fun x ↦ ?_⟩
  simp [Measure.map_apply measurable_radialAngle.of_uncurry_left]

instance (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure ν] :
    IsMarkovKernel (radialProjectionKernel ν) where
  isProbabilityMeasure x := Measure.isProbabilityMeasure_map
    (measurable_radialAngle.of_uncurry_left (x := x)).aemeasurable

/-- Lebesgue angular measure on one full turn; normalization is immaterial for finite moments. -/
def radialAngularMeasure : Measure ℝ := volume.restrict (Ioc (-Real.pi) Real.pi)

instance : IsFiniteMeasure radialAngularMeasure := by
  unfold radialAngularMeasure
  infer_instance

/-- A jointly measurable density of the absolutely continuous part of every radial projection. -/
def radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (x : EuclideanSpace ℝ (Fin 2)) (θ : ℝ) : ℝ≥0∞ :=
  Kernel.rnDeriv (radialProjectionKernel ν)
    (Kernel.const (EuclideanSpace ℝ (Fin 2)) radialAngularMeasure) x θ

@[fun_prop]
theorem measurable_radialProjectionDensity (ν : Measure (EuclideanSpace ℝ (Fin 2)))
    [SFinite ν] :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      radialProjectionDensity ν p.1 p.2) :=
  Kernel.measurable_rnDeriv _ _

/-- The canonical angular density always defines a submeasure of the radial pushforward. -/
theorem withDensity_radialProjectionDensity_le
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (x : EuclideanSpace ℝ (Fin 2)) :
    radialAngularMeasure.withDensity (radialProjectionDensity ν x) ≤
      ν.map (radialAngle x) := by
  have h := Kernel.withDensity_rnDeriv_le (radialProjectionKernel ν)
    (Kernel.const (EuclideanSpace ℝ (Fin 2)) radialAngularMeasure) x
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)] at h
  exact h

/-- Once absolute continuity is established, the same jointly measurable density represents it. -/
theorem withDensity_radialProjectionDensity_eq
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
    (x : EuclideanSpace ℝ (Fin 2))
    (h : ν.map (radialAngle x) ≪ radialAngularMeasure) :
    radialAngularMeasure.withDensity (radialProjectionDensity ν x) =
      ν.map (radialAngle x) := by
  have he := Kernel.withDensity_rnDeriv_eq
    (κ := radialProjectionKernel ν)
    (η := Kernel.const (EuclideanSpace ℝ (Fin 2)) radialAngularMeasure) h
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)] at he
  exact he

/-- The averaged angular moment is a genuine measurable integral. -/
theorem measurable_radialProjectionMoment
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν] (q : ℝ) :
    Measurable (fun x ↦ ∫⁻ θ, radialProjectionDensity ν x θ ^ q
      ∂radialAngularMeasure) := by
  exact Measurable.lintegral_prod_right (f := fun x θ ↦ radialProjectionDensity ν x θ ^ q)
    ((measurable_radialProjectionDensity ν).pow_const q)

end FalconerPacking
