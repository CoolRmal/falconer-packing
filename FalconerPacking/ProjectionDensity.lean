/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ProjectionFourier
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Jointly measurable orthogonal projection densities

An equivalent finite reference measure permits the kernel Radon--Nikodym theorem to produce
a jointly measurable density against a sigma-finite reference measure. Applying this construction
to orthogonal projections gives a common measurable choice of their almost-everywhere L² densities.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

namespace FalconerPacking

section KernelDensity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace.CountableOrCountablyGenerated α β]

/-- A joint extended density, obtained through a finite measure equivalent to the reference. -/
def kernelDensityENN (κ : Kernel α β) (ξ : Measure β) [SigmaFinite ξ] (a : α) (x : β) :
    ℝ≥0∞ :=
  ξ.toFinite.rnDeriv ξ x * κ.rnDeriv (Kernel.const α ξ.toFinite) a x

/-- A nonnegative real representative of the joint kernel density. -/
def kernelDensity (κ : Kernel α β) (ξ : Measure β) [SigmaFinite ξ] (a : α) (x : β) : ℝ :=
  (kernelDensityENN κ ξ a x).toReal

@[fun_prop]
theorem measurable_kernelDensityENN (κ : Kernel α β) (ξ : Measure β) [SigmaFinite ξ] :
    Measurable (fun p : α × β ↦ kernelDensityENN κ ξ p.1 p.2) := by
  exact ((Measure.measurable_rnDeriv ξ.toFinite ξ).comp measurable_snd).mul
    (Kernel.measurable_rnDeriv κ (Kernel.const α ξ.toFinite))

@[fun_prop]
theorem measurable_kernelDensity (κ : Kernel α β) (ξ : Measure β) [SigmaFinite ξ] :
    Measurable (fun p : α × β ↦ kernelDensity κ ξ p.1 p.2) :=
  (measurable_kernelDensityENN κ ξ).ennreal_toReal

/-- On an absolutely continuous fiber the joint extended density represents the original law. -/
theorem withDensity_kernelDensityENN (κ : Kernel α β) [IsFiniteKernel κ]
    (ξ : Measure β) [SigmaFinite ξ] {a : α} (ha : κ a ≪ ξ) :
    ξ.withDensity (kernelDensityENN κ ξ a) = κ a := by
  have h := Kernel.withDensity_rnDeriv_eq
    (η := Kernel.const α ξ.toFinite) (ha.trans (absolutelyContinuous_toFinite ξ))
  rw [Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv κ _), Kernel.const_apply] at h
  change ξ.withDensity
    ((ξ.toFinite.rnDeriv ξ) * (κ.rnDeriv (Kernel.const α ξ.toFinite) a)) = κ a
  rw [withDensity_mul ξ (Measure.measurable_rnDeriv _ _)
    (Kernel.measurable_rnDeriv_right _ _ _),
    Measure.withDensity_rnDeriv_eq _ _ (toFinite_absolutelyContinuous ξ)]
  exact h

/-- The jointly chosen density agrees almost everywhere with the fiberwise RN derivative. -/
theorem kernelDensityENN_ae_eq_rnDeriv (κ : Kernel α β) [IsFiniteKernel κ]
    (ξ : Measure β) [SigmaFinite ξ] {a : α} (ha : κ a ≪ ξ) :
    kernelDensityENN κ ξ a =ᵐ[ξ] (κ a).rnDeriv ξ := by
  have h := Measure.rnDeriv_withDensity ξ (f := kernelDensityENN κ ξ a)
    ((measurable_kernelDensityENN κ ξ).comp (measurable_const.prodMk measurable_id))
  rw [withDensity_kernelDensityENN κ ξ ha] at h
  exact h.symm

/-- Passing to real values preserves the almost-everywhere identification. -/
theorem kernelDensity_ae_eq_rnDeriv (κ : Kernel α β) [IsFiniteKernel κ]
    (ξ : Measure β) [SigmaFinite ξ] {a : α} (ha : κ a ≪ ξ) :
    kernelDensity κ ξ a =ᵐ[ξ] fun x ↦ ((κ a).rnDeriv ξ x).toReal :=
  (kernelDensityENN_ae_eq_rnDeriv κ ξ ha).fun_comp ENNReal.toReal

/-- The real-valued joint representative still recovers every absolutely continuous fiber. -/
theorem withDensity_kernelDensity (κ : Kernel α β) [IsFiniteKernel κ]
    (ξ : Measure β) [SigmaFinite ξ] {a : α} (ha : κ a ≪ ξ) :
    ξ.withDensity (fun x ↦ ENNReal.ofReal (kernelDensity κ ξ a x)) = κ a := by
  rw [← Measure.withDensity_rnDeriv_eq (κ a) ξ ha]
  apply withDensity_congr_ae
  filter_upwards [kernelDensity_ae_eq_rnDeriv κ ξ ha, Measure.rnDeriv_lt_top (κ a) ξ]
    with x hx hfin
  rw [hx, ENNReal.ofReal_toReal hfin.ne]

/-- Any existing nonnegative density agrees with the jointly chosen representative. -/
theorem kernelDensity_ae_eq_of_density (κ : Kernel α β) [IsFiniteKernel κ]
    (ξ : Measure β) [SigmaFinite ξ] {a : α} {f : β → ℝ}
    (hf : AEMeasurable f ξ) (hf₀ : ∀ x, 0 ≤ f x)
    (hd : κ a = ξ.withDensity (fun x ↦ ENNReal.ofReal (f x))) :
    kernelDensity κ ξ a =ᵐ[ξ] f := by
  have ha : κ a ≪ ξ := hd ▸ withDensity_absolutelyContinuous ξ _
  have h := Measure.rnDeriv_withDensity₀ ξ hf.ennreal_ofReal
  rw [← hd] at h
  filter_upwards [kernelDensity_ae_eq_rnDeriv κ ξ ha, h] with x hx hx'
  rw [hx, hx', ENNReal.toReal_ofReal (hf₀ x)]

/-- Almost-everywhere absolutely continuous fibers give the expected jointly measurable
density of the composition-product law. -/
theorem compProd_eq_withDensity_kernelDensity (κ : Kernel α β) [IsFiniteKernel κ]
    (ν : Measure α) [SFinite ν] (ξ : Measure β) [SigmaFinite ξ]
    (ha : ∀ᵐ a ∂ν, κ a ≪ ξ) :
    ν ⊗ₘ κ = (ν.prod ξ).withDensity
      (fun p : α × β ↦ ENNReal.ofReal (kernelDensity κ ξ p.1 p.2)) := by
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [Measure.lintegral_compProd hf,
    lintegral_withDensity_eq_lintegral_mul₀
      (measurable_kernelDensity κ ξ).ennreal_ofReal.aemeasurable hf.aemeasurable,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ha] with a ha
  rw [← withDensity_kernelDensity κ ξ ha,
    lintegral_withDensity_eq_lintegral_mul₀ (by fun_prop) (by fun_prop)]
  rfl

end KernelDensity

/-- Square-integrable fiber characteristic functions give the same norm identity for the
jointly measurable density, rather than only for a separately chosen density. -/
theorem kernelDensity_L2_of_memLp_charFun {α : Type*} [MeasurableSpace α]
    (κ : Kernel α ℝ) [IsFiniteKernel κ] {a : α}
    (ha : MemLp (charFun (κ a)) 2 volume) :
    Integrable (kernelDensity κ volume a) volume ∧
      MemLp (kernelDensity κ volume a) 2 volume ∧
      κ a = volume.withDensity (fun x ↦ ENNReal.ofReal (kernelDensity κ volume a x)) ∧
      ∫ x, kernelDensity κ volume a x ^ 2 =
        (2 * Real.pi)⁻¹ * ∫ ξ, ‖charFun (κ a) ξ‖ ^ 2 := by
  obtain ⟨f, hf₀, hfi, hf₂, hfd, hfn⟩ := exists_L2_density_of_memLp_charFun_sq (κ a) ha
  have heq := kernelDensity_ae_eq_of_density κ volume hfi.aemeasurable hf₀ hfd
  refine ⟨hfi.congr heq.symm, (memLp_congr_ae heq).mpr hf₂,
    (withDensity_kernelDensity κ volume
      (absolutelyContinuous_of_memLp_charFun (κ a) ha)).symm, ?_⟩
  rw [← hfn]
  exact integral_congr_ae (heq.fun_comp (fun x : ℝ ↦ x ^ 2))

/-- Orthogonal projection as a measurable kernel in the direction angle. -/
def orthogonalProjectionKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] : Kernel ℝ ℝ :=
  (Kernel.id ×ₖ Kernel.const ℝ μ).map
    (fun p : ℝ × EuclideanSpace ℝ (Fin 2) ↦ ⟪p.2, angularDirection p.1⟫)

instance orthogonalProjectionKernel.instIsFiniteKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] :
    IsFiniteKernel (orthogonalProjectionKernel μ) := by
  rw [orthogonalProjectionKernel]
  infer_instance

instance orthogonalProjectionKernel.instIsMarkovKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] :
    IsMarkovKernel (orthogonalProjectionKernel μ) := by
  rw [orthogonalProjectionKernel]
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Each fiber of the projection kernel is the usual orthogonal pushforward. -/
theorem orthogonalProjectionKernel_apply
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] (θ : ℝ) :
    orthogonalProjectionKernel μ θ = μ.map (fun x ↦ ⟪x, angularDirection θ⟫) := by
  rw [orthogonalProjectionKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A single jointly measurable choice of all projection densities. -/
def orthogonalProjectionDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] (θ t : ℝ) : ℝ :=
  kernelDensity (orthogonalProjectionKernel μ) volume θ t

@[fun_prop]
theorem measurable_orthogonalProjectionDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] :
    Measurable (fun p : ℝ × ℝ ↦ orthogonalProjectionDensity μ p.1 p.2) :=
  measurable_kernelDensity _ _

/-- Projection densities are nonnegative at every point, including exceptional fibers. -/
theorem orthogonalProjectionDensity_nonneg
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] (θ t : ℝ) :
    0 ≤ orthogonalProjectionDensity μ θ t :=
  ENNReal.toReal_nonneg

/-- Frostman probabilities above exponent one have a jointly measurable family of actual
nonnegative L² projection densities, with the exact characteristic-function norm formula. -/
theorem ae_orthogonalProjectionDensity_L2
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      Integrable (orthogonalProjectionDensity μ θ) volume ∧
      MemLp (orthogonalProjectionDensity μ θ) 2 volume ∧
      μ.map (fun x ↦ ⟪x, angularDirection θ⟫) =
        volume.withDensity (fun t ↦ ENNReal.ofReal (orthogonalProjectionDensity μ θ t)) ∧
      ∫ t, orthogonalProjectionDensity μ θ t ^ 2 =
        (2 * Real.pi)⁻¹ * ∫ r : ℝ, ‖charFun μ (r • angularDirection θ)‖ ^ 2 := by
  filter_upwards [ae_memLp_charFun_orthogonalProjection μ hs hs₂ hfr] with θ hθ
  have hκ : MemLp (charFun (orthogonalProjectionKernel μ θ)) 2 volume := by
    rwa [orthogonalProjectionKernel_apply]
  unfold orthogonalProjectionDensity
  simpa only [orthogonalProjectionKernel_apply,
    charFun_orthogonalProjection] using kernelDensity_L2_of_memLp_charFun _ hκ

/-- The angle-projection joint law has the jointly chosen density. -/
theorem compProd_orthogonalProjectionKernel_eq_withDensity
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    volume.restrict (Ioo (-Real.pi) Real.pi) ⊗ₘ orthogonalProjectionKernel μ =
      ((volume.restrict (Ioo (-Real.pi) Real.pi)).prod volume).withDensity
        (fun p : ℝ × ℝ ↦ ENNReal.ofReal (orthogonalProjectionDensity μ p.1 p.2)) := by
  apply compProd_eq_withDensity_kernelDensity
  filter_upwards [ae_memLp_charFun_orthogonalProjection μ hs hs₂ hfr] with θ hθ
  rw [orthogonalProjectionKernel_apply]
  exact absolutelyContinuous_of_memLp_charFun _ hθ

end FalconerPacking
