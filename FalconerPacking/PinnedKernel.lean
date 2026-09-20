/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PositiveLimit
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Pinned distance kernels

This file packages pinned distance measures as a measurable kernel in the pin.  It then uses the
absolute-continuity theorem for composition products to pass absolute continuity of a joint law
to almost-every pinned law.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace FalconerPacking

/-- The Markov kernel that sends a pin `y` to the pushforward of `μ` by `x ↦ dist x y`. -/
def pinnedDistanceKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] :
    Kernel (EuclideanSpace ℝ (Fin 2)) ℝ :=
  (Kernel.id ×ₖ Kernel.const (EuclideanSpace ℝ (Fin 2)) μ).map
    (fun p ↦ dist p.2 p.1)

instance pinnedDistanceKernel.instIsSFiniteKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] :
    IsSFiniteKernel (pinnedDistanceKernel μ) := by
  rw [pinnedDistanceKernel]
  infer_instance

instance pinnedDistanceKernel.instIsFiniteKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] :
    IsFiniteKernel (pinnedDistanceKernel μ) := by
  rw [pinnedDistanceKernel]
  infer_instance

instance pinnedDistanceKernel.instIsMarkovKernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] :
    IsMarkovKernel (pinnedDistanceKernel μ) := by
  rw [pinnedDistanceKernel]
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Evaluating the pinned kernel gives the pinned pushforward measure defined earlier. -/
theorem pinnedDistanceKernel_apply
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    (y : EuclideanSpace ℝ (Fin 2)) :
    pinnedDistanceKernel μ y = pinnedDistanceMeasure μ y := by
  rw [pinnedDistanceKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The joint pin-distance law, with the pin as the first coordinate. -/
def jointPinnedDistanceMeasure
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) :
    Measure (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  (ν.prod μ).map (fun p ↦ (p.1, dist p.2 p.1))

/-- The joint pin-distance law is the composition product of the pin measure and the pinned
distance kernel. -/
theorem compProd_pinnedDistanceKernel
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] [SFinite ν] :
    ν ⊗ₘ pinnedDistanceKernel μ = jointPinnedDistanceMeasure μ ν := by
  ext s hs
  rw [Measure.compProd_apply hs, jointPinnedDistanceMeasure,
    Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply (hs.preimage (by fun_prop))]
  congr with y
  rw [pinnedDistanceKernel_apply, pinnedDistanceMeasure,
    Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop))]
  rfl

/-- If a composition-product law is absolutely continuous with respect to a product with a
finite reference measure, then almost every conditional kernel measure is absolutely continuous
with respect to that reference measure. -/
theorem ae_kernel_absolutelyContinuous_of_compProd
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {ν : Measure α} [SFinite ν] {ξ : Measure β} [IsFiniteMeasure ξ]
    {κ : Kernel α β} [IsFiniteKernel κ]
    (h : ν ⊗ₘ κ ≪ ν.prod ξ) :
    ∀ᵐ a ∂ν, κ a ≪ ξ := by
  rw [← Measure.compProd_const] at h
  exact h.kernel_of_compProd

/-- The same fiberwise conclusion for an s-finite reference measure, obtained by replacing the
reference by its finite equivalent measure. -/
theorem ae_kernel_absolutelyContinuous_of_compProd_sfinite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {ν : Measure α} [SFinite ν] {ξ : Measure β} [SFinite ξ]
    {κ : Kernel α β} [IsFiniteKernel κ]
    (h : ν ⊗ₘ κ ≪ ν.prod ξ) :
    ∀ᵐ a ∂ν, κ a ≪ ξ := by
  have hfinite : ν ⊗ₘ κ ≪ ν.prod ξ.toFinite :=
    h.trans (Measure.AbsolutelyContinuous.rfl.prod
      (absolutelyContinuous_toFinite ξ))
  filter_upwards [ae_kernel_absolutelyContinuous_of_compProd hfinite] with a ha
  exact ha.trans (toFinite_absolutelyContinuous ξ)

/-- Absolute continuity of the joint pin-distance law implies absolute continuity of almost every
pinned distance measure. -/
theorem ae_pinnedDistanceMeasure_absolutelyContinuous_of_joint
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μ]
    {ν : Measure (EuclideanSpace ℝ (Fin 2))} [SFinite ν]
    {ξ : Measure ℝ} [SFinite ξ]
    (h : jointPinnedDistanceMeasure μ ν ≪ ν.prod ξ) :
    ∀ᵐ y ∂ν, pinnedDistanceMeasure μ y ≪ ξ := by
  have hcomp : ν ⊗ₘ pinnedDistanceKernel μ ≪ ν.prod ξ := by
    rwa [compProd_pinnedDistanceKernel]
  filter_upwards [ae_kernel_absolutelyContinuous_of_compProd_sfinite hcomp] with y hy
  rwa [pinnedDistanceKernel_apply] at hy

/-- A joint density with respect to pin measure times Lebesgue measure yields a pin in the
prescribed pin set whose distance set has positive length. -/
theorem exists_mem_volume_pinnedDistances_pos_of_joint_absolutelyContinuous
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {E F : Set (EuclideanSpace ℝ (Fin 2))}
    (hμE : 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) E)
    (hνF : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Fᶜ = 0)
    (hjoint : jointPinnedDistanceMeasure
      (μ : Measure (EuclideanSpace ℝ (Fin 2)))
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) ≪
        (ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume) :
    ∃ y ∈ F, 0 < volume (pinnedDistances E y) := by
  apply exists_mem_volume_pinnedDistances_pos_of_ae ν hμE hνF
  exact ae_pinnedDistanceMeasure_absolutelyContinuous_of_joint hjoint

end FalconerPacking
