/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AffineDistanceL1
import FalconerPacking.OccupiedCubes
import Mathlib.MeasureTheory.Function.Floor

/-!
# Finite dyadic affine density mixtures

The affine approximations are actual pushforward laws. Their jointly measurable densities
are finite mixtures of the canonical conditional affine densities, with the original cube
masses as weights. The mixture estimates also apply after a common refinement.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

instance normalizedRestrict.instIsFiniteMeasure
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (Q : Set (EuclideanSpace ℝ (Fin 2))) :
    IsFiniteMeasure (normalizedRestrict μ Q) := by
  constructor
  change ((μ Q)⁻¹ • μ.restrict Q) univ < ∞
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact (ENNReal.inv_mul_le_one (μ Q)).trans_lt (by simp)

/-- Multiplying a normalized restriction by its original mass recovers the restriction. -/
theorem measure_smul_normalizedRestrict
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (Q : Set (EuclideanSpace ℝ (Fin 2))) :
    μ Q • normalizedRestrict μ Q = μ.restrict Q := by
  by_cases hQ : μ Q = 0
  · simp [hQ, Measure.restrict_eq_zero.2 hQ]
  · rw [normalizedRestrict, smul_smul, ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q),
      one_smul]

/-- The joint affine law retains the pin as its first coordinate. -/
def jointAffineDistanceMeasure
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) (b : EuclideanSpace ℝ (Fin 2)) :
    Measure (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  (ν.prod μ).map (fun p ↦ (p.1, affineDistance b p.2 p.1))

/-- The affine kernel and direct pushforward give the same joint law. -/
theorem compProd_affineDistanceKernel
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [SFinite ν]
    (b : EuclideanSpace ℝ (Fin 2)) :
    ν ⊗ₘ affineDistanceKernel μ b = jointAffineDistanceMeasure μ ν b := by
  ext s hs
  rw [Measure.compProd_apply hs, jointAffineDistanceMeasure,
    Measure.map_apply (by unfold affineDistance; fun_prop) hs,
    Measure.prod_apply (hs.preimage (by unfold affineDistance; fun_prop))]
  congr with y
  rw [affineDistanceKernel_apply,
    Measure.map_apply (by unfold affineDistance; fun_prop)
      (hs.preimage (by fun_prop))]
  rfl

/-- Absolute continuity of the selected radial law suffices; no bounded radial density is needed. -/
theorem ae_affineDistanceKernel_absolutelyContinuous_of_radial_ac
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite ν]
    (b : EuclideanSpace ℝ (Fin 2))
    (hrad : ν.map (radialAngle b) ≪ (volume : Measure ℝ))
    (hsep : ∀ᵐ y ∂ν, b ≠ y) :
    ∀ᵐ y ∂ν, affineDistanceKernel μ b y ≪ (volume : Measure ℝ) := by
  have hdom : ν.map (radialAngle b) ≤ ∞ • (volume : Measure ℝ) := by
    apply Measure.le_iff.2
    intro A hA
    rw [Measure.smul_apply, smul_eq_mul]
    by_cases hz : volume A = 0
    · simp [hz, hrad hz]
    · simp [ENNReal.top_mul hz]
  filter_upwards [ae_map_affineDistance_eq_withDensity μ hs hs₂ hfr ν b b ∞ hdom hsep]
    with y hy
  rw [affineDistanceKernel_apply, hy]
  exact withDensity_absolutelyContinuous _ _

/-- A finite nonnegative density mixture represents the corresponding weighted measure sum. -/
theorem finset_smul_withDensity_eq
    {α ι : Type*} [MeasurableSpace α] (ξ : Measure α) (S : Finset ι)
    (w : ι → ℝ≥0∞) (f : ι → α → ℝ) (hw : ∀ i ∈ S, w i ≠ ∞)
    (hf : ∀ i ∈ S, Measurable (f i)) (hf₀ : ∀ i ∈ S, ∀ x, 0 ≤ f i x) :
    (∑ i ∈ S, w i • ξ.withDensity (fun x ↦ ENNReal.ofReal (f i x))) =
      ξ.withDensity (fun x ↦ ENNReal.ofReal (∑ i ∈ S, (w i).toReal * f i x)) := by
  ext A hA
  rw [Measure.finsetSum_apply, withDensity_apply _ hA]
  have he (x : α) : ENNReal.ofReal (∑ i ∈ S, (w i).toReal * f i x) =
      ∑ i ∈ S, w i * ENNReal.ofReal (f i x) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ mul_nonneg ENNReal.toReal_nonneg
      (hf₀ i hi x))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hw i hi)]
  simp_rw [he]
  rw [lintegral_finsetSum S (f := fun i x ↦ w i * ENNReal.ofReal (f i x))
    (fun i hi ↦ (measurable_const : Measurable (fun _ : α ↦ w i)).mul
      (hf i hi).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hA,
    lintegral_const_mul _ (hf i hi).ennreal_ofReal]

/-- Weighted finite mixtures satisfy the exact positive-integral triangle estimate. -/
theorem lintegral_abs_finset_weighted_sub_le
    {α ι : Type*} [MeasurableSpace α] (ξ : Measure α) (S : Finset ι)
    (w : ι → ℝ) (f g : ι → α → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hf : ∀ i ∈ S, Measurable (f i)) (hg : ∀ i ∈ S, Measurable (g i)) :
    (∫⁻ x, ENNReal.ofReal |(∑ i ∈ S, w i * f i x) - ∑ i ∈ S, w i * g i x| ∂ξ) ≤
      ∑ i ∈ S, ENNReal.ofReal (w i) *
        ∫⁻ x, ENNReal.ofReal |f i x - g i x| ∂ξ := by
  calc
    _ ≤ ∫⁻ x, ∑ i ∈ S, ENNReal.ofReal (w i) *
        ENNReal.ofReal |f i x - g i x| ∂ξ := by
      apply lintegral_mono
      intro x
      have h := Finset.abs_sum_le_sum_abs (fun i ↦ w i * (f i x - g i x)) S
      simp only [mul_sub, Finset.sum_sub_distrib] at h
      apply (ENNReal.ofReal_le_ofReal h).trans_eq
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ abs_nonneg _)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi), ENNReal.ofReal_mul (hw i hi)]
    _ = _ := by
      rw [lintegral_finsetSum S
        (f := fun i x ↦ ENNReal.ofReal (w i) * ENNReal.ofReal |f i x - g i x|) (by
          intro i hi
          have := hf i hi
          have := hg i hi
          fun_prop)]
      apply Finset.sum_congr rfl
      intro i hi
      apply lintegral_const_mul
      have := hf i hi
      have := hg i hi
      fun_prop

@[fun_prop]
theorem measurable_cubeIndex (n : ℕ) : Measurable (cubeIndex n) := by
  unfold cubeIndex
  fun_prop

/-- The actual dyadic affine map, with a fixed center for each cube. -/
def dyadicAffineMap (n : ℕ) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) × ℝ :=
  (p.1, affineDistance (b (cubeIndex n p.2)) p.2 p.1)

@[fun_prop]
theorem measurable_dyadicAffineMap (n : ℕ)
    (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) : Measurable (dyadicAffineMap n b) := by
  have hb : Measurable b := measurable_of_countable b
  unfold dyadicAffineMap affineDistance
  fun_prop

/-- The finite density mixture at one dyadic level. Null cubes contribute zero. -/
def dyadicAffineDensity (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (S : Finset (Fin 2 → ℤ)) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (p : EuclideanSpace ℝ (Fin 2) × ℝ) : ℝ :=
  ∑ k ∈ S, (μ (dyadicCube n k)).toReal *
    affineDistanceDensity (normalizedRestrict μ (dyadicCube n k)) (b k) p.1 p.2

@[fun_prop]
theorem measurable_dyadicAffineDensity (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (S : Finset (Fin 2 → ℤ)) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) :
    Measurable (dyadicAffineDensity μ n S b) := by
  unfold dyadicAffineDensity
  fun_prop

theorem dyadicAffineDensity_nonneg (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ)
    (S : Finset (Fin 2 → ℤ)) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (p : EuclideanSpace ℝ (Fin 2) × ℝ) : 0 ≤ dyadicAffineDensity μ n S b p :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (affineDistanceDensity_nonneg _ _ _ _)

/-- A finite occupied cover splits the source into its actual cube restrictions. -/
theorem measure_eq_sum_dyadic_restrict
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (S : Finset (Fin 2 → ℤ))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ k ∈ S, dyadicCube n k) :
    μ = ∑ k ∈ S, μ.restrict (dyadicCube n k) := by
  calc
    μ = μ.restrict (⋃ k ∈ S, dyadicCube n k) :=
      (Measure.restrict_eq_self_of_ae_mem hcover).symm
    _ = _ := by
      rw [Measure.restrict_biUnion_finset
        (fun _ _ _ _ h ↦ dyadicCube_disjoint h) (measurableSet_dyadicCube n),
        Measure.sum_fintype]
      exact Finset.sum_coe_sort S (fun k ↦ μ.restrict (dyadicCube n k))

/-- Splitting the source into cubes is compatible with the actual dyadic affine map. -/
theorem map_dyadicAffineMap_eq_sum
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [SFinite ν]
    (n : ℕ) (S : Finset (Fin 2 → ℤ)) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ k ∈ S, dyadicCube n k) :
    (ν.prod μ).map (dyadicAffineMap n b) =
      ∑ k ∈ S, μ (dyadicCube n k) •
        jointAffineDistanceMeasure (normalizedRestrict μ (dyadicCube n k)) ν (b k) := by
  have hprod : ν.prod μ = ∑ k ∈ S, ν.prod (μ.restrict (dyadicCube n k)) := by
    conv_lhs => rw [measure_eq_sum_dyadic_restrict μ n S hcover]
    rw [← Measure.sum_coe_finset, Measure.prod_sum_right, Measure.sum_fintype]
    exact Finset.sum_coe_sort S (fun k ↦ ν.prod (μ.restrict (dyadicCube n k)))
  rw [hprod, Measure.map_finset_sum (measurable_dyadicAffineMap n b).aemeasurable]
  apply Finset.sum_congr rfl
  intro k hk
  have hmap : (ν.prod (μ.restrict (dyadicCube n k))).map (dyadicAffineMap n b) =
      jointAffineDistanceMeasure (μ.restrict (dyadicCube n k)) ν (b k) := by
    apply Measure.map_congr
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := ν) (ν := μ.restrict (dyadicCube n k))).ae
        (ae_restrict_mem (measurableSet_dyadicCube n k))] with p hp
    simp only [dyadicAffineMap, mem_dyadicCube_iff.1 hp]
  rw [hmap, jointAffineDistanceMeasure, jointAffineDistanceMeasure,
    ← Measure.map_smul, ← Measure.prod_smul_right, measure_smul_normalizedRestrict]

/-- The finite dyadic approximation has the stated jointly measurable density. -/
theorem map_dyadicAffineMap_eq_withDensity
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [SFinite ν]
    {s C : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (n : ℕ) (S : Finset (Fin 2 → ℤ)) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ k ∈ S, dyadicCube n k)
    (hrad : ∀ k ∈ S, μ (dyadicCube n k) ≠ 0 →
      ν.map (radialAngle (b k)) ≪ (volume : Measure ℝ))
    (hsep : ∀ k ∈ S, μ (dyadicCube n k) ≠ 0 → ∀ᵐ y ∂ν, b k ≠ y) :
    (ν.prod μ).map (dyadicAffineMap n b) =
      (ν.prod volume).withDensity (fun p ↦ ENNReal.ofReal (dyadicAffineDensity μ n S b p)) := by
  rw [map_dyadicAffineMap_eq_sum μ ν n S b hcover]
  calc
    _ = ∑ k ∈ S, μ (dyadicCube n k) • (ν.prod volume).withDensity
        (fun p ↦ ENNReal.ofReal
          (affineDistanceDensity (normalizedRestrict μ (dyadicCube n k)) (b k) p.1 p.2)) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hmass : μ (dyadicCube n k) = 0
      · simp [hmass]
      haveI := isProbabilityMeasure_normalizedRestrict (measurableSet_dyadicCube n k)
        hmass (measure_ne_top μ _)
      congr 1
      rw [← compProd_affineDistanceKernel]
      exact compProd_eq_withDensity_kernelDensity _ ν volume
        (ae_affineDistanceKernel_absolutelyContinuous_of_radial_ac _ hs hs₂
          (isFrostman_normalizedRestrict hfr hmass (measure_ne_top μ _)) ν (b k)
          (hrad k hk hmass) (hsep k hk hmass))
    _ = _ := finset_smul_withDensity_eq (ν.prod volume) S _ _
      (fun _ _ ↦ measure_ne_top μ _) (fun _ _ ↦ measurable_affineDistanceDensity _ _)
      (fun _ _ _ ↦ affineDistanceDensity_nonneg _ _ _ _)

/-- Nonnegative measurable real densities of the same law agree almost everywhere. -/
theorem ae_eq_of_withDensity_ofReal_eq
    {α : Type*} [MeasurableSpace α] (ξ : Measure α) [SigmaFinite ξ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x)
    (he : ξ.withDensity (fun x ↦ ENNReal.ofReal (f x)) =
      ξ.withDensity (fun x ↦ ENNReal.ofReal (g x))) : f =ᵐ[ξ] g := by
  have hae := (withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal.aemeasurable
    hg.ennreal_ofReal.aemeasurable).1 he
  filter_upwards [hae] with x hx
  simpa only [ENNReal.toReal_ofReal (hf₀ x), ENNReal.toReal_ofReal (hg₀ x)] using
    congrArg ENNReal.toReal hx

/-- Repeating a parent's center at its children leaves the pointwise affine map unchanged. -/
theorem dyadicAffineMap_succ_parent (n : ℕ)
    (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2)) :
    dyadicAffineMap (n + 1) (fun k ↦ b (fun i ↦ k i / 2)) = dyadicAffineMap n b := by
  funext p
  simp only [dyadicAffineMap]
  rw [cubeIndex_succ n p.2]

/-- The full finer partition gives a common-refinement representative of any parent density. -/
theorem dyadicAffineDensity_parent_ae_eq
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s C : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (n : ℕ) (S : Finset (Fin 2 → ℤ)) (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ} (hf : Measurable f) (hf₀ : ∀ p, 0 ≤ f p)
    (hfd : (ν.prod μ).map (dyadicAffineMap n b) =
      (ν.prod volume).withDensity (fun p ↦ ENNReal.ofReal (f p)))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ k ∈ S, dyadicCube (n + 1) k)
    (hrad : ∀ k ∈ S, μ (dyadicCube (n + 1) k) ≠ 0 →
      ν.map (radialAngle (b (fun i ↦ k i / 2))) ≪ (volume : Measure ℝ))
    (hsep : ∀ k ∈ S, μ (dyadicCube (n + 1) k) ≠ 0 →
      ∀ᵐ y ∂ν, b (fun i ↦ k i / 2) ≠ y) :
    f =ᵐ[ν.prod volume]
      dyadicAffineDensity μ (n + 1) S (fun k ↦ b (fun i ↦ k i / 2)) := by
  apply ae_eq_of_withDensity_ofReal_eq (ν.prod volume) hf
    (measurable_dyadicAffineDensity _ _ _ _) hf₀ (dyadicAffineDensity_nonneg _ _ _ _)
  rw [← hfd, ← dyadicAffineMap_succ_parent]
  exact map_dyadicAffineMap_eq_withDensity μ ν hs hs₂ hfr (n + 1) S _
    hcover hrad hsep

/-- Comparing adjacent levels reduces exactly to the finer conditional comparisons. -/
theorem dyadicAffineDensity_succ_sub_L1_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s C : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C)
    (n : ℕ) (S : Finset (Fin 2 → ℤ))
    (b c : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    {f : EuclideanSpace ℝ (Fin 2) × ℝ → ℝ} (hf : Measurable f) (hf₀ : ∀ p, 0 ≤ f p)
    (hfd : (ν.prod μ).map (dyadicAffineMap n b) =
      (ν.prod volume).withDensity (fun p ↦ ENNReal.ofReal (f p)))
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ k ∈ S, dyadicCube (n + 1) k)
    (hrad : ∀ k ∈ S, μ (dyadicCube (n + 1) k) ≠ 0 →
      ν.map (radialAngle (b (fun i ↦ k i / 2))) ≪ (volume : Measure ℝ))
    (hsep : ∀ k ∈ S, μ (dyadicCube (n + 1) k) ≠ 0 →
      ∀ᵐ y ∂ν, b (fun i ↦ k i / 2) ≠ y) :
    (∫⁻ p, ENNReal.ofReal |dyadicAffineDensity μ (n + 1) S c p - f p| ∂ν.prod volume) ≤
      ∑ k ∈ S, μ (dyadicCube (n + 1) k) * ∫⁻ y, ∫⁻ t : ℝ,
        ENNReal.ofReal |affineDistanceDensity
          (normalizedRestrict μ (dyadicCube (n + 1) k)) (c k) y t -
        affineDistanceDensity (normalizedRestrict μ (dyadicCube (n + 1) k))
          (b (fun i ↦ k i / 2)) y t| ∂volume ∂ν := by
  have he := dyadicAffineDensity_parent_ae_eq μ ν hs hs₂ hfr n S b hf hf₀ hfd
    hcover hrad hsep
  have hint := lintegral_congr_ae (he.mono fun p hp ↦ congrArg
    (fun v ↦ ENNReal.ofReal |dyadicAffineDensity μ (n + 1) S c p - v|) hp)
  rw [hint]
  apply (lintegral_abs_finset_weighted_sub_le (ν.prod volume) S
    (fun k ↦ (μ (dyadicCube (n + 1) k)).toReal) _ _
    (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun _ _ ↦ measurable_affineDistanceDensity _ _)
    (fun _ _ ↦ measurable_affineDistanceDensity _ _)).trans_eq
  apply Finset.sum_congr rfl
  intro k hk
  rw [ENNReal.ofReal_toReal (measure_ne_top μ _), lintegral_prod _ (by fun_prop)]

/-- A probability affine law has an integrable density with total mass one. -/
theorem integrable_dyadicAffineDensity_of_density
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (n : ℕ) (S : Finset (Fin 2 → ℤ))
    (b : (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (hd : (ν.prod μ).map (dyadicAffineMap n b) =
      (ν.prod volume).withDensity (fun p ↦ ENNReal.ofReal (dyadicAffineDensity μ n S b p))) :
    Integrable (dyadicAffineDensity μ n S b) (ν.prod volume) ∧
      (∫⁻ p, ENNReal.ofReal (dyadicAffineDensity μ n S b p) ∂ν.prod volume) = 1 ∧
      (∫ p, dyadicAffineDensity μ n S b p ∂ν.prod volume) = 1 := by
  haveI := Measure.isProbabilityMeasure_map (μ := ν.prod μ)
    (measurable_dyadicAffineMap n b).aemeasurable
  have hmass := congrArg (fun m : Measure (EuclideanSpace ℝ (Fin 2) × ℝ) ↦ m univ) hd
  have hlin :
      (∫⁻ p, ENNReal.ofReal (dyadicAffineDensity μ n S b p) ∂ν.prod volume) = 1 := by
    simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using hmass.symm
  have hm : AEStronglyMeasurable (dyadicAffineDensity μ n S b) (ν.prod volume) :=
    (measurable_dyadicAffineDensity μ n S b).aestronglyMeasurable
  refine ⟨⟨hm, ?_⟩, hlin, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal (dyadicAffineDensity_nonneg μ n S b _), hlin]
    exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ (dyadicAffineDensity_nonneg μ n S b)) hm, hlin, ENNReal.toReal_one]

end FalconerPacking
