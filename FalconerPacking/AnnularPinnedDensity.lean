/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicAnnularSummability
public import FalconerPacking.AnnularPinnedReconstruction
public import FalconerPacking.CircleFourierConvolution

/-!
# Absolute continuity from actual decaying annular good/bad pieces

The shell split here reconstructs the already constructed compact annular source pieces exactly.
The source expansion's convergence is proved in `AnnularPinnedReconstruction`, rather than
postulated as an additional analytic hypothesis. The remaining explicit assumptions are the
actual good squared second-norm and bad first-norm bounds, with finite norms for early shells.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- Actual annular good/bad bounds with a negative dyadic exponent prove absolute continuity of
 the joint distance law and of the distance law at almost every prescribed pin. -/
theorem pinnedDistance_absolutelyContinuous_of_dyadic_annular_bounds
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχone : ∀ᵐ x ∂μ, χ x = 1) (hχnorm : ∀ x, ‖χ x‖ ≤ 1)
    {T : ℕ} (hT : 0 < T) {L : ℝ}
    (hL : ∀ᵐ y ∂ν, ∀ x ∈ Function.support χ, dist x y ≤ L)
    (good bad : ℕ → EuclideanSpace ℝ (Fin 2) × ℝ → ℂ)
    (hgm : ∀ n, Measurable (good n)) (hbm : ∀ n, Measurable (bad n))
    (hsplit : ∀ n, ∀ᵐ p ∂ν.prod volume,
      good n p + bad n p = complexDistanceDensity
        (compactAnnularSource μ hμ χ hχ T n) p.1 p.2)
    (n₀ : ℕ) (hearlyg : ∀ n < n₀, MemLp (good n) 2 (ν.prod volume))
    (hearlyb : ∀ n < n₀, Integrable (bad n) (ν.prod volume))
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hgood : ∀ n, n₀ ≤ n →
      (∫⁻ p, ENNReal.ofReal (‖good n p‖ ^ 2) ∂ν.prod volume) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ))))
    (hbad : ∀ n, n₀ ≤ n →
      (∫⁻ p, ENNReal.ofReal ‖bad n p‖ ∂ν.prod volume) ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ)))) :
    jointPinnedDistanceMeasure μ ν ≪ ν.prod volume ∧
      ∀ᵐ y ∂ν, pinnedDistanceMeasure μ y ≪ volume := by
  obtain ⟨hg, hb, hgs, hbs⟩ := annular_norms_summable_of_dyadic_bounds (ν.prod volume)
    good bad hgm hbm n₀ hearlyg hearlyb hC hε hgood hbad
  haveI : IsFiniteMeasure (jointPinnedDistanceMeasure μ ν) := by
    unfold jointPinnedDistanceMeasure
    infer_instance
  have hac : jointPinnedDistanceMeasure μ ν ≪ ν.prod volume := by
    refine absolutelyContinuous_of_annular_tests_finite_region (ν.prod volume)
      (jointPinnedDistanceMeasure μ ν) (S := univ ×ˢ Icc (0 : ℝ) L) ?_
      good bad hg hb hgs hbs ?_ ?_
    · rw [Measure.prod_prod, measure_univ, one_mul]
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
    · intro n
      filter_upwards [hsplit n,
        (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := volume)).ae hL]
        with p hp hLp
      intro houtside
      rw [hp]
      by_cases ht : 0 < p.2
      · apply complexDistanceDensity_eq_zero_of_lt
        · intro x hx
          exact hLp x (support_compactAnnularSource_subset μ hμ χ hχ T n hx)
        · have hn : ¬ p.2 ≤ L := by
            intro hle
            exact houtside ⟨mem_univ _, ht.le, hle⟩
          exact lt_of_not_ge hn
      · simp only [complexDistanceDensity, ht, ↓reduceIte]
    · intro φ
      let ψ := BoundedContinuousFunction.comp Complex.ofReal Complex.isometry_ofReal.lipschitz φ
      have hlim := tendsto_joint_compactAnnularSource_distanceDensity μ ν hμ χ hχ
        hχone hχnorm hT ψ
      have htarget : (∫ p, ψ p ∂jointPinnedDistanceMeasure μ ν) =
          ((∫ p, φ p ∂jointPinnedDistanceMeasure μ ν : ℝ) : ℂ) := by
        exact integral_complex_ofReal
      rw [htarget] at hlim
      apply hlim.congr'
      filter_upwards with N
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hsplit] with p hp
      congr 1
      exact Finset.sum_congr rfl (fun n _ ↦ (hp n).symm)
  exact ⟨hac, ae_pinnedDistanceMeasure_absolutelyContinuous_of_joint hac⟩

end FalconerPacking
