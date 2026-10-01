/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.CoherentStepSummability
import FalconerPacking.DyadicPositiveCubes
import FalconerPacking.DyadicAffineDensity
import FalconerPacking.RadialMomentCenters

/-!
# The actual summed dyadic affine comparison

The normalized child probabilities retain the original Frostman constant divided by their
mass. The whole-pin comparison is summed using the fixed radial moments at both centers.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- The scale-independent coefficient in the summed affine comparison. -/
def coherentAffineCoefficient (s C δ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (12 * uniformProjectionCoefficient s) * ENNReal.ofReal C) ^
    (1 / 2 : ℝ) * ENNReal.ofReal ((1 + 8 / δ) ^ (s - 1 / 2))

theorem coherentAffineCoefficient_ne_top (s C δ : ℝ) :
    coherentAffineCoefficient s C δ ≠ ∞ := by
  exact ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
    ENNReal.ofReal_ne_top

/-- The actual child comparisons satisfy the finite sum bound at every sufficiently fine scale. -/
theorem sum_dyadic_affine_errors_le
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s C δ q : ℝ} (hs : 1 < s) (hs₂ : s ≤ 2) (hC : 1 ≤ C)
    (hfr : IsFrostman μ s C) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hq : 1 ≤ q)
    (c : ℕ → (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (hc : ∀ n k, 0 < μ (dyadicCube n k) → c n k ∈ dyadicCube n k)
    (hrad : ∀ n k, 0 < μ (dyadicCube n k) →
      ν.map (radialAngle (c n k)) =
        radialAngularMeasure.withDensity (radialProjectionDensity ν (c n k)))
    (hsep : ∀ n k, 0 < μ (dyadicCube n k) → ∀ᵐ y ∂ν, δ ≤ dist (c n k) y)
    (B : ℝ≥0∞)
    (hmoment : ∀ n (I : Finset (Fin 2 → ℤ)),
      ∑ k ∈ I, μ (dyadicCube n k) *
        (∫⁻ θ, radialProjectionDensity ν (c n k) θ ^ q ∂radialAngularMeasure) ≤ B)
    (n : ℕ) (I : Finset (Fin 2 → ℤ))
    (hI : ∀ k ∈ I, 0 < μ (dyadicCube (n + 1) k))
    (hr : Real.sqrt 2 / (2 : ℝ) ^ n ≤ δ / 16)
    (A : ℝ≥0∞) (hA : A ≠ 0) (hAt : A ≠ ∞) :
    (∑ k ∈ I, μ (dyadicCube (n + 1) k) * ∫⁻ y, ∫⁻ t : ℝ,
      ENNReal.ofReal |affineDistanceDensity
        (normalizedRestrict μ (dyadicCube (n + 1) k)) (c (n + 1) k) y t -
      affineDistanceDensity (normalizedRestrict μ (dyadicCube (n + 1) k))
        (c n (ancestor 1 k)) y t| ∂volume ∂ν) ≤
      coherentAffineCoefficient s C δ * A ^ (1 / 2 : ℝ) *
        ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2)) *
          (I.card : ℝ≥0∞) ^ (1 / 2 : ℝ) + 4 * B * A ^ (1 - q) := by
  apply sum_coherent_child_errors_le μ n I _
    (fun j k ↦ ∫⁻ θ, radialProjectionDensity ν (c j k) θ ^ q ∂radialAngularMeasure)
    (coherentAffineCoefficient s C δ * A ^ (1 / 2 : ℝ) *
      ENNReal.ofReal ((Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - 1 / 2))) A B q hmoment
  intro k hk
  have hmass := hI k hk
  have hmassfin := measure_ne_top μ (dyadicCube (n + 1) k)
  have hp : 0 < μ (dyadicCube n (ancestor 1 k)) :=
    hmass.trans_le (measure_mono (dyadicCube_subset_parent n k))
  haveI := isProbabilityMeasure_normalizedRestrict
    (measurableSet_dyadicCube (n + 1) k) hmass.ne' hmassfin
  have hm : 0 < (μ (dyadicCube (n + 1) k)).toReal :=
    ENNReal.toReal_pos hmass.ne' hmassfin
  have hm₁ : (μ (dyadicCube (n + 1) k)).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal hmassfin ENNReal.one_ne_top).mpr
        (prob_le_one (μ := μ))
  have hsource : ∀ᵐ x ∂normalizedRestrict μ (dyadicCube (n + 1) k),
      dist x (c (n + 1) k) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
    filter_upwards [ae_mem_dyadicCube_normalizedRestrict μ (n + 1) k] with x hx
    exact dist_le_of_mem_dyadicCube ((dyadicCube_subset_parent n k) hx)
      ((dyadicCube_subset_parent n k) (hc (n + 1) k hmass))
  have hρ (j : ℕ) (l : Fin 2 → ℤ) :
      Measurable (radialProjectionDensity ν (c j l)) :=
    (measurable_radialProjectionDensity ν).of_uncurry_left
  have h := affineDistanceDensity_truncated_L1_bound
    (normalizedRestrict μ (dyadicCube (n + 1) k)) ν hs hs₂ hC hm hm₁
    (isFrostman_normalizedRestrict hfr hmass.ne' hmassfin)
    (c (n + 1) k) (c n (ancestor 1 k)) A hA hAt hq hδ hδ₁
    (by positivity) hr (dist_dyadic_moment_centers_parent μ c hc hmass)
    hsource (hsep (n + 1) k hmass)
    (radialProjectionDensity ν (c (n + 1) k))
    (radialProjectionDensity ν (c n (ancestor 1 k)))
    (hρ _ _) (hρ _ _) (hrad (n + 1) k hmass) (hrad n _ hp)
  simp only [ENNReal.ofReal_toReal hmassfin] at h
  conv_lhs at h =>
    arg 2
    arg 2
    ext y
    arg 2
    ext t
    rw [abs_sub_comm]
  refine h.trans_eq ?_
  simp only [coherentAffineCoefficient,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  ring

end FalconerPacking
