/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AnnularPinnedDensity

/-!
# Absolute continuity from separately constructed late annular pieces

Only sufficiently late annuli need a good part. Early annuli are assigned wholly to the
bad part, whose integrability is already proved for the actual compact source expansion.
There is no compatibility requirement between decompositions at different frequencies.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Classical
open scoped ENNReal Topology

namespace FalconerPacking

/-- Separately constructed measurable good pieces with summable second- and first-norm
bounds for their actual remainders imply pinned absolute continuity. -/
theorem pinnedDistance_absolutelyContinuous_of_eventual_annular_good_parts
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {M : ℝ} (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχone : ∀ᵐ x ∂μ, χ x = 1) (hχnorm : ∀ x, ‖χ x‖ ≤ 1)
    {T : ℕ} (hT : 0 < T) {L : ℝ}
    (hL : ∀ᵐ y ∂ν, ∀ x ∈ Function.support χ, dist x y ≤ L)
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hparts : ∀ᶠ n : ℕ in atTop,
      ∃ g : EuclideanSpace ℝ (Fin 2) × ℝ → ℂ, Measurable g ∧
        (∫⁻ p, ‖g p‖ₑ ^ 2 ∂ν.prod volume) ≤
          ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ))) ∧
        (∫⁻ p, ‖complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n) p.1 p.2 -
          g p‖ₑ ∂ν.prod volume) ≤
            ENNReal.ofReal (C * (2 : ℝ) ^ (-ε * (n : ℝ)))) :
    jointPinnedDistanceMeasure μ ν ≪ ν.prod volume ∧
      ∀ᵐ y ∂ν, pinnedDistanceMeasure μ y ≪ volume := by
  obtain ⟨n₀, hlate⟩ := eventually_atTop.mp hparts
  let good (n : ℕ) := if hn : n₀ ≤ n then Classical.choose (hlate n hn) else fun _ ↦ 0
  let full (n : ℕ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) :=
    complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n) p.1 p.2
  let bad (n : ℕ) (p : EuclideanSpace ℝ (Fin 2) × ℝ) := full n p - good n p
  have hfull (n : ℕ) : Measurable (full n) :=
    measurable_joint_complexDistanceDensity (compactAnnularSource μ hμ χ hχ T n).continuous.measurable
  have hgood (n : ℕ) : Measurable (good n) := by
    dsimp [good]
    split
    · exact (Classical.choose_spec (hlate n ‹_›)).1
    · exact measurable_const
  apply pinnedDistance_absolutelyContinuous_of_dyadic_annular_bounds
    μ ν hμ χ hχ hχone hχnorm hT hL good bad hgood
    (fun n ↦ (hfull n).sub (hgood n)) ?_ n₀ ?_ ?_ hC hε ?_ ?_
  · intro n
    exact ae_of_all _ fun p ↦ by dsimp [bad, full]; ring
  · intro n hn
    have hzero : good n = fun _ ↦ 0 := by simp [good, not_le_of_gt hn]
    rw [hzero]
    exact MemLp.zero
  · intro n hn
    have hbad : bad n = full n := by
      ext p
      simp [bad, good, not_le_of_gt hn]
    rw [hbad]
    exact integrable_joint_complexDistanceDensity ν
      (compactAnnularSource μ hμ χ hχ T n).continuous.measurable
      (compactAnnularSource μ hμ χ hχ T n).integrable
  · intro n hn
    simpa only [good, dif_pos hn, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      using (Classical.choose_spec (hlate n hn)).2.1
  · intro n hn
    simpa only [bad, full, good, dif_pos hn, ofReal_norm]
      using (Classical.choose_spec (hlate n hn)).2.2

end FalconerPacking
