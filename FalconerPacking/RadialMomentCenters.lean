/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicMomentCenters
public import FalconerPacking.RadialProjectionKernel

/-!
# One fixed family of radial moment centers

Almost-everywhere radial absolute continuity and an averaged moment bound yield a single
family of dyadic centers. The same family has the geometric and moment properties needed at
every generation, and each selected center lies in the original source set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Select all dyadic centers at once, retaining the actual radial density and moment bound. -/
theorem exists_dyadic_radial_moment_centers
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : μ Kᶜ = 0) (q : ℝ)
    (hac : ∀ᵐ x ∂μ, ν.map (radialAngle x) ≪ radialAngularMeasure) :
    ∃ c : ℕ → (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2),
      (∀ n k, 0 < μ (dyadicCube n k) → c n k ∈ dyadicCube n k ∩ K ∧
        ν.map (radialAngle (c n k)) =
          radialAngularMeasure.withDensity (radialProjectionDensity ν (c n k))) ∧
      (∀ n (I : Finset (Fin 2 → ℤ)),
        ∑ k ∈ I, μ (dyadicCube n k) *
          (∫⁻ θ, radialProjectionDensity ν (c n k) θ ^ q ∂radialAngularMeasure) ≤
        ∫⁻ x, ∫⁻ θ, radialProjectionDensity ν x θ ^ q ∂radialAngularMeasure ∂μ) ∧
      (∀ n, Measurable (dyadicCenterMap n (c n))) ∧
      ∀ n, ∀ᵐ x ∂μ, dyadicCenterMap n (c n) x ∈ K ∧
        dist x (dyadicCenterMap n (c n) x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  let G := K ∩ {x | ν.map (radialAngle x) ≪ radialAngularMeasure}
  have hG : μ Gᶜ = 0 := by
    apply ae_iff.mp
    filter_upwards [ae_iff.mpr hK, hac] with x hx ha
    exact ⟨hx, ha⟩
  obtain ⟨c, hc, _, hsum, hmeas, hgeom⟩ := exists_dyadic_moment_centers μ hG
    (measurable_radialProjectionMoment ν q).aemeasurable
  refine ⟨c, ?_, hsum, hmeas, ?_⟩
  · intro n k hk
    have hx := hc n k hk
    exact ⟨⟨hx.1, hx.2.1⟩,
      (withDensity_radialProjectionDensity_eq ν (c n k) hx.2.2).symm⟩
  · intro n
    exact (hgeom n).mono fun x hx ↦ ⟨hx.1.1, hx.2⟩

/-- A selected child center and its parent center lie in the same parent square. -/
theorem dist_dyadic_moment_centers_parent
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (c : ℕ → (Fin 2 → ℤ) → EuclideanSpace ℝ (Fin 2))
    (hc : ∀ n k, 0 < μ (dyadicCube n k) → c n k ∈ dyadicCube n k)
    {n : ℕ} {k : Fin 2 → ℤ} (hk : 0 < μ (dyadicCube (n + 1) k)) :
    dist (c (n + 1) k) (c n (ancestor 1 k)) ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  have hsub := dyadicCube_subset_parent n k
  have hp : 0 < μ (dyadicCube n (ancestor 1 k)) := hk.trans_le (measure_mono hsub)
  exact dist_le_of_mem_dyadicCube (hsub (hc (n + 1) k hk)) (hc n _ hp)

end FalconerPacking
