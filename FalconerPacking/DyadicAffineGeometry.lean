/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicCenters

/-!
# Tail geometry for coherent affine approximations

Dyadic cube diameters tend to zero, so a fixed initial depth makes all later cubes smaller
than the source-pin separation. Almost-everywhere source-center bounds lift to the joint law.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerPacking

/-- Dyadic cube diameters vanish. -/
theorem tendsto_dyadic_cube_diameter :
    Tendsto (fun n : ℕ ↦ Real.sqrt 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  simpa only [dyadicRadius, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, div_eq_mul_inv, mul_zero] using
    tendsto_dyadicRadius.const_mul (Real.sqrt 2)

/-- All sufficiently fine cubes are smaller than a sixteenth of any positive separation. -/
theorem exists_dyadic_cube_diameter_le_separation {δ : ℝ} (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → Real.sqrt 2 / (2 : ℝ) ^ n ≤ δ / 16 := by
  have he := tendsto_dyadic_cube_diameter.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < δ / 16))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp he
  exact ⟨n₀, fun n hn ↦ (hn₀ n hn).le⟩

/-- Discarding any fixed initial number of generations preserves vanishing diameter. -/
theorem tendsto_shifted_dyadic_cube_diameter (n₀ : ℕ) :
    Tendsto (fun n : ℕ ↦ Real.sqrt 2 / (2 : ℝ) ^ (n + n₀)) atTop (𝓝 0) :=
  tendsto_dyadic_cube_diameter.comp (tendsto_add_atTop_nat n₀)

/-- Source-center geometry and fixed separation hold for almost every source-pin pair. -/
theorem ae_joint_dyadic_center_geometry
    (μ ν : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ] [SFinite ν]
    {K L : Set (EuclideanSpace ℝ (Fin 2))}
    (hνL : ν Lᶜ = 0) {δ : ℝ}
    (hsep : ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y)
    (c : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hc : ∀ n, Measurable (c n))
    (hgeom : ∀ n, ∀ᵐ x ∂μ, c n x ∈ K ∧
      dist x (c n x) ≤ Real.sqrt 2 / (2 : ℝ) ^ n) (n : ℕ) :
    (∀ᵐ p ∂ν.prod μ, dist p.2 (c n p.2) ≤ Real.sqrt 2 / (2 : ℝ) ^ n) ∧
      ∀ᵐ p ∂ν.prod μ, δ ≤ dist (c n p.2) p.1 := by
  constructor
  · apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le (measurable_snd.dist ((hc n).comp measurable_snd))
        measurable_const)).mpr
    exact Eventually.of_forall fun _ ↦ (hgeom n).mono fun _ hx ↦ hx.2
  · apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const (((hc n).comp measurable_snd).dist
        measurable_fst))).mpr
    filter_upwards [ae_iff.mpr hνL] with y hy
    exact (hgeom n).mono fun x hx ↦ hsep (c n x) hx.1 y hy

end FalconerPacking
