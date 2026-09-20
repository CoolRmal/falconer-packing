/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PinnedKernel
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Affine approximation to distance

This file defines the positive linearization used on each source cube and proves its quadratic
error estimate away from the pin.  The estimate supplies the geometric `hclose` hypothesis of
the coherent joint-approximation theorem.
-/

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace FalconerPacking

/-- Linearize `x ↦ dist x y` at the source center `b`. -/
def affineDistance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b x y : E) : ℝ :=
  inner ℝ ((‖b - y‖)⁻¹ • (b - y)) (x - y)

/-- Keep the pin and replace distance by the affine approximation based at a center selected
from the source point.  The input order is `(pin, source)`, matching `ν.prod μ`. -/
def affineJointDistanceMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E → E) (p : E × E) : E × ℝ :=
  (p.1, affineDistance (c p.2) p.2 p.1)

/-- A measurable center selection gives a measurable joint affine-distance map. -/
theorem measurable_affineJointDistanceMap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {c : E → E} (hc : Measurable c) :
    Measurable (affineJointDistanceMap c) := by
  have hcenter : Measurable fun p : E × E ↦ c p.2 - p.1 :=
    (hc.comp measurable_snd).sub measurable_fst
  have hdirection : Measurable fun p : E × E ↦
      (‖c p.2 - p.1‖)⁻¹ • (c p.2 - p.1) :=
    hcenter.norm.inv.smul hcenter
  have hsource : Measurable fun p : E × E ↦ p.2 - p.1 :=
    measurable_snd.sub measurable_fst
  exact measurable_fst.prodMk
    (continuous_inner.measurable.comp (hdirection.prodMk hsource))

/-- The direction from the pin to a distinct center has norm one. -/
theorem norm_inv_norm_smul_sub_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b y : E} (hby : b ≠ y) :
    ‖(‖b - y‖)⁻¹ • (b - y)‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
  simpa [sub_ne_zero] using hby

/-- The affine approximation is exact at its center. -/
@[simp]
theorem affineDistance_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b y : E} (hby : b ≠ y) :
    affineDistance b b y = dist b y := by
  rw [affineDistance, real_inner_smul_left, real_inner_self_eq_norm_sq,
    dist_eq_norm]
  field_simp [sub_ne_zero.mpr hby]

/-- The affine approximation underestimates the true distance. -/
theorem affineDistance_le_dist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b x y : E} (hby : b ≠ y) :
    affineDistance b x y ≤ dist x y := by
  calc
    affineDistance b x y
        ≤ ‖(‖b - y‖)⁻¹ • (b - y)‖ * ‖x - y‖ := by
      exact real_inner_le_norm _ _
    _ = dist x y := by rw [norm_inv_norm_smul_sub_eq_one hby, one_mul, dist_eq_norm]

/-- In a ball whose radius is at most half the center-pin separation, linearizing distance at
the center makes a quadratic error. -/
theorem abs_affineDistance_sub_dist_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {b x y : E} (hby : b ≠ y) {r : ℝ}
    (hxb : dist x b ≤ r) (hr : r ≤ dist b y / 2) :
    |affineDistance b x y - dist x y| ≤ r ^ 2 / dist b y := by
  let u := b - y
  let h := x - b
  let e := (‖u‖)⁻¹ • u
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hby)
  have hh : ‖h‖ ≤ r := by simpa [h, dist_eq_norm, norm_sub_rev] using hxb
  have hr' : r ≤ ‖u‖ / 2 := by simpa [u, dist_eq_norm] using hr
  have he : ‖e‖ = 1 := by
    simpa [e, u] using norm_inv_norm_smul_sub_eq_one hby
  have heh_abs : |inner ℝ e h| ≤ ‖h‖ := by
    simpa [he] using abs_real_inner_le_norm e h
  have heh_lower : -‖h‖ ≤ inner ℝ e h :=
    (abs_le.mp heh_abs).1
  have heh_upper : inner ℝ e h ≤ ‖h‖ :=
    (abs_le.mp heh_abs).2
  have heu : inner ℝ e u = ‖u‖ := by
    simp only [e, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp [ne_of_gt hu]
  have hinner : inner ℝ u h = ‖u‖ * inner ℝ e h := by
    simp only [e, real_inner_smul_left]
    field_simp [ne_of_gt hu]
  have hxy : x - y = u + h := by
    simp only [u, h]
    abel
  have haff : affineDistance b x y = ‖u‖ + inner ℝ e h := by
    rw [affineDistance, hxy, inner_add_right, heu]
  have hsq : ‖u + h‖ ^ 2 - (‖u‖ + inner ℝ e h) ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [norm_add_sq_real, hinner]
    nlinarith [sq_nonneg (inner ℝ e h)]
  have hnorm_lower : ‖u‖ / 2 ≤ ‖u + h‖ := by
    have htri : ‖u‖ ≤ ‖u + h‖ + ‖h‖ := by
      calc
        ‖u‖ = ‖(u + h) - h‖ := by congr 1; abel
        _ ≤ ‖u + h‖ + ‖h‖ := norm_sub_le _ _
    nlinarith
  have haff_lower : ‖u‖ / 2 ≤ ‖u‖ + inner ℝ e h := by
    nlinarith
  have hdiff_nonneg :
      0 ≤ ‖u + h‖ - (‖u‖ + inner ℝ e h) := by
    simpa [← hxy, ← haff, dist_eq_norm] using affineDistance_le_dist hby
  have hsum : ‖u‖ ≤ ‖u + h‖ + (‖u‖ + inner ℝ e h) := by
    nlinarith
  have hquad :
      (‖u + h‖ - (‖u‖ + inner ℝ e h)) * ‖u‖ ≤ ‖h‖ ^ 2 := by
    calc
      (‖u + h‖ - (‖u‖ + inner ℝ e h)) * ‖u‖
          ≤ (‖u + h‖ - (‖u‖ + inner ℝ e h)) *
              (‖u + h‖ + (‖u‖ + inner ℝ e h)) :=
        mul_le_mul_of_nonneg_left hsum hdiff_nonneg
      _ = ‖u + h‖ ^ 2 - (‖u‖ + inner ℝ e h) ^ 2 := by ring
      _ ≤ ‖h‖ ^ 2 := hsq
  have herror :
      ‖u + h‖ - (‖u‖ + inner ℝ e h) ≤ ‖h‖ ^ 2 / ‖u‖ := by
    rw [le_div_iff₀ hu]
    exact hquad
  rw [abs_of_nonpos (sub_nonpos.mpr (affineDistance_le_dist hby)), neg_sub,
    haff, dist_eq_norm, hxy]
  calc
    ‖u + h‖ - (‖u‖ + inner ℝ e h) ≤ ‖h‖ ^ 2 / ‖u‖ := herror
    _ ≤ r ^ 2 / ‖u‖ := by
      gcongr
    _ = r ^ 2 / dist b y := by rw [dist_eq_norm]

/-- A uniform positive separation turns the quadratic estimate into a uniform error bound for
the joint affine map. -/
theorem dist_affineJointDistanceMap_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : E → E) {p : E × E} {r δ : ℝ}
    (hδ : 0 < δ) (hsource : dist p.2 (c p.2) ≤ r)
    (hseparated : δ ≤ dist (c p.2) p.1) (hr : r ≤ δ / 2) :
    dist (affineJointDistanceMap c p) (p.1, dist p.2 p.1) ≤ r ^ 2 / δ := by
  have hdist : 0 < dist (c p.2) p.1 := hδ.trans_le hseparated
  have hcne : c p.2 ≠ p.1 := dist_pos.mp hdist
  have hr' : r ≤ dist (c p.2) p.1 / 2 := hr.trans (by gcongr)
  have hlocal := abs_affineDistance_sub_dist_le hcne hsource hr'
  change dist (p.1, affineDistance (c p.2) p.2 p.1)
      (p.1, dist p.2 p.1) ≤ r ^ 2 / δ
  rw [dist_prod_same_left, Real.dist_eq]
  exact hlocal.trans (by
    apply (div_le_div_iff₀ hdist hδ).2
    gcongr)

/-- Squaring a vanishing source scale and dividing by a fixed positive separation still tends
to zero. -/
theorem tendsto_sq_div_const
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) (δ : ℝ) :
    Tendsto (fun n ↦ r n ^ 2 / δ) atTop (𝓝 0) := by
  simpa using (hr.pow 2).div_const δ

/-- A separated coherent affine construction needs no additional weak-limit hypothesis.  The
quadratic estimate above supplies uniform convergence to distance, so the remaining analytic
work is exactly the construction and successive `L¹` comparison of the displayed densities. -/
theorem exists_mem_volume_pinnedDistances_pos_of_coherent_affineDistance
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {E F : Set (EuclideanSpace ℝ (Fin 2))}
    (c : ℕ → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (r : ℕ → ℝ)
    (f : ℕ →
      (EuclideanSpace ℝ (Fin 2) × ℝ) →₁[
        (ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume] ℝ)
    {δ : ℝ} {Z : ℕ → ℝ≥0∞} {K : ℝ≥0∞} {eta : ℝ}
    (hμE : 0 < (μ : Measure (EuclideanSpace ℝ (Fin 2))) E)
    (hνF : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Fᶜ = 0)
    (hδ : 0 < δ) (hc : ∀ n, Measurable (c n))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hsource : ∀ n x, dist x (c n x) ≤ r n)
    (hseparated : ∀ n
      (p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
        δ ≤ dist (c n p.2) p.1)
    (hrhalf : ∀ n, r n ≤ δ / 2)
    (hdensity : ∀ n,
      (((ν.prod μ : ProbabilityMeasure
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) :
          Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))).map
            (affineJointDistanceMap (c n))) =
        (finiteMeasureOfL1Density
          ((ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume) (f n) :
            Measure (EuclideanSpace ℝ (Fin 2) × ℝ)))
    (hK : K ≠ ∞) (hZ : (∑' n, Z n ^ eta) ≠ ∞)
    (hstep : ∀ n, edist (f n) (f n.succ) ≤ K * Z n ^ eta) :
    ∃ y ∈ F, 0 < volume (pinnedDistances E y) := by
  apply exists_mem_volume_pinnedDistances_pos_of_coherent_approximation
    μ ν (E := E) (F := F) (fun n ↦ affineJointDistanceMap (c n)) f hμE hνF
  · intro n
    exact (measurable_affineJointDistanceMap (hc n)).aemeasurable
  · exact tendsto_sq_div_const hr0 δ
  · intro n p
    exact dist_affineJointDistanceMap_le (c n) hδ
      (hsource n p.2) (hseparated n p) (hrhalf n)
  · exact hdensity
  · exact hK
  · exact hZ
  · exact hstep

end FalconerPacking
