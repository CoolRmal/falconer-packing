/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AffineDistance
public import FalconerPacking.CorrelatedAngularCharts
public import FalconerPacking.ProjectionDensity

/-!
# Geometric inputs for comparing affine distance maps

Two nearby affine distance approximations become two orthogonal projections of the same
translated source, with a common offset and a quadratic residual translation. Separation
from the pin supplies every angular and translation bound used by the Fourier comparison.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The residual translation after subtracting the common distance offset at `b`. -/
def affineProjectionShift (b c y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  affineDistance c b y - dist b y

@[fun_prop]
theorem measurable_affineProjectionShift (b c : EuclideanSpace ℝ (Fin 2)) :
    Measurable (affineProjectionShift b c) := by
  unfold affineProjectionShift affineDistance
  fun_prop

/-- Affine distance at the first center is its distance offset plus a projection of `x-b`. -/
theorem affineDistance_eq_projection_add_dist
    {b y : EuclideanSpace ℝ (Fin 2)} (hby : b ≠ y) (x : EuclideanSpace ℝ (Fin 2)) :
    affineDistance b x y = ⟪x - b, angularDirection (radialAngle b y)⟫ + dist b y := by
  have he : x - y = (x - b) + (b - y) := by abel
  rw [affineDistance, he, inner_add_right, angularDirection_radialAngle hby,
    real_inner_comm (x - b)]
  change _ + affineDistance b b y = _
  rw [affineDistance_self hby]

/-- Affine distance at the second center has the same common offset and a residual shift. -/
theorem affineDistance_eq_shifted_projection_add_dist
    {b c y : EuclideanSpace ℝ (Fin 2)} (hcy : c ≠ y) (x : EuclideanSpace ℝ (Fin 2)) :
    affineDistance c x y =
      (⟪x - b, angularDirection (radialAngle c y)⟫ + affineProjectionShift b c y) + dist b y := by
  have he : x - y = (x - b) + (b - y) := by abel
  rw [affineDistance, he, inner_add_right, angularDirection_radialAngle hcy,
    real_inner_comm (x - b), affineProjectionShift, affineDistance]
  ring

/-- A nearby second center inherits half the pin separation of the first. -/
theorem half_separation_le_dist_center
    {b c y : EuclideanSpace ℝ (Fin 2)} {δ r : ℝ}
    (hsep : δ ≤ dist b y) (hbc : dist b c ≤ r) (hr : r ≤ δ / 2) :
    δ / 2 ≤ dist c y := by
  have htri := dist_triangle b c y
  linarith

/-- The residual shift is quadratic in the center displacement. -/
theorem abs_affineProjectionShift_le
    {b c y : EuclideanSpace ℝ (Fin 2)} {δ r : ℝ} (hδ : 0 < δ)
    (hsep : δ ≤ dist b y) (hbc : dist b c ≤ r) (hr : r ≤ δ / 4) :
    |affineProjectionShift b c y| ≤ 2 * r ^ 2 / δ := by
  have hcysep := half_separation_le_dist_center hsep hbc (by linarith)
  have hcy : c ≠ y := dist_pos.1 (lt_of_lt_of_le (by linarith : 0 < δ / 2) hcysep)
  have hbound := abs_affineDistance_sub_dist_le hcy hbc (by linarith : r ≤ dist c y / 2)
  calc
    |affineProjectionShift b c y| ≤ r ^ 2 / dist c y := hbound
    _ ≤ r ^ 2 / (δ / 2) :=
      div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hcysep
    _ = _ := by ring

/-- A common radius for the source, angular, and quadratic-translation comparisons. -/
def affineComparisonRadius (δ r : ℝ) : ℝ := (1 + 8 / δ) * r

theorem affineComparisonRadius_pos {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    0 < affineComparisonRadius δ r := by unfold affineComparisonRadius; positivity

theorem le_affineComparisonRadius {δ r : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r) :
    r ≤ affineComparisonRadius δ r := by
  unfold affineComparisonRadius
  nlinarith [div_pos (by norm_num : (0 : ℝ) < 8) hδ]

/-- At sufficiently fine scales the common comparison radius is at most one. -/
theorem affineComparisonRadius_le_one {δ r : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hr : r ≤ δ / 16) : affineComparisonRadius δ r ≤ 1 := by
  have hfactor : 0 ≤ 1 + 8 / δ := by positivity
  have h := mul_le_mul_of_nonneg_left hr hfactor
  have he : (1 + 8 / δ) * (δ / 16) = (δ + 8) / 16 := by field_simp
  rw [he] at h
  unfold affineComparisonRadius
  linarith

/-- Actual separated centers give the circular angular and residual shift bounds. -/
theorem affineProjection_comparison_bounds
    {b c y : EuclideanSpace ℝ (Fin 2)} {δ r : ℝ} (hδ : 0 < δ) (hr₀ : 0 ≤ r)
    (hsep : δ ≤ dist b y) (hbc : dist b c ≤ r) (hr : r ≤ δ / 4) :
    (Real.pi / 2) *
        ‖angularDirection (radialAngle c y) - angularDirection (radialAngle b y)‖ ≤
      affineComparisonRadius δ r ∧
      |affineProjectionShift b c y| ≤ (affineComparisonRadius δ r) ^ 2 := by
  have hcysep := half_separation_le_dist_center hsep hbc (by linarith)
  have hdir := norm_radialDirection_sub_le (by positivity : 0 < δ / 2)
    hcysep (by linarith : δ / 2 ≤ dist b y)
  rw [dist_comm c b] at hdir
  constructor
  · have hdir' : (Real.pi / 2) *
        ‖angularDirection (radialAngle c y) - angularDirection (radialAngle b y)‖ ≤
        2 * Real.pi * r / δ := by
      calc
        _ ≤ (Real.pi / 2) * (2 * dist b c / (δ / 2)) :=
          mul_le_mul_of_nonneg_left hdir (by positivity)
        _ ≤ (Real.pi / 2) * (2 * r / (δ / 2)) := by gcongr
        _ = _ := by ring
    apply hdir'.trans
    unfold affineComparisonRadius
    rw [div_le_iff₀ hδ]
    field_simp
    nlinarith [Real.pi_le_four, mul_nonneg hδ.le hr₀]
  · apply (abs_affineProjectionShift_le hδ hsep hbc hr).trans
    unfold affineComparisonRadius
    have he : (1 + 8 / δ) * δ = δ + 8 := by field_simp
    have hfactor : (0 : ℝ) ≤ 1 + 8 / δ := by positivity
    have hsquare : 2 / δ ≤ (1 + 8 / δ) ^ 2 := by
      rw [div_le_iff₀ hδ]
      nlinarith [sq_nonneg (8 / δ), div_pos (by norm_num : (0 : ℝ) < 8) hδ]
    calc
      2 * r ^ 2 / δ = (2 / δ) * r ^ 2 := by ring
      _ ≤ (1 + 8 / δ) ^ 2 * r ^ 2 :=
        mul_le_mul_of_nonneg_right hsquare (sq_nonneg r)
      _ = _ := by ring

/-- Translating the source leaves its Frostman constant unchanged. -/
theorem IsFrostman.map_sub_const
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ}
    (hμ : IsFrostman μ s C) (b : EuclideanSpace ℝ (Fin 2)) :
    IsFrostman (μ.map (fun x ↦ x - b)) s C := by
  intro z r hr hr₁
  rw [Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet]
  have he : (fun x ↦ x - b) ⁻¹' Metric.ball z r = Metric.ball (z + b) r := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm]
    abel_nf
  rw [he]
  exact hμ (z + b) r hr hr₁

/-- Translating a source supported within radius `r` gives the required centered support. -/
theorem ae_norm_le_map_sub_const
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {b : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hsource : ∀ᵐ x ∂μ, dist x b ≤ r) :
    ∀ᵐ z ∂μ.map (fun x ↦ x - b), ‖z‖ ≤ r := by
  rw [ae_map_iff (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  simpa only [dist_eq_norm] using hsource

/-- The original affine-distance law is a translated projection law of the centered source. -/
theorem map_affineDistance_eq_projection_translate
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    {b y : EuclideanSpace ℝ (Fin 2)} (hby : b ≠ y) :
    μ.map (fun x ↦ affineDistance b x y) =
      (orthogonalProjectionKernel (μ.map (fun x ↦ x - b)) (radialAngle b y)).map
        (fun t ↦ t + dist b y) := by
  rw [orthogonalProjectionKernel_apply,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact affineDistance_eq_projection_add_dist hby x

/-- The second original affine-distance law has the same offset and the residual shift. -/
theorem map_affineDistance_eq_shifted_projection_translate
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [SFinite μ]
    {b c y : EuclideanSpace ℝ (Fin 2)} (hcy : c ≠ y) :
    μ.map (fun x ↦ affineDistance c x y) =
      (orthogonalProjectionKernel (μ.map (fun x ↦ x - b)) (radialAngle c y)).map
        (fun t ↦ (t + affineProjectionShift b c y) + dist b y) := by
  rw [orthogonalProjectionKernel_apply,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact affineDistance_eq_shifted_projection_add_dist hcy x

/-- All geometric and source-measure inputs for the circular projection comparison follow
from actual nearby centers, a small source ball, and pin separation. -/
theorem affineProjection_comparison_inputs
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μ]
    {κ : Measure (EuclideanSpace ℝ (Fin 2))} [SFinite κ]
    {b c : EuclideanSpace ℝ (Fin 2)} {δ r s C : ℝ}
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hr : 0 < r) (hrδ : r ≤ δ / 16)
    (hbc : dist b c ≤ r) (hfr : IsFrostman μ s C)
    (hsource : ∀ᵐ x ∂μ, dist x b ≤ r) (hsep : ∀ᵐ y ∂κ, δ ≤ dist b y) :
    0 < affineComparisonRadius δ r ∧ affineComparisonRadius δ r ≤ 1 ∧
      IsProbabilityMeasure (μ.map (fun x ↦ x - b)) ∧
      IsFrostman (μ.map (fun x ↦ x - b)) s C ∧
      (∀ᵐ z ∂μ.map (fun x ↦ x - b), ‖z‖ ≤ affineComparisonRadius δ r) ∧
      ∀ᵐ y ∂κ,
        (radialAngle b y ∈ Icc (-Real.pi) Real.pi ∧
          radialAngle c y ∈ Icc (-Real.pi) Real.pi) ∧
        (Real.pi / 2) *
            ‖angularDirection (radialAngle c y) - angularDirection (radialAngle b y)‖ ≤
          affineComparisonRadius δ r ∧
        |affineProjectionShift b c y| ≤ (affineComparisonRadius δ r) ^ 2 ∧
        μ.map (fun x ↦ affineDistance b x y) =
          (orthogonalProjectionKernel (μ.map (fun x ↦ x - b)) (radialAngle b y)).map
            (fun t ↦ t + dist b y) ∧
        μ.map (fun x ↦ affineDistance c x y) =
          (orthogonalProjectionKernel (μ.map (fun x ↦ x - b)) (radialAngle c y)).map
            (fun t ↦ (t + affineProjectionShift b c y) + dist b y) := by
  refine ⟨affineComparisonRadius_pos hδ hr, affineComparisonRadius_le_one hδ hδ₁ hrδ,
    inferInstance, hfr.map_sub_const b, ?_, ?_⟩
  · exact (ae_norm_le_map_sub_const hsource).mono fun _ hz ↦
      hz.trans (le_affineComparisonRadius hδ hr.le)
  · filter_upwards [hsep] with y hy
    have hrδ' : r ≤ δ / 4 := by linarith
    have hby : b ≠ y := dist_pos.1 (hδ.trans_le hy)
    have hcysep := half_separation_le_dist_center hy hbc (by linarith)
    have hcy : c ≠ y := dist_pos.1 (lt_of_lt_of_le (by linarith : 0 < δ / 2) hcysep)
    obtain ⟨hangle, hshift⟩ := affineProjection_comparison_bounds hδ hr.le hy hbc hrδ'
    exact ⟨⟨⟨(radialAngle_mem b y).1.le, (radialAngle_mem b y).2⟩,
      ⟨(radialAngle_mem c y).1.le, (radialAngle_mem c y).2⟩⟩, hangle, hshift,
      map_affineDistance_eq_projection_translate μ hby,
      map_affineDistance_eq_shifted_projection_translate μ hcy⟩

end FalconerPacking
