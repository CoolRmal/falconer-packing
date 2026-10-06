/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.CircleFourierConvolution
public import FalconerPacking.RadialAngleGeometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Local mass of normalized circle measure

Two angular charts of length pi and the quantitative chord inequality give the actual
radius-over-circle-radius bound for every centered frequency ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace FalconerPacking

instance (r : ℝ) : IsProbabilityMeasure (normalizedCircleMeasure r) := by
  unfold normalizedCircleMeasure
  infer_instance

/-- In one half-turn chart a circle-ball preimage has small angular diameter. -/
theorem volume_circle_closedBall_preimage_chart_le
    {r a : ℝ} (hr : 0 < r)
    (z : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    volume (Icc t (t + Real.pi) ∩
      (fun θ ↦ r • angularDirection θ) ⁻¹' closedBall z a) ≤
      ENNReal.ofReal (Real.pi * a / r) := by
  apply (Real.volume_le_diam _).trans
  apply Metric.ediam_le_of_forall_dist_le
  intro θ hθ φ hφ
  have harc : |φ - θ| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hθ.1.1, hθ.1.2, hφ.1.1, hφ.1.2]
  have hchord : r * ‖angularDirection φ - angularDirection θ‖ ≤ 2 * a := by
    have h := dist_triangle (r • angularDirection φ) z (r • angularDirection θ)
    rw [dist_comm z (r • angularDirection θ)] at h
    have he : dist (r • angularDirection φ) (r • angularDirection θ) =
        r * ‖angularDirection φ - angularDirection θ‖ := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [he] at h
    linarith [mem_closedBall.mp hφ.2, mem_closedBall.mp hθ.2]
  have hang := abs_sub_le_pi_div_two_mul_chord harc
  rw [Real.dist_eq, abs_sub_comm]
  apply (le_div_iff₀ hr).mpr
  have hp := mul_le_mul_of_nonneg_left hchord Real.pi_pos.le
  nlinarith

/-- Every closed frequency ball has normalized circle mass at most its radius divided
by the circle radius. The center is arbitrary. -/
theorem normalizedCircleMeasure_closedBall_le
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (z : EuclideanSpace ℝ (Fin 2)) :
    normalizedCircleMeasure r (closedBall z a) ≤ ENNReal.ofReal (a / r) := by
  have hm : Measurable (fun θ ↦ r • angularDirection θ) := by fun_prop
  let E := (fun θ ↦ r • angularDirection θ) ⁻¹' closedBall z a
  have hE : MeasurableSet E := hm isClosed_closedBall.measurableSet
  have hcover : E ∩ Ioc (-Real.pi) Real.pi ⊆
      (Icc (-Real.pi) (-Real.pi + Real.pi) ∩ E) ∪ (Icc 0 (0 + Real.pi) ∩ E) := by
    intro θ hθ
    rcases le_or_gt θ 0 with h | h
    · exact Or.inl ⟨⟨hθ.2.1.le, by linarith⟩, hθ.1⟩
    · exact Or.inr ⟨⟨h.le, by simpa using hθ.2.2⟩, hθ.1⟩
  rw [normalizedCircleMeasure, Measure.map_apply hm isClosed_closedBall.measurableSet,
    radialAngularProbability, Measure.smul_apply, smul_eq_mul, radialAngularMeasure,
    Measure.restrict_apply hE]
  calc
    _ ≤ (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        (volume (Icc (-Real.pi) (-Real.pi + Real.pi) ∩ E) +
          volume (Icc 0 (0 + Real.pi) ∩ E)) :=
      mul_le_mul_right ((measure_mono hcover).trans (measure_union_le _ _)) _
    _ ≤ (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        (ENNReal.ofReal (Real.pi * a / r) + ENNReal.ofReal (Real.pi * a / r)) :=
      mul_le_mul_right (add_le_add
        (volume_circle_closedBall_preimage_chart_le hr z (-Real.pi))
        (volume_circle_closedBall_preimage_chart_le hr z 0)) _
    _ = _ := by
      have hu : 0 ≤ Real.pi * a / r := by positivity
      rw [← ENNReal.ofReal_add hu hu,
        ← ENNReal.ofReal_inv_of_pos (by positivity : 0 < 2 * Real.pi),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
      congr 1
      field_simp
      ring

/-- The same bound holds for open frequency balls. -/
theorem normalizedCircleMeasure_ball_le
    {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (z : EuclideanSpace ℝ (Fin 2)) :
    normalizedCircleMeasure r (ball z a) ≤ ENNReal.ofReal (a / r) :=
  (measure_mono ball_subset_closedBall).trans (normalizedCircleMeasure_closedBall_le hr ha z)

end FalconerPacking
