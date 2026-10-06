/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SchwartzMeasureReconstruction
public import FalconerPacking.SourceStripPartition

/-!
# Actual packet mass from a source strip and a kernel tail

A bounded spatial cutoff supported in a strip localizes a convolved source in first norm.
The near-source contribution is its actual enlarged-strip mass. The remaining contribution
is the actual transverse tail of the convolution kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- A transverse strip centered at a prescribed signed normal coordinate. -/
def packetSourceStrip (e : EuclideanSpace ℝ (Fin 2)) (c w : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) := {x | |⟪e, x⟫ - c| ≤ w}

theorem measurableSet_packetSourceStrip (e : EuclideanSpace ℝ (Fin 2)) (c w : ℝ) :
    MeasurableSet (packetSourceStrip e c w) := by
  apply isClosed_le (by fun_prop) continuous_const |>.measurableSet

/-- An actual convolution packet is controlled by source mass in twice its strip and the
transverse first-norm tail of its kernel. -/
theorem lintegral_enorm_strip_packet_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (η : EuclideanSpace ℝ (Fin 2) → ℝ) (hη : Continuous η)
    (hηone : ∀ x, |η x| ≤ 1)
    (e : EuclideanSpace ℝ (Fin 2)) (c w : ℝ)
    (hηs : Function.support η ⊆ packetSourceStrip e c w) :
    (∫⁻ x, ‖η x • schwartzMeasureDensity μ K x‖ₑ) ≤
      (∫⁻ z, ‖K z‖ₑ) * μ (packetSourceStrip e c (2 * w)) +
      (∫⁻ z in {z | w ≤ |⟪e, z⟫|}, ‖K z‖ₑ) * μ univ := by
  let S := packetSourceStrip e c (2 * w)
  let V : Set (EuclideanSpace ℝ (Fin 2)) := {z | w ≤ |⟪e, z⟫|}
  let C := ∫⁻ z, ‖K z‖ₑ
  let A := ∫⁻ z in V, ‖K z‖ₑ
  have hS : MeasurableSet S := measurableSet_packetSourceStrip _ _ _
  have hV : MeasurableSet V := isClosed_le continuous_const (by fun_prop) |>.measurableSet
  have hηe (x) : ‖η x‖ₑ ≤ 1 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (hηone x)
  have hpoint (y : EuclideanSpace ℝ (Fin 2)) :
      (∫⁻ x, ‖η x‖ₑ * ‖K (x - y)‖ₑ) ≤ S.indicator (fun _ ↦ C) y + A := by
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      apply le_add_right (le_refl C) |>.trans'
      calc
        _ ≤ ∫⁻ x, ‖K (x - y)‖ₑ := lintegral_mono fun x ↦
          (mul_le_mul' (hηe x) le_rfl).trans_eq (one_mul _)
        _ = C := lintegral_sub_right_eq_self (fun z ↦ ‖K z‖ₑ) y
    · rw [indicator_of_notMem hy, zero_add]
      calc
        _ ≤ ∫⁻ x, V.indicator (fun z ↦ ‖K z‖ₑ) (x - y) := by
          apply lintegral_mono
          intro x
          dsimp only
          by_cases hx : η x = 0
          · simp only [hx, enorm_zero, zero_mul, zero_le]
          · have hs : |⟪e, x⟫ - c| ≤ w := hηs hx
            have hfar : 2 * w < |⟪e, y⟫ - c| := lt_of_not_ge hy
            have ht : |⟪e, y⟫ - c| ≤ |⟪e, x⟫ - c| + |⟪e, x - y⟫| := by
              rw [inner_sub_right]
              calc
                _ = |(⟪e, x⟫ - c) - (⟪e, x⟫ - ⟪e, y⟫)| := by congr 1; ring
                _ ≤ _ := abs_sub _ _
            have hv : x - y ∈ V := by change w ≤ _; linarith
            rw [indicator_of_mem hv]
            exact (mul_le_mul' (hηe x) le_rfl).trans_eq (one_mul _)
        _ = A := by
          rw [lintegral_sub_right_eq_self, lintegral_indicator hV]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖η x‖ₑ * ‖K (x - y)‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      have hm : Measurable (fun y ↦ ‖K (x - y)‖ₑ) :=
        (K.continuous.measurable.comp (measurable_const.sub measurable_id)).enorm
      rw [enorm_smul, lintegral_const_mul _ hm]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    _ = ∫⁻ y, ∫⁻ x, ‖η x‖ₑ * ‖K (x - y)‖ₑ ∂volume ∂μ :=
      lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ y, S.indicator (fun _ ↦ C) y + A ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left (measurable_const.indicator hS), lintegral_indicator hS]
      simp only [lintegral_const, Measure.restrict_apply_univ, S, C, A, V]

/-- The explicit source-strip packet satisfies every cutoff hypothesis in the mass bound. -/
theorem lintegral_enorm_sourceStripPacket_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (R : ℝ) (hR : 0 < R) {w : ℝ} (hw : 0 < w)
    (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) :
    (∫⁻ x, ‖sourceStripPacket R hR w e j x • schwartzMeasureDensity μ K x‖ₑ) ≤
      (∫⁻ z, ‖K z‖ₑ) * μ (packetSourceStrip e (w * j) (2 * w)) +
      (∫⁻ z in {z | w ≤ |⟪e, z⟫|}, ‖K z‖ₑ) * μ univ := by
  apply lintegral_enorm_strip_packet_le μ K _ (sourceStripPacket R hR w e j).continuous
  · intro x
    rw [abs_of_nonneg (sourceStripPacket_nonneg R hR w e j x)]
    exact sourceStripPacket_le_one R hR w e j x
  · intro x hx
    have h : |⟪e, x⟫ - w * j| < w := (support_sourceStripPacket R hR hw e j hx).2
    exact h.le

end FalconerPacking
