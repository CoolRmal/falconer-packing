/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SmoothStripPartition
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Compact smooth planar strip packets

An explicit one-dimensional partition is pulled back along a strip normal and
multiplied by a fixed compact source cutoff. All scale and overlap bounds are proved.
-/

noncomputable section

open Set Metric SchwartzMap
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- A compact source cutoff times one explicitly constructed oriented strip weight. -/
def smoothStripPacket (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  χ x * smoothStripWeight w j ⟪e, x⟫

theorem contDiff_smoothStripPacket (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) :
    ContDiff ℝ ∞ (smoothStripPacket χ w e j) :=
  (χ.smooth ⊤).mul ((contDiff_smoothStripWeight w j).comp (innerSL ℝ e).contDiff)

theorem hasCompactSupport_smoothStripPacket
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) :
    HasCompactSupport (smoothStripPacket χ w e j) := hχ.mul_right

theorem smoothStripPacket_nonneg
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : ∀ x, 0 ≤ χ x)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ smoothStripPacket χ w e j x :=
  mul_nonneg (hχ x) (smoothStripWeight_nonneg w j _)

/-- Packets are supported in the source cutoff and the stated physical strip. -/
theorem support_smoothStripPacket
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    {w : ℝ} (hw : 0 < w) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) :
    Function.support (smoothStripPacket χ w e j) ⊆
      Function.support χ ∩ {x | |⟪e, x⟫ - w * j| < w} := by
  intro x hx
  have h := mul_ne_zero_iff.mp hx
  exact ⟨h.1, smoothStripWeight_support hw j h.2⟩

/-- The compact packet sum is exactly the given source cutoff. -/
theorem sum_smoothStripPacket_eq
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    {R w : ℝ} (hχ : Function.support χ ⊆ closedBall 0 R) (hw : 0 < w)
    {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ ≤ 1)
    (M : ℕ) (hM : R ≤ w * M) (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ j ∈ slopeNet M, smoothStripPacket χ w e j x) = χ x := by
  simp only [smoothStripPacket, ← Finset.mul_sum]
  by_cases hx : χ x = 0
  · simp only [hx, zero_mul]
  have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hχ hx
  have hi : |⟪e, x⟫| ≤ w * M :=
    (abs_real_inner_le_norm e x).trans ((mul_le_of_le_one_left (norm_nonneg x) he).trans
      (hxR.trans hM))
  rw [sum_smoothStripWeight_eq_one hw M hi, mul_one]

/-- Spatial overlap is uniformly bounded, independently of width, direction, and packet count. -/
theorem card_smoothStripPacket_support_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (I : Finset ℤ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (I.filter (fun j ↦ smoothStripPacket χ w e j x ≠ 0)).card ≤ 3 := by
  classical
  refine (Finset.card_le_card ?_).trans (card_smoothStripWeight_support_le w I ⟪e, x⟫)
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
    (mul_ne_zero_iff.mp (Finset.mem_filter.mp hj).2).2⟩

/-- Pulling back a scalar strip weight by a unit-bounded normal does not enlarge its derivatives. -/
theorem norm_iteratedFDeriv_orientedStrip_le (n : ℕ) (w : ℝ) (j : ℤ)
    {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ ≤ 1) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ n (fun y ↦ smoothStripWeight w j ⟪e, y⟫) x‖ ≤
      ‖iteratedDeriv n (smoothStripWeight w j) ⟪e, x⟫‖ := by
  have hc : ContDiff ℝ n (smoothStripWeight w j) :=
    (contDiff_smoothStripWeight w j).of_le (by exact_mod_cast le_top)
  rw [show (fun y ↦ smoothStripWeight w j ⟪e, y⟫) =
      smoothStripWeight w j ∘ innerSL ℝ e from rfl,
    (innerSL ℝ e).iteratedFDeriv_comp_right hc x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, innerSL_apply_norm]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) he)

/-- The derivative constant is independent of width, strip index, normal, and spatial point. -/
theorem exists_smoothStripPacket_derivative_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w →
      ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)),
        ‖iteratedFDeriv ℝ n (smoothStripPacket χ w e j) x‖ ≤ C * max 1 w⁻¹ ^ n := by
  classical
  choose D hD hbound using exists_smoothStripWeight_derivative_bound
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i χ * D (n - i)
  refine ⟨C, Finset.sum_nonneg (fun i hi ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (hD _)), ?_⟩
  intro w hw e he j x
  have hbase : 1 ≤ max 1 w⁻¹ := le_max_left _ _
  have hmul := norm_iteratedFDeriv_mul_le (χ.smooth ⊤)
    ((contDiff_smoothStripWeight w j).comp (innerSL ℝ e).contDiff) x
    (by exact_mod_cast le_top : (n : ℕ∞ω) ≤ ∞)
  refine hmul.trans ?_
  dsimp only [C]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hχi := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ i x
  have hgi := (norm_iteratedFDeriv_orientedStrip_le (n - i) w j he x).trans
    (hbound (n - i) w hw j ⟪e, x⟫)
  have hpow : w⁻¹ ^ (n - i) ≤ max 1 w⁻¹ ^ n :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hw.le) (le_max_right 1 w⁻¹) _).trans
      (pow_le_pow_right₀ hbase (Nat.sub_le _ _))
  calc
    _ ≤ (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i χ *
        (D (n - i) * w⁻¹ ^ (n - i)) := by
      gcongr
      exact hgi
    _ ≤ (n.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i χ * (D (n - i) * max 1 w⁻¹ ^ n) := by
      gcongr
      exact hD _
    _ = _ := by ring

/-- In the packet range `w ≤ 1`, the full spatial bound has exactly the power `w⁻ⁿ`. -/
theorem exists_smoothStripPacket_derivative_bound_of_le_one
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)),
        ‖iteratedFDeriv ℝ n (smoothStripPacket χ w e j) x‖ ≤ C * w⁻¹ ^ n := by
  obtain ⟨C, hC, hbound⟩ := exists_smoothStripPacket_derivative_bound χ n
  refine ⟨C, hC, fun w hw hw₁ e he j x ↦ ?_⟩
  simpa only [max_eq_right ((one_le_inv₀ hw).mpr hw₁)] using hbound w hw e he j x

end FalconerPacking
