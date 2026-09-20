/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Statement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The dimension definitions

Module 1 of the implementation ledger: the covering definitions of `upperBoxDim` and
`packingDim` used by the statement are related to Mathlib's Hausdorff dimension.

The main results are `dimH_le_upperBoxDim` and `dimH_le_packingDim`: a polynomial covering
bound at the dyadic scales with exponent `s` forces every Hausdorff measure of order `t > s` to
vanish, and packing dimension dominates Hausdorff dimension through countable stability.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- The dyadic radii of the covering definition, as powers of one half. -/
theorem two_rpow_neg_natCast (n : ℕ) : (2 : ℝ) ^ (-(n : ℝ)) = (1 / 2 : ℝ) ^ n := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]

theorem two_rpow_neg_natCast_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _

/-- An open ball has extended diameter at most twice its radius. -/
theorem ediam_ball_le (x : Plane) (r : ℝ) :
    Metric.ediam (Metric.ball x r) ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le fun a ha b hb ↦ ?_
  have ha' : dist a x < r := Metric.mem_ball.1 ha
  have hb' : dist b x < r := Metric.mem_ball.1 hb
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  calc dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
    _ ≤ 2 * r := by rw [dist_comm x b]; linarith

/-- A polynomial covering bound with exponent `s` kills every Hausdorff measure of order
`t > s`. -/
theorem hausdorffMeasure_eq_zero_of_hasUpperBoxBound {E : Set Plane} {s t : ℝ} (hs : 0 ≤ s)
    (h : HasUpperBoxBound E s) (hst : s < t) : μH[t] E = 0 := by
  obtain ⟨C, hC, hcov⟩ := h
  choose pts hsub hcard using hcov
  have ht : 0 ≤ t := hs.trans hst.le
  set r : ℕ → ℝ := fun n ↦ (2 : ℝ) ^ (-(n : ℝ)) with hrdef
  have hrpos : ∀ n, 0 < r n := fun n ↦ two_rpow_neg_natCast_pos n
  -- the comparison sequence, which tends to zero
  set g : ℕ → ℝ := fun n ↦ C * (2 : ℝ) ^ ((n : ℝ) * s) * (2 * r n) ^ t with hgdef
  have hq : (0 : ℝ) < (2 : ℝ) ^ (s - t) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2 : ℝ) ^ (s - t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have e1 : ∀ n : ℕ, (2 : ℝ) ^ ((n : ℝ) * s) = ((2 : ℝ) ^ s) ^ n := by
    intro n
    rw [← Real.rpow_natCast ((2 : ℝ) ^ s) n, ← Real.rpow_mul h2, mul_comm]
  have e2 : ∀ n : ℕ, ((2 : ℝ) ^ (-(n : ℝ))) ^ t = ((2 : ℝ) ^ (-t)) ^ n := by
    intro n
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-t)) n, ← Real.rpow_mul h2, ← Real.rpow_mul h2]
    ring_nf
  have e3 : (2 : ℝ) ^ s * (2 : ℝ) ^ (-t) = (2 : ℝ) ^ (s - t) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have hgeq : ∀ n, g n = C * 2 ^ t * ((2 : ℝ) ^ (s - t)) ^ n := by
    intro n
    simp only [hgdef, hrdef]
    rw [Real.mul_rpow h2 (Real.rpow_nonneg h2 _), e1 n, e2 n, ← e3, mul_pow]
    ring
  have hgtends : Tendsto g atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul (C * 2 ^ t)
    rw [mul_zero] at this
    exact this.congr fun n ↦ (hgeq n).symm
  -- the covering estimate
  refine nonpos_iff_eq_zero.1 ?_
  have hcover := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
    (ι := fun n : ℕ ↦ {x : Plane // x ∈ pts n}) t E
    (fun n ↦ ENNReal.ofReal (2 * r n))
    (by
      have hreal : Tendsto (fun n : ℕ ↦ 2 * r n) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 : ℝ) / 2 < 1)).const_mul 2
        rw [mul_zero] at this
        exact this.congr fun n ↦ by simp only [hrdef, two_rpow_neg_natCast]
      have h3 := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
      rw [ENNReal.ofReal_zero] at h3
      exact h3)
    (fun n i ↦ Metric.ball (i : Plane) (r n))
    (Eventually.of_forall fun n i ↦ ediam_ball_le _ _)
    (Eventually.of_forall fun n ↦ by
      have := hsub n
      rw [Set.iUnion_subtype]
      exact this)
  refine hcover.trans ?_
  have hbound : ∀ n : ℕ,
      (∑ i : {x : Plane // x ∈ pts n}, Metric.ediam (Metric.ball (i : Plane) (r n)) ^ t)
        ≤ ENNReal.ofReal (g n) := by
    intro n
    have hterm : ∀ i : {x : Plane // x ∈ pts n},
        Metric.ediam (Metric.ball (i : Plane) (r n)) ^ t
          ≤ ENNReal.ofReal ((2 * r n) ^ t) := by
      intro i
      rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) ht]
      exact ENNReal.rpow_le_rpow (ediam_ball_le _ _) ht
    refine (Finset.sum_le_sum fun i _ ↦ hterm i).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    have hcardle : ((pts n).card : ℝ≥0∞) ≤ ENNReal.ofReal (C * (2 : ℝ) ^ ((n : ℝ) * s)) := by
      rw [show ((pts n).card : ℝ≥0∞) = ENNReal.ofReal ((pts n).card : ℝ) by
        simp [ENNReal.ofReal_natCast]]
      exact ENNReal.ofReal_le_ofReal (hcard n)
    calc ((pts n).card : ℝ≥0∞) * ENNReal.ofReal ((2 * r n) ^ t)
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ ((n : ℝ) * s)) * ENNReal.ofReal ((2 * r n) ^ t) :=
          by gcongr
      _ = ENNReal.ofReal (g n) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  refine (liminf_le_liminf (Eventually.of_forall hbound)).trans ?_
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (g n)) atTop (𝓝 0) := by
    have h4 := (ENNReal.continuous_ofReal.tendsto 0).comp hgtends
    rw [ENNReal.ofReal_zero] at h4
    exact h4
  exact le_of_eq hlim.liminf_eq

/-- The Hausdorff dimension is at most the covering exponent of any polynomial dyadic bound. -/
theorem dimH_le_of_hasUpperBoxBound {E : Set Plane} {s : ℝ} (hs : 0 ≤ s)
    (h : HasUpperBoxBound E s) : dimH E ≤ ENNReal.ofReal s := by
  refine dimH_le fun d' hd' ↦ ?_
  rw [ENNReal.coe_nnreal_eq, ENNReal.ofReal_le_ofReal_iff hs]
  by_contra hcon
  rw [not_le] at hcon
  rw [hausdorffMeasure_eq_zero_of_hasUpperBoxBound hs h hcon] at hd'
  exact ENNReal.zero_ne_top hd'

/-- Hausdorff dimension is at most upper box dimension. -/
theorem dimH_le_upperBoxDim (E : Set Plane) : dimH E ≤ upperBoxDim E := by
  refine le_iInf fun s ↦ le_iInf fun hs ↦ le_iInf fun h ↦ ?_
  exact dimH_le_of_hasUpperBoxBound hs h

/-- **Hausdorff dimension is at most packing dimension.**  The manuscript uses this to know
that the packing exponent may be taken above the Hausdorff exponent. -/
theorem dimH_le_packingDim (E : Set Plane) : dimH E ≤ packingDim E := by
  refine le_iInf fun K ↦ le_iInf fun hK ↦ le_iInf fun _ ↦ ?_
  calc dimH E ≤ dimH (⋃ n, K n) := dimH_mono hK
    _ = ⨆ n, dimH (K n) := dimH_iUnion _
    _ ≤ ⨆ n, upperBoxDim (K n) := iSup_mono fun n ↦ dimH_le_upperBoxDim _

end FalconerPacking
