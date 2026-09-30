/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.DyadicCapacity
import FalconerPacking.FrostmanLimit

/-!
# Dyadic content and Hausdorff dimension

Comparison with small Euclidean balls connects the geometric dyadic capacity to Hausdorff
dimension. This permits the capacity extraction theorem to produce compact subsets of Borel
sets without any assumption of sigma-finite Hausdorff measure.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FalconerPacking

/-- Countable subadditivity of the concrete dyadic covering content. -/
theorem dyadicCoverContent_iUnion_le (w : DyadicCell → ℝ≥0∞)
    (E : ℕ → Set (EuclideanSpace ℝ (Fin 2))) :
    dyadicCoverContent w (⋃ n, E n) ≤ ∑' n, dyadicCoverContent w (E n) := by
  classical
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hfinite
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.mpr hε).ne' ℕ
  have hnear (n : ℕ) : ∃ S : Set DyadicCell, IsAntichain (· ≤ ·) S ∧
      E n ⊆ dyadicCoverUnion S ∧
        dyadicCoverCost w S < dyadicCoverContent w (E n) + δ n :=
    exists_antichain_dyadicCoverCost_lt w (ENNReal.lt_add_right
      ((ENNReal.le_tsum n).trans_lt hfinite).ne (ENNReal.coe_pos.mpr (hδpos n)).ne')
  choose S _ hcover hcost using hnear
  have hsub : (⋃ n, E n) ⊆ dyadicCoverUnion (⋃ n, S n) := by
    intro x hx
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp (hcover n hxn)
    exact mem_iUnion₂.mpr ⟨Q, mem_iUnion.mpr ⟨n, hQ⟩, hxQ⟩
  refine (dyadicCoverContent_le_cost w hsub).trans ((dyadicCoverCost_iUnion_le w S).trans ?_)
  calc
    _ ≤ ∑' n, (dyadicCoverContent w (E n) + (δ n : ℝ≥0∞)) :=
      ENNReal.tsum_le_tsum fun n ↦ (hcost n).le
    _ = (∑' n, dyadicCoverContent w (E n)) + ∑' n, (δ n : ℝ≥0∞) := ENNReal.tsum_add
    _ ≤ _ := add_le_add le_rfl hδsum.le

/-- Dyadic covering content packaged as an outer measure. -/
def dyadicCoverOuterMeasure (w : DyadicCell → ℝ≥0∞) :
    OuterMeasure (EuclideanSpace ℝ (Fin 2)) where
  measureOf := dyadicCoverContent w
  empty := by
    apply le_antisymm _ zero_le
    exact (dyadicCoverContent_le_cost w (S := ∅) (empty_subset _)).trans_eq
      (by simp [dyadicCoverCost])
  mono := fun h ↦ dyadicCoverContent_mono w h
  iUnion_nat := fun E _ ↦ dyadicCoverContent_iUnion_le w E

/-- A cube cover controls ordinary Hausdorff content with the Euclidean diameter constant. -/
theorem hausdorffContent_le_dyadicCoverCost {s : ℝ} (hs : 0 ≤ s)
    {E : Set (EuclideanSpace ℝ (Fin 2))} {S : Set DyadicCell}
    (hcover : E ⊆ dyadicCoverUnion S) :
    hausdorffContent s E ≤ ENNReal.ofReal (Real.sqrt 2 ^ s) *
      dyadicCoverCost (dyadicPowerWeight s) S := by
  calc
    _ ≤ hausdorffContent s (dyadicCoverUnion S) := measure_mono hcover
    _ ≤ ∑' Q : S, hausdorffContent s Q.val.carrier :=
      measure_biUnion_le _ (Set.to_countable S) _
    _ ≤ ∑' Q : S, ENNReal.ofReal (Real.sqrt 2 ^ s) * dyadicPowerWeight s Q :=
      ENNReal.tsum_le_tsum fun Q ↦ (hausdorffContent_le_contentCost s _).trans
        (contentCost_dyadicCube_le hs Q.val.level Q.val.index)
    _ = _ := by rw [ENNReal.tsum_mul_left, tsum_subtype]; rfl

/-- Ordinary content is bounded by a fixed multiple of dyadic content. -/
theorem hausdorffContent_le_dyadicPowerContent {s : ℝ} (hs : 0 ≤ s)
    (E : Set (EuclideanSpace ℝ (Fin 2))) :
    hausdorffContent s E ≤ ENNReal.ofReal (Real.sqrt 2 ^ s) * dyadicPowerContent s E := by
  have hc : ENNReal.ofReal (Real.sqrt 2 ^ s) ≠ 0 := by positivity
  simp only [dyadicPowerContent, dyadicCoverContent,
    ENNReal.mul_iInf_of_ne hc ENNReal.ofReal_ne_top]
  exact le_iInf fun S ↦ le_iInf fun hS ↦ hausdorffContent_le_dyadicCoverCost hs hS

/-- A positive ordinary content forces positive dyadic content. -/
theorem dyadicPowerContent_pos_of_hausdorffContent_pos {s : ℝ} (hs : 0 ≤ s)
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : 0 < hausdorffContent s E) :
    0 < dyadicPowerContent s E := by
  by_contra h
  have hz : dyadicPowerContent s E = 0 := nonpos_iff_eq_zero.mp (not_lt.mp h)
  have hle := hausdorffContent_le_dyadicPowerContent hs E
  rw [hz, mul_zero] at hle
  exact hE.not_ge hle

/-- Cost of a finite family of cubes at one common generation. -/
theorem dyadicPowerCost_finset_level (s : ℝ) (F : Finset DyadicCell) (n : ℕ)
    (hlevel : ∀ Q ∈ F, Q.level = n) :
    dyadicCoverCost (dyadicPowerWeight s) (F : Set DyadicCell) =
      F.card * ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) * s)) := by
  rw [dyadicCoverCost_finset]
  calc
    _ = ∑ _Q ∈ F, ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) * s)) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      simp only [dyadicPowerWeight, hlevel Q hQ]
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- A dyadic-radius ball is covered by at most four squares at the corresponding generation. -/
theorem dyadicPowerContent_ball_dyadic_le (s : ℝ) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    dyadicPowerContent s (Metric.ball x (dyadicCoverRadius n)) ≤
      4 * ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ) * s)) := by
  classical
  let F : Finset DyadicCell := (neighboringCubeIndices n x).image (fun k ↦ ⟨n, k⟩)
  have hcover : Metric.ball x (dyadicCoverRadius n) ⊆ dyadicCoverUnion F := by
    intro y hy
    exact mem_iUnion₂.mpr ⟨⟨n, cubeIndex n y⟩,
      Finset.mem_image.mpr ⟨cubeIndex n y, cubeIndex_mem_neighboringCubeIndices hy, rfl⟩,
      mem_dyadicCube_cubeIndex n y⟩
  have hcard : F.card ≤ 4 :=
    Finset.card_image_le.trans (card_neighboringCubeIndices n x).le
  refine (dyadicCoverContent_le_cost _ hcover).trans ?_
  rw [dyadicPowerCost_finset_level s F n (by
    intro Q hQ
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hQ
    rfl)]
  exact mul_le_mul_left (by exact_mod_cast hcard) _

/-- A small arbitrary-radius ball has the expected power content bound. -/
theorem dyadicPowerContent_ball_le {s : ℝ} (hs : 0 ≤ s)
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    dyadicPowerContent s (Metric.ball x r) ≤ ENNReal.ofReal (4 * (4 * r) ^ s) := by
  obtain ⟨i, hilow, hiup⟩ := exists_dyadicRadius_bracket hr (by linarith)
  cases i with
  | zero =>
    have : (1 : ℝ) / 2 < r := by
      simpa only [Nat.zero_add, dyadicRadius, two_rpow_neg_natCast, pow_one] using hilow
    exact False.elim (this.not_ge hrhalf)
  | succ j =>
    have hrcover : r ≤ dyadicCoverRadius j := by
      rw [dyadicCoverRadius_eq_dyadicRadius_succ]
      exact hiup
    have hscale : dyadicRadius j < 4 * r := by
      rw [dyadicRadius_eq_four_mul_add_two]
      exact mul_lt_mul_of_pos_left hilow (by norm_num)
    have hallow : allowance j s ≤ (4 * r) ^ s := by
      rw [allowance_eq_dyadicRadius_rpow]
      exact Real.rpow_le_rpow (by unfold dyadicRadius; positivity) hscale.le hs
    refine (dyadicCoverContent_mono _ (Metric.ball_subset_ball hrcover)).trans
      ((dyadicPowerContent_ball_dyadic_le s j x).trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num only [ENNReal.ofReal_ofNat]
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hallow) _

/-- Positive-exponent dyadic content vanishes on every singleton. -/
theorem dyadicPowerContent_singleton {s : ℝ} (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin 2)) : dyadicPowerContent s {x} = 0 := by
  have hbound (n : ℕ) : dyadicPowerContent s {x} ≤
      ENNReal.ofReal (((2 : ℝ) ^ (-s)) ^ n) := by
    let Q : DyadicCell := ⟨n, cubeIndex n x⟩
    have hcover : {x} ⊆ dyadicCoverUnion {Q} := by
      intro y hy
      have : y = x := mem_singleton_iff.mp hy
      subst y
      exact mem_iUnion₂.mpr ⟨Q, rfl, mem_dyadicCube_cubeIndex n x⟩
    refine (dyadicCoverContent_le_cost _ hcover).trans_eq ?_
    have hcost : dyadicCoverCost (dyadicPowerWeight s) {Q} = dyadicPowerWeight s Q := by
      simpa using dyadicCoverCost_finset (dyadicPowerWeight s) {Q}
    rw [hcost]
    simp only [dyadicPowerWeight, Q]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ (2 : ℝ) ^ (-s))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))
  have ht' : Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal (((2 : ℝ) ^ (-s)) ^ n))
      Filter.atTop (nhds 0) := by simpa using ENNReal.tendsto_ofReal ht
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds ht'
    (Filter.Eventually.of_forall hbound)) zero_le

/-- Small-set dyadic content is bounded by a fixed multiple of diameter to the exponent. -/
theorem dyadicPowerContent_small_set_le {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : Metric.ediam A ≤ ENNReal.ofReal (1 / 4)) :
    dyadicPowerContent s A ≤ ENNReal.ofReal (4 * (8 : ℝ) ^ s) * Metric.ediam A ^ s := by
  rcases eq_empty_or_nonempty A with rfl | ⟨x, hx⟩
  · change dyadicCoverOuterMeasure (dyadicPowerWeight s) ∅ ≤ _
    simp
  by_cases hzero : Metric.ediam A = 0
  · have hsub : A ⊆ {x} := fun y hy ↦
      mem_singleton_iff.mpr ((Metric.ediam_eq_zero_iff.mp hzero) hy hx)
    exact (dyadicCoverContent_mono _ hsub).trans
      ((dyadicPowerContent_singleton hs x).le.trans zero_le)
  have hfinite : Metric.ediam A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hdiampos : 0 < Metric.diam A := ENNReal.toReal_pos hzero hfinite
  have hdiamle : Metric.diam A ≤ 1 / 4 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hA
  have hsub : A ⊆ Metric.ball x (2 * Metric.diam A) := by
    intro y hy
    exact (Metric.dist_le_diam_of_mem' hfinite hy hx).trans_lt (by linarith)
  refine (dyadicCoverContent_mono _ hsub).trans
    ((dyadicPowerContent_ball_le hs.le x (by positivity) (by linarith)).trans_eq ?_)
  rw [show 4 * (2 * Metric.diam A) = 8 * Metric.diam A by ring,
    Real.mul_rpow (by norm_num) hdiampos.le, ← mul_assoc,
    ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hdiampos.le hs.le]
  congr 2
  exact ENNReal.ofReal_toReal hfinite

/-- Dyadic content is bounded by a fixed multiple of Hausdorff measure. -/
theorem dyadicPowerContent_le_hausdorffMeasure {s : ℝ} (hs : 0 < s)
    (A : Set (EuclideanSpace ℝ (Fin 2))) :
    dyadicPowerContent s A ≤ ENNReal.ofReal (4 * (8 : ℝ) ^ s) * μH[s] A := by
  let c : ℝ≥0∞ := ENNReal.ofReal (4 * (8 : ℝ) ^ s)
  have hc : c ≠ 0 := by positivity
  have hle : dyadicCoverOuterMeasure (dyadicPowerWeight s) ≤
      OuterMeasure.mkMetric (fun r ↦ c * r ^ s) :=
    OuterMeasure.le_mkMetric _ _ (ENNReal.ofReal (1 / 4)) (by norm_num)
      (fun _ hA ↦ dyadicPowerContent_small_set_le hs hA)
  have hle' := hle.trans (OuterMeasure.mkMetric_mono_smul ENNReal.ofReal_ne_top hc
    (Filter.Eventually.of_forall fun _ ↦ le_rfl))
  simpa only [← Measure.mkMetric_toOuterMeasure, Measure.coe_toOuterMeasure,
    smul_apply, smul_eq_mul, Measure.hausdorffMeasure, dyadicPowerContent,
    dyadicCoverOuterMeasure, OuterMeasure.coe_mk] using hle' A

/-- Positive dyadic content forces Hausdorff dimension at least the exponent. -/
theorem le_dimH_of_dyadicPowerContent_pos {s : ℝ} (hs : 0 < s)
    {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : 0 < dyadicPowerContent s A) :
    ENNReal.ofReal s ≤ dimH A := by
  have hmeasure : μH[s] A ≠ 0 := by
    intro hz
    have hle := dyadicPowerContent_le_hausdorffMeasure hs A
    rw [hz, mul_zero] at hle
    exact hA.not_ge hle
  have hdim := le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨s, hs.le⟩) hmeasure
  rw [ENNReal.coe_nnreal_eq] at hdim
  exact hdim

/-- Every analytic planar set of dimension above `s > 1` contains a compact subset
whose dimension is still strictly above `s`. -/
theorem exists_isCompact_subset_lt_dimH_of_analyticSet
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : AnalyticSet E) {s : ℝ}
    (hs : 1 < s) (hdim : ENNReal.ofReal s < dimH E) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact K ∧ K ⊆ E ∧ ENNReal.ofReal s < dimH K := by
  obtain ⟨t, hst, htdim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hdim
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have ht : 1 < (t : ℝ) := hs.trans ((ENNReal.ofReal_lt_coe_iff hspos.le).mp hst)
  have htpos : 0 < (t : ℝ) := lt_trans zero_lt_one ht
  have hH : μH[(t : ℝ)] E = ∞ := hausdorffMeasure_of_lt_dimH htdim
  have hcontent : 0 < dyadicPowerContent (t : ℝ) E :=
    dyadicPowerContent_pos_of_hausdorffContent_pos htpos.le
      (hausdorffContent_pos htpos (by rw [hH]; exact ENNReal.top_ne_zero))
  obtain ⟨K, hK, hKE, hKpos⟩ :=
    exists_isCompact_subset_dyadicPowerContent_pos ht hE hcontent
  refine ⟨K, hK, hKE, hst.trans_le ?_⟩
  simpa only [ENNReal.coe_nnreal_eq] using le_dimH_of_dyadicPowerContent_pos htpos hKpos

/-- The compact dimension-extraction theorem for arbitrary Borel planar sets. -/
theorem exists_isCompact_subset_lt_dimH_of_measurableSet
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {s : ℝ}
    (hs : 1 < s) (hdim : ENNReal.ofReal s < dimH E) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)),
      IsCompact K ∧ K ⊆ E ∧ ENNReal.ofReal s < dimH K :=
  exists_isCompact_subset_lt_dimH_of_analyticSet hE.analyticSet hs hdim

/-- An arbitrary Borel planar set of dimension above `s > 1` carries a compactly supported
`s`-Frostman probability measure. No sigma-finiteness assumption is needed. -/
theorem exists_isFrostman_probabilityMeasure_of_measurableSet
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hE : MeasurableSet E) {s : ℝ}
    (hs : 1 < s) (hdim : ENNReal.ofReal s < dimH E) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2)))
      (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (C : ℝ),
      IsCompact K ∧ K ⊆ E ∧ μ ∈ probabilityMeasuresSupportedOn K ∧
      IsFrostman (μ : Measure _) s C := by
  obtain ⟨K, hK, hKE, hdimK⟩ :=
    exists_isCompact_subset_lt_dimH_of_measurableSet hE hs hdim
  obtain ⟨μ, C, hμK, hfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH
    hK (lt_trans zero_lt_one hs) hdimK
  exact ⟨K, μ, C, hK, hKE, hμK, hfr⟩

end FalconerPacking
