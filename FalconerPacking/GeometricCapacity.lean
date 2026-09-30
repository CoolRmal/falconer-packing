/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Capacity
import FalconerPacking.FrostmanLimit
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Capacities defined by compact families of Frostman measures

The supremum of the outer masses of a weakly compact family of finite measures is a Choquet
capacity. We apply this to Frostman probability measures on a fixed compact planar set.

This constructs an actual capacity, rather than assuming continuity of Hausdorff content.
It does not yet prove positivity of this capacity on arbitrary Borel sets whose Hausdorff
dimension exceeds the Frostman exponent. Such a positivity theorem is a separate obligation.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FalconerPacking

/-- The largest outer mass assigned by a family of finite measures. -/
def finiteMeasureCapacity {α : Type*} [MeasurableSpace α]
    (F : Set (FiniteMeasure α)) (A : Set α) : ℝ≥0∞ :=
  ⨆ μ ∈ F, (μ : Measure α) A

/-- Outer masses are monotone, including on sets that are not measurable. -/
theorem monotone_finiteMeasureCapacity {α : Type*} [MeasurableSpace α]
    (F : Set (FiniteMeasure α)) : Monotone (finiteMeasureCapacity F) := by
  intro A B hAB
  exact iSup_mono fun μ ↦ iSup_mono fun _ ↦ measure_mono hAB

/-- Continuity from below does not require measurability of the increasing sets. -/
theorem finiteMeasureCapacity_iUnion {α : Type*} [MeasurableSpace α]
    (F : Set (FiniteMeasure α)) (A : ℕ → Set α) (hA : Monotone A) :
    finiteMeasureCapacity F (⋃ n, A n) = ⨆ n, finiteMeasureCapacity F (A n) := by
  simp only [finiteMeasureCapacity, hA.measure_iUnion]
  apply le_antisymm
  · refine iSup_le fun μ ↦ iSup_le fun hμ ↦ iSup_le fun n ↦ ?_
    exact le_iSup_of_le n (le_iSup_of_le μ (le_iSup_of_le hμ le_rfl))
  · refine iSup_le fun n ↦ iSup_le fun μ ↦ iSup_le fun hμ ↦ ?_
    exact le_iSup_of_le μ (le_iSup_of_le hμ (le_iSup_of_le n le_rfl))

/-- Closed-set evaluation is upper semicontinuous for weak convergence of finite measures. -/
theorem upperSemicontinuous_finiteMeasure_closed
    {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {K : Set α} (hK : IsClosed K) :
    UpperSemicontinuous (fun μ : FiniteMeasure α ↦ (μ : Measure α) K) := by
  rw [upperSemicontinuous_iff_limsup_le]
  intro μ
  exact FiniteMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hK

/-- Compactness of the measure family allows one measure to meet all nested mass bounds. -/
theorem exists_finiteMeasure_iInter_mass_ge
    {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {F : Set (FiniteMeasure α)} (hF : IsCompact F) (K : ℕ → Set α)
    (hK : ∀ n, IsClosed (K n)) (hanti : Antitone K) {a : ℝ≥0∞}
    (ha : ∀ n, a < finiteMeasureCapacity F (K n)) :
    ∃ μ ∈ F, a ≤ (μ : Measure α) (⋂ n, K n) := by
  let T : ℕ → Set (FiniteMeasure α) := fun n ↦
    F ∩ {μ | a ≤ (μ : Measure α) (K n)}
  have hTc (n : ℕ) : IsClosed (T n) :=
    hF.isClosed.inter ((upperSemicontinuous_finiteMeasure_closed (hK n)).isClosed_preimage a)
  have hTne (n : ℕ) : (T n).Nonempty := by
    obtain ⟨μ, hμ⟩ := lt_iSup_iff.mp (ha n)
    obtain ⟨hμF, hmass⟩ := lt_iSup_iff.mp hμ
    exact ⟨μ, hμF, hmass.le⟩
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T
    (fun n μ hμ ↦ ⟨hμ.1, hμ.2.trans (measure_mono (hanti (Nat.le_succ n)))⟩)
    hTne (hF.of_isClosed_subset (hTc 0) inter_subset_left) hTc
  refine ⟨μ, (mem_iInter.mp hμ 0).1, ?_⟩
  rw [hanti.measure_iInter (fun n ↦ (hK n).measurableSet.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩]
  exact le_iInf fun n ↦ (mem_iInter.mp hμ n).2

/-- A weakly compact family of finite measures defines a Choquet capacity. -/
theorem isChoquetCapacity_finiteMeasureCapacity
    {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {F : Set (FiniteMeasure α)} (hF : IsCompact F) :
    IsChoquetCapacity (finiteMeasureCapacity F) where
  map_empty := by simp [finiteMeasureCapacity]
  monotone := monotone_finiteMeasureCapacity F
  map_iUnion := finiteMeasureCapacity_iUnion F
  map_iInter K hK hanti _ := by
    apply le_antisymm
    · exact le_iInf fun n ↦ monotone_finiteMeasureCapacity F (iInter_subset K n)
    · apply le_of_forall_lt_imp_le_of_dense
      intro a ha
      obtain ⟨μ, hμF, hμ⟩ := exists_finiteMeasure_iInter_mass_ge hF K
        (fun n ↦ (hK n).isClosed) hanti (fun n ↦ ha.trans_le (iInf_le _ n))
      apply hμ.trans
      exact le_iSup_of_le μ (le_iSup_of_le hμF le_rfl)

/-- Probability measures on a fixed set with one uniform Frostman constant. -/
def frostmanProbabilityMeasures (B : Set (EuclideanSpace ℝ (Fin 2))) (s C : ℝ) :
    Set (ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) :=
  {μ | μ ∈ probabilityMeasuresSupportedOn B ∧ IsFrostman (μ : Measure _) s C}

/-- An open-set mass bound is closed in the topology of weak convergence. -/
theorem isClosed_probabilityMeasure_open_mass_le
    {α : Type*} [MeasurableSpace α] [MetricSpace α] [BorelSpace α]
    {U : Set α} (hU : IsOpen U) (a : ℝ≥0∞) :
    IsClosed {μ : ProbabilityMeasure α | (μ : Measure α) U ≤ a} := by
  have h : LowerSemicontinuous (fun μ : ProbabilityMeasure α ↦ (μ : Measure α) U) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro μ
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hU
  exact h.isClosed_preimage a

/-- All the Frostman ball inequalities survive weak limits simultaneously. -/
theorem isClosed_probabilityMeasure_isFrostman (s C : ℝ) :
    IsClosed {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)) |
      IsFrostman (μ : Measure _) s C} := by
  simp only [IsFrostman, setOf_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun r ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun _ ↦ isClosed_probabilityMeasure_open_mass_le Metric.isOpen_ball _

/-- The fixed-constant Frostman family is weakly compact on a compact ambient set. -/
theorem isCompact_frostmanProbabilityMeasures
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : IsCompact B) (s C : ℝ) :
    IsCompact (frostmanProbabilityMeasures B s C) :=
  (isCompact_probabilityMeasuresSupportedOn hB).inter_right
    (isClosed_probabilityMeasure_isFrostman s C)

/-- A geometric capacity obtained from Frostman probabilities on a compact ambient set. -/
def frostmanCapacity (B : Set (EuclideanSpace ℝ (Fin 2))) (s C : ℝ) :
    Set (EuclideanSpace ℝ (Fin 2)) → ℝ≥0∞ :=
  finiteMeasureCapacity
    (ProbabilityMeasure.toFiniteMeasure '' frostmanProbabilityMeasures B s C)

/-- The geometric Frostman capacity satisfies every hypothesis of analytic compact extraction. -/
theorem isChoquetCapacity_frostmanCapacity
    {B : Set (EuclideanSpace ℝ (Fin 2))} (hB : IsCompact B) (s C : ℝ) :
    IsChoquetCapacity (frostmanCapacity B s C) :=
  isChoquetCapacity_finiteMeasureCapacity ((isCompact_frostmanProbabilityMeasures hB s C).image
    (ProbabilityMeasure.toFiniteMeasure_isEmbedding _).continuous)

/-- Positivity means that an actual Frostman probability assigns positive outer mass. -/
theorem frostmanCapacity_pos_iff
    (B A : Set (EuclideanSpace ℝ (Fin 2))) (s C : ℝ) :
    0 < frostmanCapacity B s C A ↔
      ∃ μ ∈ frostmanProbabilityMeasures B s C, 0 < (μ : Measure _) A := by
  simp only [frostmanCapacity, finiteMeasureCapacity, lt_iSup_iff, mem_image]
  constructor
  · rintro ⟨ν, ⟨μ, hμ, rfl⟩, hpos⟩
    exact ⟨μ, hμ, hpos⟩
  · rintro ⟨μ, hμ, hpos⟩
    exact ⟨μ.toFiniteMeasure, ⟨μ, hμ, rfl⟩, hpos⟩

/-- A positive value on an analytic set is retained on a compact subset, with the same
Frostman exponent and constant in the witnessing ambient probability measure. -/
theorem exists_isCompact_subset_frostman_mass_pos_of_capacity_pos
    {B A : Set (EuclideanSpace ℝ (Fin 2))} (hB : IsCompact B) (hA : AnalyticSet A)
    {s C : ℝ} (hpos : 0 < frostmanCapacity B s C A) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2)))
      (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))),
      IsCompact K ∧ K ⊆ A ∧ μ ∈ frostmanProbabilityMeasures B s C ∧
        0 < (μ : Measure _) K := by
  obtain ⟨K, hK, hKA, hcap⟩ :=
    (isChoquetCapacity_frostmanCapacity hB s C).exists_isCompact_subset_of_analyticSet hA hpos
  obtain ⟨μ, hμ, hμK⟩ := (frostmanCapacity_pos_iff B K s C).mp hcap
  exact ⟨K, μ, hK, hKA, hμ, hμK⟩

/-- The existing compact Frostman theorem gives positive capacity, with some finite
Frostman constant, on compact sets above the exponent. -/
theorem exists_frostmanCapacity_pos_of_isCompact
    {B K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hKB : K ⊆ B)
    {s : ℝ} (hs : 0 < s) (hdim : ENNReal.ofReal s < dimH K) :
    ∃ C : ℝ, 0 < frostmanCapacity B s C K := by
  obtain ⟨μ, C, hμK, hfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH hK hs hdim
  have hμB : μ ∈ probabilityMeasuresSupportedOn B := by
    change (μ : Measure _) Bᶜ = 0
    exact measure_mono_null (compl_subset_compl.mpr hKB) hμK
  have hmass : (μ : Measure _) K = 1 := by
    have hcompl : (μ : Measure _) Kᶜ = 0 := hμK
    have hsum := measure_add_measure_compl (μ := (μ : Measure _)) hK.measurableSet
    simpa only [hcompl, add_zero, measure_univ] using hsum
  refine ⟨C, (frostmanCapacity_pos_iff B K s C).mpr ⟨μ, ⟨hμB, hfr⟩, ?_⟩⟩
  rw [hmass]
  exact zero_lt_one

/-- A small set is contained in a ball of twice its diameter; the zero-diameter case is null
because positive-exponent Frostman measures have no atoms. -/
theorem isFrostman_small_set_mass_le
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    (hfr : IsFrostman μ s C) {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA : Metric.ediam A ≤ ENNReal.ofReal (1 / 2)) :
    μ A ≤ ENNReal.ofReal (C * 2 ^ s) * Metric.ediam A ^ s := by
  rcases eq_empty_or_nonempty A with rfl | ⟨x, hx⟩
  · simp
  by_cases hzero : Metric.ediam A = 0
  · have hsub : A ⊆ {x} := fun y hy ↦
      Set.mem_singleton_iff.mpr ((Metric.ediam_eq_zero_iff.mp hzero) hy hx)
    rw [measure_mono_null hsub (measure_singleton_eq_zero_of_isFrostman hs hfr x)]
    exact bot_le
  have hfinite : Metric.ediam A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hdiampos : 0 < Metric.diam A := ENNReal.toReal_pos hzero hfinite
  have hdiamle : Metric.diam A ≤ 1 / 2 := ENNReal.toReal_le_of_le_ofReal (by norm_num) hA
  have hsub : A ⊆ Metric.ball x (2 * Metric.diam A) := by
    intro y hy
    exact (Metric.dist_le_diam_of_mem' hfinite hy hx).trans_lt (by linarith)
  refine (measure_mono hsub).trans ((hfr x _ (by positivity) (by linarith)).trans_eq ?_)
  rw [Real.mul_rpow (by norm_num) hdiampos.le]
  rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hC (Real.rpow_nonneg (by norm_num) s)),
    ← ENNReal.ofReal_rpow_of_nonneg hdiampos.le hs.le]
  congr 2
  exact ENNReal.ofReal_toReal hfinite

/-- The mass-distribution estimate: a Frostman measure is bounded by a finite multiple of
Hausdorff measure of the same exponent. -/
theorem isFrostman_le_smul_hausdorffMeasure
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ} (hs : 0 < s) (hC : 0 < C)
    (hfr : IsFrostman μ s C) :
    μ ≤ ENNReal.ofReal (C * 2 ^ s) • μH[s] := by
  let c : ℝ≥0∞ := ENNReal.ofReal (C * 2 ^ s)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (mul_pos hC (Real.rpow_pos_of_pos (by norm_num) s))
  have hle : μ ≤ Measure.mkMetric (fun r ↦ c * r ^ s) :=
    Measure.le_mkMetric _ μ (ENNReal.ofReal (1 / 2)) (by norm_num)
      (fun _ hA ↦ isFrostman_small_set_mass_le hs hC.le hfr hA)
  exact hle.trans (Measure.mkMetric_mono_smul ENNReal.ofReal_ne_top hc
    (Eventually.of_forall fun _ ↦ le_rfl))

/-- The mass-distribution principle applies to positive outer mass, without assuming the set
is measurable. The Frostman constant may have either sign. -/
theorem le_dimH_of_isFrostman_measure_pos
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ} (hs : 0 < s)
    (hfr : IsFrostman μ s C) {A : Set (EuclideanSpace ℝ (Fin 2))} (hA : 0 < μ A) :
    ENNReal.ofReal s ≤ dimH A := by
  have hfr' : IsFrostman μ s (max C 1) := by
    intro x r hr hr1
    exact (hfr x r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hr.le s)))
  have hac : μ ≪ μH[s] := Measure.absolutelyContinuous_of_le_smul
    (isFrostman_le_smul_hausdorffMeasure hs (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hfr')
  have hH : μH[s] A ≠ 0 := fun hzero ↦ hA.ne' (hac hzero)
  rw [ENNReal.ofReal_eq_coe_nnreal hs.le]
  exact le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨s, hs.le⟩) hH

/-- Positive geometric capacity yields a compact subset with at least the Frostman dimension.
Applying this at an intermediate exponent larger than a desired exponent gives strict dimension. -/
theorem exists_isCompact_subset_le_dimH_of_frostmanCapacity_pos
    {B A : Set (EuclideanSpace ℝ (Fin 2))} (hB : IsCompact B) (hA : AnalyticSet A)
    {s C : ℝ} (hs : 0 < s) (hpos : 0 < frostmanCapacity B s C A) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)), IsCompact K ∧ K ⊆ A ∧
      ENNReal.ofReal s ≤ dimH K := by
  obtain ⟨K, μ, hK, hKA, hμ, hμK⟩ :=
    exists_isCompact_subset_frostman_mass_pos_of_capacity_pos hB hA hpos
  exact ⟨K, hK, hKA, le_dimH_of_isFrostman_measure_pos hs hμ.2 hμK⟩

end FalconerPacking
