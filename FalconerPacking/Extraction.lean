/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Restriction

/-!
# Extracting a piece of controlled box dimension

The selection step of Proposition 2.5 and of module 15: *the countable-cover characterization of
packing dimension gives a cover by bounded sets of upper box dimension at most `u₀`.  At least
one member has positive mass.*

`exists_bounded_piece_of_measure_pos` is that statement, and
`exists_isCompact_subset_of_measure_pos` refines it to a compact subset of positive mass by inner
regularity, as the manuscript does immediately afterwards.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Unfolding the infimum in `packingDim`: below any strict upper bound there is an actual
bounded countable cover whose pieces all have upper box dimension below that bound. -/
theorem exists_cover_of_packingDim_lt {E : Set Plane} {c : ℝ≥0∞} (h : packingDim E < c) :
    ∃ K : ℕ → Set Plane, E ⊆ ⋃ n, K n ∧ (∀ n, Bornology.IsBounded (K n)) ∧
      ∀ n, upperBoxDim (K n) < c := by
  rw [packingDim, iInf_lt_iff] at h
  obtain ⟨K, hK⟩ := h
  rw [iInf_lt_iff] at hK
  obtain ⟨hcov, hK⟩ := hK
  rw [iInf_lt_iff] at hK
  obtain ⟨hbdd, hlt⟩ := hK
  exact ⟨K, hcov, hbdd,
    fun n ↦ lt_of_le_of_lt (le_iSup (fun m ↦ upperBoxDim (K m)) n) hlt⟩

/-- **The selection step.**  If `E` carries positive mass and its packing dimension is below `c`,
some bounded piece of upper box dimension below `c` already carries positive mass. -/
theorem exists_bounded_piece_of_measure_pos {μ : Measure Plane} {E : Set Plane} {c : ℝ≥0∞}
    (hpack : packingDim E < c) (hμ : 0 < μ E) :
    ∃ K : Set Plane, Bornology.IsBounded K ∧ upperBoxDim K < c ∧ 0 < μ (K ∩ E) := by
  obtain ⟨K, hcov, hbdd, hlt⟩ := exists_cover_of_packingDim_lt hpack
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_lt] at hcon
  have hzero : ∀ n, μ (K n ∩ E) = 0 := by
    intro n
    have := hcon (K n) (hbdd n) (hlt n)
    exact nonpos_iff_eq_zero.1 this
  have hEsub : E ⊆ ⋃ n, K n ∩ E := by
    intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hx)
    exact mem_iUnion.2 ⟨n, hn, hx⟩
  have : μ E = 0 := by
    refine nonpos_iff_eq_zero.1 ((measure_mono hEsub).trans ?_)
    exact le_of_eq (measure_iUnion_null hzero)
  exact absurd this hμ.ne'

/-- **Inner regularity after selection.**  A piece of positive mass contains a compact subset of
positive mass, which is what the manuscript restricts its Frostman measure to. -/
theorem exists_isCompact_subset_of_measure_pos {μ : Measure Plane} [IsFiniteMeasure μ]
    [μ.InnerRegularCompactLTTop] {A : Set Plane} (hA : MeasurableSet A) (hμ : 0 < μ A) :
    ∃ L : Set Plane, IsCompact L ∧ L ⊆ A ∧ 0 < μ L := by
  obtain ⟨L, hLA, hLcomp, hL⟩ :=
    hA.exists_lt_isCompact_of_ne_top (μ := μ) (measure_ne_top μ A) hμ
  exact ⟨L, hLcomp, hLA, hL⟩

section Separation

variable {μ : Measure Plane}

/-- Some point of a set of positive mass charges every ball around it. -/
theorem exists_mem_forall_measure_ball_pos {K : Set Plane} (hμK : 0 < μ K) :
    ∃ x ∈ K, ∀ ε > 0, 0 < μ (K ∩ Metric.ball x ε) := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_and, not_forall, not_lt, nonpos_iff_eq_zero] at hcon
  have hnull : μ K = 0 := by
    refine measure_null_of_locally_null K fun x hx ↦ ?_
    obtain ⟨ε, hε, hzero⟩ := hcon x hx
    refine ⟨K ∩ Metric.ball x ε, ?_, hzero⟩
    refine mem_nhdsWithin.2 ⟨Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
    intro y hy
    exact ⟨hy.2, hy.1⟩
  exact absurd hnull hμK.ne'

/-- **The separation step.**  A compact set of positive mass for a Frostman measure splits into
two compact subsets of positive mass at positive distance from each other. -/
theorem exists_separated_compacts {s C : ℝ} (hs : 0 < s) (hfr : IsFrostman μ s C)
    {K : Set Plane} (hK : IsCompact K) (hμK : 0 < μ K) :
    ∃ (K₁ K₂ : Set Plane) (d : ℝ), IsCompact K₁ ∧ IsCompact K₂ ∧ K₁ ⊆ K ∧ K₂ ⊆ K ∧
      0 < μ K₁ ∧ 0 < μ K₂ ∧ 0 < d ∧ ∀ y ∈ K₁, ∀ z ∈ K₂, d ≤ dist y z := by
  obtain ⟨x, hxK, hx⟩ := exists_mem_forall_measure_ball_pos hμK
  have hatom : μ {x} = 0 := measure_singleton_eq_zero_of_isFrostman hs hfr x
  have hdiff : 0 < μ (K \ {x}) := by
    have : μ (K \ {x}) = μ K := measure_diff_null hatom
    rw [this]
    exact hμK
  have hcover : K \ {x} ⊆ ⋃ n : ℕ, K \ Metric.ball x (1 / (n + 1)) := by
    intro y hy
    have hne : dist y x ≠ 0 := fun h ↦ hy.2 (by simpa using dist_eq_zero.1 h)
    have hpos : 0 < dist y x := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact mem_iUnion.2 ⟨n, hy.1, fun hmem ↦ absurd (Metric.mem_ball.1 hmem) (not_lt.2 hn.le)⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < μ (K \ Metric.ball x (1 / (n + 1))) := by
    by_contra hcon
    rw [not_exists] at hcon
    simp only [not_lt, nonpos_iff_eq_zero] at hcon
    exact absurd ((measure_mono hcover).trans (le_of_eq (measure_iUnion_null hcon)))
      (not_le.2 hdiff)
  set r : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hr
  have hrpos : 0 < r := by positivity
  have htwo : 2 * r = 1 / ((n : ℝ) + 1) := by
    rw [hr]
    field_simp
  refine ⟨K ∩ Metric.closedBall x r, K \ Metric.ball x (1 / ((n : ℝ) + 1)), r,
    hK.inter_right Metric.isClosed_closedBall,
    hK.diff Metric.isOpen_ball, inter_subset_left, diff_subset, ?_, hn, hrpos, ?_⟩
  · exact lt_of_lt_of_le (hx r hrpos)
      (measure_mono (inter_subset_inter_right _ Metric.ball_subset_closedBall))
  · intro y hy z hz
    have hy' : dist y x ≤ r := Metric.mem_closedBall.1 hy.2
    have hz' : 1 / ((n : ℝ) + 1) ≤ dist z x :=
      not_lt.1 fun hlt ↦ hz.2 (Metric.mem_ball.2 hlt)
    have htri : dist z x ≤ dist z y + dist y x := dist_triangle z y x
    have hzy : dist z y = dist y z := dist_comm z y
    linarith [htwo, hy', hz', htri, hzy]

end Separation

end FalconerPacking
