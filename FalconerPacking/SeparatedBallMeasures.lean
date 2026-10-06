/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.Extraction
public import FalconerPacking.SeparatedBallGeometry

/-!
# Positive compact pieces in a separated coordinate chart

Restricting to small closed balls around mass-support points gives positive compact
pieces. A single explicit isometry then supplies the coordinate gap used in angular
strip deletion. Normalization changes the Frostman constant by exactly the reciprocal
mass, and the isometry preserves that constant and polynomial covering bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Euclidean isometries preserve Frostman estimates with the same constant. -/
theorem IsFrostman.map_isometryEquiv
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C : ℝ} (hμ : IsFrostman μ s C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) :
    IsFrostman (μ.map e) s C := by
  intro x r hr hr1
  rw [Measure.map_apply e.continuous.measurable Metric.isOpen_ball.measurableSet,
    e.preimage_ball]
  exact hμ (e.symm x) r hr hr1

/-- Isometries preserve the actual dyadic-radius covering bound. -/
theorem HasUpperBoxBound.image_isometryEquiv
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u : ℝ} (hK : HasUpperBoxBound K u)
    (e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) :
    HasUpperBoxBound (e '' K) u := by
  classical
  obtain ⟨C, hC, hcover⟩ := hK
  refine ⟨C, hC, fun n ↦ ?_⟩
  obtain ⟨P, hP, hcard⟩ := hcover n
  refine ⟨P.image e, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (hP hx)
    exact mem_iUnion₂.mpr ⟨e z, Finset.mem_image.mpr ⟨z, hz, rfl⟩,
      by simpa only [Metric.mem_ball, e.dist_eq] using hxz⟩
  · exact (Nat.cast_le.mpr Finset.card_image_le).trans hcard

/-- The common coordinate change leaves every pinned distance set unchanged. -/
theorem pinnedDistances_image_isometryEquiv
    (K : Set (EuclideanSpace ℝ (Fin 2))) (y : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) :
    pinnedDistances (e '' K) (e y) = pinnedDistances K y := by
  ext t
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, ht⟩
    exact ⟨x, hx, by simpa only [e.dist_eq] using ht⟩
  · rintro ⟨x, hx, ht⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, by simpa only [e.dist_eq] using ht⟩

/-- Every positive compact set has a point around which all small closed-ball
restrictions remain compact and have positive mass. -/
theorem exists_compact_positive_ball_pieces
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {K : Set (EuclideanSpace ℝ (Fin 2))}
    (hK : IsCompact K) (hμK : 0 < μ K) :
    ∃ a ∈ K, ∀ r > 0,
      IsCompact (K ∩ Metric.closedBall a r) ∧ 0 < μ (K ∩ Metric.closedBall a r) := by
  obtain ⟨a, ha, hballs⟩ := exists_mem_forall_measure_ball_pos hμK
  refine ⟨a, ha, fun r hr ↦ ⟨hK.inter_right Metric.isClosed_closedBall, ?_⟩⟩
  exact (hballs r hr).trans_le (measure_mono (inter_subset_inter_right _ Metric.ball_subset_closedBall))

/-- The normalized restriction, after an isometry, is an actual probability concentrated
on the compact image and obeys the normalized original Frostman bound. -/
theorem normalizedRestrict_map_isometry_data
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s C : ℝ}
    (hK : IsCompact K) (hμK : 0 < μ K) (hfr : IsFrostman μ s C)
    (e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) :
    IsProbabilityMeasure ((normalizedRestrict μ K).map e) ∧
      ((normalizedRestrict μ K).map e) (e '' K)ᶜ = 0 ∧
      IsFrostman ((normalizedRestrict μ K).map e) s (C / (μ K).toReal) := by
  letI := isProbabilityMeasure_normalizedRestrict hK.measurableSet hμK.ne'
    (measure_ne_top μ K)
  refine ⟨inferInstance, ?_,
    (isFrostman_normalizedRestrict hfr hμK.ne' (measure_ne_top μ K)).map_isometryEquiv e⟩
  rw [Measure.map_apply e.continuous.measurable (hK.image e.continuous).measurableSet.compl]
  have he : e ⁻¹' (e '' K)ᶜ = Kᶜ := by
    rw [preimage_compl, Set.preimage_image_eq K e.injective]
  rw [he, normalizedRestrict_apply μ K Kᶜ hK.measurableSet.compl]
  simp

/-- Positive separated compact source and pin sets have positive compact subpieces
inside two balls whose common coordinate chart has a strictly positive horizontal gap. -/
theorem exists_positive_compacts_in_separated_chart
    {μ ν : Measure (EuclideanSpace ℝ (Fin 2))}
    {K L : Set (EuclideanSpace ℝ (Fin 2))} {δ₀ : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hμK : 0 < μ K) (hνL : 0 < ν L)
    (hδ₀ : 0 < δ₀) (hsep : ∀ x ∈ K, ∀ y ∈ L, δ₀ ≤ dist x y) :
    ∃ (A B : Set (EuclideanSpace ℝ (Fin 2)))
      (e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) (δ R : ℝ),
      IsCompact A ∧ IsCompact B ∧ A ⊆ K ∧ B ⊆ L ∧ 0 < μ A ∧ 0 < ν B ∧
      0 < δ ∧ 0 < R ∧
      (∀ x ∈ e '' A, ‖x‖ ≤ R) ∧ (∀ y ∈ e '' B, ‖y‖ ≤ R) ∧
      (∀ x ∈ e '' A, ∀ y ∈ e '' B, δ ≤ (y - x) 0) := by
  obtain ⟨a, haK, ha⟩ := exists_compact_positive_ball_pieces hK hμK
  obtain ⟨b, hbL, hb⟩ := exists_compact_positive_ball_pieces hL hνL
  have hd : 0 < dist a b := hδ₀.trans_le (hsep a haK b hbL)
  have hr : 0 < dist a b / 8 := by positivity
  let A := K ∩ Metric.closedBall a (dist a b / 8)
  let B := L ∩ Metric.closedBall b (dist a b / 8)
  let e := centerAlignment a b
  have hA := ha (dist a b / 8) hr
  have hB := hb (dist a b / 8) hr
  refine ⟨A, B, e, dist a b / 2, 2 * dist a b,
    hA.1, hB.1, inter_subset_left, inter_subset_left, hA.2, hB.2,
    by positivity, by positivity, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (centerAlignment_small_balls le_rfl hx.2
      (Metric.mem_closedBall_self hr.le)).2.1
  · rintro _ ⟨y, hy, rfl⟩
    exact (centerAlignment_small_balls le_rfl
      (Metric.mem_closedBall_self hr.le) hy.2).2.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (centerAlignment_small_balls le_rfl hx.2 hy.2).1

end FalconerPacking
