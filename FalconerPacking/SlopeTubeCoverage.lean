/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.EnlargedSlopeTubeGeometry

/-!
# A finite containing tube for every physical tube direction

The explicit slope grid and finite offset enlargements cover arbitrary unit-normal tubes.
The conclusion selects one actual finite-family member, so taking unions over finer cap
choices never incurs their number.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Every nonempty physical strip in the parent ball is contained in one finite-grid tube. -/
theorem exists_enlargedSlopeTube_containing_strip_with_normal
    (o p e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M)
    {w C : ℝ} (hw : w ≤ C * (b / M))
    (hne : (Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w}).Nonempty) :
    ∃ i ∈ slopeTubeLabels M,
      Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w} ⊆
        enlargedSlopeTube o b M (Nat.ceil (4 * C + 2) + 1) i ∧
      ∀ z : EuclideanSpace ℝ (Fin 2),
        |slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) z| ≤
          2 * |⟪e, z⟫| + ‖z‖ / M := by
  have ha : 0 < b / M := div_pos hb (by exact_mod_cast hM)
  obtain ⟨x₀, hx₀ball, hx₀strip⟩ := hne
  obtain ⟨c, k, hk, hnet⟩ := exists_slopeNet_unit_normal_bound hM e he
  obtain ⟨l, hl, hx₀⟩ := exists_slopeStrip_cover hb hM c hk hx₀ball
  refine ⟨(c, k, l), Finset.mem_product.mpr ⟨Finset.mem_univ c, hl⟩, ?_, hnet⟩
  rintro x ⟨hxball, hxstrip⟩
  change |⟪e, x - p⟫| ≤ w at hxstrip
  change |⟪e, x₀ - p⟫| ≤ w at hx₀strip
  apply mem_enlargedSlopeTube_of_normal_near hb hM hk hx₀ hxball
  have hinner : |⟪e, x - x₀⟫| ≤ 2 * w := by
    have hid : x - x₀ = (x - p) - (x₀ - p) := by abel
    rw [hid, inner_sub_right]
    exact (abs_sub _ _).trans (by linarith)
  have hnorm : ‖x - x₀‖ ≤ 2 * b := by
    have ht := dist_triangle x o x₀
    rw [dist_comm o x₀] at ht
    rw [← dist_eq_norm]
    linarith [Metric.mem_ball.mp hxball, Metric.mem_ball.mp hx₀ball]
  have hMreal : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  calc
    _ ≤ 2 * |⟪e, x - x₀⟫| + ‖x - x₀‖ / M := hnet _
    _ ≤ 4 * w + 2 * b / M :=
      add_le_add (by linarith) (div_le_div_of_nonneg_right hnorm hMreal)
    _ ≤ 4 * (C * (b / M)) + 2 * b / M := by gcongr
    _ = (4 * C + 2) * (b / M) := by ring
    _ ≤ (Nat.ceil (4 * C + 2) : ℝ) * (b / M) :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil _) ha.le

/-- The containing member is a single tube in the concrete finite family. -/
theorem exists_enlargedSlopeTube_containing_unit_strip
    (o p e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M)
    {w C : ℝ} (hw : w ≤ C * (b / M))
    (hne : (Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w}).Nonempty) :
    ∃ i ∈ slopeTubeLabels M,
      Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w} ⊆
        enlargedSlopeTube o b M (Nat.ceil (4 * C + 2) + 1) i := by
  obtain ⟨i, hi, hsub, _⟩ :=
    exists_enlargedSlopeTube_containing_strip_with_normal o p e he hb hM hw hne
  exact ⟨i, hi, hsub⟩

/-- A heavy strip in an arbitrary direction forces a heavy member of the finite family. -/
theorem exists_heavy_enlargedSlopeTube_of_heavy_unit_strip
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (o p e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M)
    {w C : ℝ} (hw : w ≤ C * (b / M)) {A : ℝ≥0∞}
    (hheavy : A < μ (Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w})) :
    ∃ i ∈ slopeTubeLabels M,
      A < μ (enlargedSlopeTube o b M (Nat.ceil (4 * C + 2) + 1) i) ∧
      Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w} ⊆
        enlargedSlopeTube o b M (Nat.ceil (4 * C + 2) + 1) i := by
  have hne : (Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w}).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.mp h, measure_empty] at hheavy
    exact (not_lt_zero hheavy)
  obtain ⟨i, hi, hsub⟩ := exists_enlargedSlopeTube_containing_unit_strip o p e he hb hM hw hne
  exact ⟨i, hi, hheavy.trans_le (measure_mono hsub), hsub⟩

end FalconerPacking
