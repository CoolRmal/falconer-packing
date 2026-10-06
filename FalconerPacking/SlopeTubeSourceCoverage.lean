/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SlopeTubeCoverage
public import FalconerPacking.EnlargedSlopeTubeDeletion

/-!
# A common finite label for tested pin tubes and their source pairs

The containing slope-grid member carries a quantitative normal comparison. This puts each
associated source point in the source strip with the same label, without counting finer caps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The normalized slope normal inherits the grid approximation of the original unit normal. -/
theorem abs_inner_slopeUnitNormal_le_of_approx
    (c : Bool) (k : ℤ) (M : ℕ) (e : EuclideanSpace ℝ (Fin 2))
    (happrox : ∀ z : EuclideanSpace ℝ (Fin 2),
      |slopeLinearCoordinate c ((k : ℝ) / M) z| ≤ 2 * |⟪e, z⟫| + ‖z‖ / M)
    (z : EuclideanSpace ℝ (Fin 2)) :
    |⟪slopeUnitNormal c ((k : ℝ) / M), z⟫| ≤ 2 * |⟪e, z⟫| + ‖z‖ / M := by
  rw [inner_slopeUnitNormal, abs_div, abs_of_nonneg (norm_nonneg _)]
  exact (div_le_self (abs_nonneg _) (one_le_norm_slopeNormalVector _ _)).trans (happrox z)

/-- The source point of a nearby-direction pair belongs to the source strip of the same label. -/
theorem mem_sourceSlopeTube_of_pair
    {X : Set (EuclideanSpace ℝ (Fin 2))} (o e : EuclideanSpace ℝ (Fin 2))
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) (L : ℕ)
    (i : Bool × (ℤ × ℤ))
    (happrox : ∀ z : EuclideanSpace ℝ (Fin 2),
      |slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) z| ≤ 2 * |⟪e, z⟫| + ‖z‖ / M)
    {x y : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ X)
    (hy : y ∈ enlargedSlopeTube o b M L i) {ε D : ℝ}
    (hpair : |⟪e, x - y⟫| ≤ ε) (hD : ‖x - y‖ ≤ D) :
    x ∈ sourceSlopeTube X o b ((L + 1) * (b / M) + 2 * ε + D / M) M i := by
  refine ⟨hx, ?_⟩
  change |⟪slopeUnitNormal i.1 ((i.2.1 : ℝ) / M), x - slopeTubeCenter o b M i⟫| ≤ _
  have hpin := enlargedSlopeTube_unit_normal_bound hb hM hy
  have hdelta := abs_inner_slopeUnitNormal_le_of_approx i.1 i.2.1 M e happrox (x - y)
  have hbound : |⟪slopeUnitNormal i.1 ((i.2.1 : ℝ) / M), x - y⟫| ≤
      2 * ε + D / M := hdelta.trans
        (add_le_add (mul_le_mul_of_nonneg_left hpair (by norm_num))
          (div_le_div_of_nonneg_right hD (Nat.cast_nonneg M)))
  have he : x - slopeTubeCenter o b M i = (y - slopeTubeCenter o b M i) + (x - y) := by abel
  rw [he, inner_add_right]
  exact (abs_add_le _ _).trans (by linarith)

/-- An arbitrary tested strip and all its associated pairs have one concrete grid label. -/
theorem exists_slopeTube_cover_with_source_pairs
    (X : Set (EuclideanSpace ℝ (Fin 2))) (o p e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1)
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M)
    {w C ε D : ℝ} (hw : w ≤ C * (b / M))
    (hne : (Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w}).Nonempty) :
    let L := Nat.ceil (4 * C + 2) + 1
    ∃ i ∈ slopeTubeLabels M,
      Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w} ⊆ enlargedSlopeTube o b M L i ∧
      ∀ y ∈ Metric.ball o b ∩ {x | |⟪e, x - p⟫| ≤ w}, ∀ x ∈ X,
        |⟪e, x - y⟫| ≤ ε → ‖x - y‖ ≤ D →
        x ∈ sourceSlopeTube X o b ((L + 1) * (b / M) + 2 * ε + D / M) M i := by
  obtain ⟨i, hi, hsub, hnormal⟩ :=
    exists_enlargedSlopeTube_containing_strip_with_normal o p e he hb hM hw hne
  refine ⟨i, hi, hsub, fun y hy x hx hpair hD ↦ ?_⟩
  exact mem_sourceSlopeTube_of_pair o e hb hM _ i hnormal hx (hsub hy) hpair hD

end FalconerPacking
