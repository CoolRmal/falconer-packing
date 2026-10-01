/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.EnlargedSlopeTubes
import FalconerPacking.SlopeNormalChart

/-!
# Geometric coverage by actual enlarged slope tubes

A uniformly bounded number of neighboring offsets covers every tube of comparable width,
in any direction. The containing tube is one member of the constructed finite family.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Nearby normal coordinates belong to the actual enlarged strip around a fixed label. -/
theorem mem_enlargedSlopeTube_of_normal_near
    {o x x₀ : EuclideanSpace ℝ (Fin 2)} {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) {c : Bool} {k l : ℤ} (hk : k ∈ slopeNet M)
    (hx₀ : x₀ ∈ slopeStrip o b M c (k, l)) (hx : x ∈ Metric.ball o b)
    (L : ℕ)
    (hnear : |slopeLinearCoordinate c ((k : ℝ) / M) (x - x₀)| ≤ L * (b / M)) :
    x ∈ enlargedSlopeTube o b M (L + 1) (c, k, l) := by
  have ha : 0 < b / M := div_pos hb (by exact_mod_cast hM)
  obtain ⟨l', hl', hx'⟩ := exists_slopeStrip_cover hb hM c hk hx
  have he : slopeLinearCoordinate c ((k : ℝ) / M) (x - x₀) =
      slopeLinearCoordinate c ((k : ℝ) / M) (x - o) -
        slopeLinearCoordinate c ((k : ℝ) / M) (x₀ - o) := by
    simp only [slopeLinearCoordinate_sub]
    ring
  rw [he, abs_le] at hnear
  have hd : |(l : ℝ) - l'| ≤ (L : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [hx₀.2.1, hx₀.2.2, hx'.2.1, hx'.2.2]
  have hi : |l - l'| ≤ ((L + 1 : ℕ) : ℤ) := by exact_mod_cast hd
  apply mem_iUnion₂.mpr
  refine ⟨(c, k, l'), Finset.mem_filter.mpr ⟨?_, rfl, rfl, hi⟩, hx'⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_univ c, hl'⟩

/-- Enlarged tubes stay inside a controlled physical normal strip. -/
theorem enlargedSlopeTube_normal_bound
    {o x : EuclideanSpace ℝ (Fin 2)} {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) {L : ℕ} {i : Bool × (ℤ × ℤ)}
    (hx : x ∈ enlargedSlopeTube o b M L i) :
    x ∈ Metric.ball o b ∧
      |slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) (x - o) -
        (i.2.2 : ℝ) * (b / M)| ≤ (L + 1) * (b / M) := by
  obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨_, hc, hk, hd⟩ := Finset.mem_filter.mp hj
  have ha : 0 < b / M := div_pos hb (by exact_mod_cast hM)
  have hbase : |slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) (x - o) -
      (j.2.2 : ℝ) * (b / M)| ≤ b / M := by
    rw [hc, hk, abs_le]
    constructor <;> linarith [hx.2.1, hx.2.2]
  have hd' : |(j.2.2 : ℝ) - i.2.2| ≤ L := by
    have hr : |(i.2.2 : ℝ) - j.2.2| ≤ L := by exact_mod_cast hd
    rwa [abs_sub_comm]
  refine ⟨hx.1, ?_⟩
  have he : slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) (x - o) -
      (i.2.2 : ℝ) * (b / M) =
      (slopeLinearCoordinate i.1 ((i.2.1 : ℝ) / M) (x - o) -
        (j.2.2 : ℝ) * (b / M)) + ((j.2.2 : ℝ) - i.2.2) * (b / M) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_pos ha]
  nlinarith

end FalconerPacking
