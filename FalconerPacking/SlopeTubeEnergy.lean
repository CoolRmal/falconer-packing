/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SlopeStripGeometry

/-!
# The truncated energy bound for a concrete two-chart tube family

Every tube and angular label is explicitly defined. The pair-count bound is derived from
the slope geometry and includes coincident pairs, rather than assuming nonatomic measures.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

theorem tubePairCount_slopeStrip_eq_zero_of_not_mem_ball
    (o x y : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (M : ℕ) (c : Bool)
    (h : x ∉ Metric.ball o b ∨ y ∉ Metric.ball o b) :
    tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y = 0 := by
  classical
  unfold tubePairCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro kl _ hkl
  rcases h with hx | hy
  · exact hx hkl.1.1
  · exact hy hkl.2.1

/-- Each slope chart has the exact scale of the truncated inverse-distance kernel. -/
theorem tubePairCount_slopeStrip_le_truncKernel
    (o x y : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) (c : Bool) :
    (tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y : ℝ≥0∞) ≤
      10 * truncKernel (b / M) b x y := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hratio : b / (b / (M : ℝ)) = M := by field_simp
  have hcard : ((tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y : ℕ) : ℝ) ≤
      3 * M := by
    exact_mod_cast tubePairCount_slopeStrip_le_three_mul o x y hb hM c
  by_cases hxy : x = y
  · rw [truncKernel, if_pos hxy, hratio, ENNReal.ofReal_natCast]
    have h : ((tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y : ℕ) : ℝ) ≤
        10 * M := by nlinarith
    exact_mod_cast h
  · have hD : 0 < dist x y := dist_pos.mpr hxy
    by_cases hx : x ∈ Metric.ball o b
    · by_cases hy : y ∈ Metric.ball o b
      · have hDb : dist x y ≤ 2 * b := by
          have h := dist_triangle x o y
          rw [dist_comm o y] at h
          linarith [Metric.mem_ball.mp hx, Metric.mem_ball.mp hy]
        have hcount : ((tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y : ℕ) : ℝ) ≤
            10 * b / dist x y := by
          have h := tubePairCount_slopeStrip_le_slope_count o x y hb hM c
          have hc := card_slope_pair_indices_le hM hD hDb
            (dist_le_sum_abs_slopeCoordinates c x y)
          exact (Nat.cast_le.mpr h).trans hc
        have hmin : ((tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y : ℕ) : ℝ) ≤
            10 * min (M : ℝ) (b / dist x y) := by
          rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10)]
          exact le_min (by nlinarith) (by simpa [mul_div_assoc] using hcount)
        rw [truncKernel, if_neg hxy, hratio]
        have h := ENNReal.ofReal_le_ofReal hmin
        simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10),
          ENNReal.ofReal_ofNat] using h
      · rw [tubePairCount_slopeStrip_eq_zero_of_not_mem_ball o x y b M c (Or.inr hy)]
        simp only [Nat.cast_zero, zero_le]
    · rw [tubePairCount_slopeStrip_eq_zero_of_not_mem_ball o x y b M c (Or.inl hx)]
      simp only [Nat.cast_zero, zero_le]

/-- Both slope charts together form one explicitly indexed finite tube family. -/
def slopeTubeLabels (M : ℕ) : Finset (Bool × (ℤ × ℤ)) :=
  Finset.univ ×ˢ slopeStripLabels M

def slopeTube (o : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (M : ℕ)
    (i : Bool × (ℤ × ℤ)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  slopeStrip o b M i.1 i.2

theorem tubePairCount_slopeTube_eq_add (o x y : EuclideanSpace ℝ (Fin 2))
    (b : ℝ) (M : ℕ) :
    tubePairCount (slopeTubeLabels M) (slopeTube o b M) x y =
      tubePairCount (slopeStripLabels M) (slopeStrip o b M false) x y +
        tubePairCount (slopeStripLabels M) (slopeStrip o b M true) x y := by
  classical
  simp only [tubePairCount, Finset.card_filter]
  simp only [slopeTubeLabels, Finset.sum_product, Fintype.sum_bool]
  simp only [slopeTube, add_comm]
  rfl

/-- The full concrete family satisfies the atom-compatible truncated pair-count bound. -/
theorem tubePairCount_slopeTube_le_truncKernel
    (o x y : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) :
    (tubePairCount (slopeTubeLabels M) (slopeTube o b M) x y : ℝ≥0∞) ≤
      20 * truncKernel (b / M) b x y := by
  rw [tubePairCount_slopeTube_eq_add, Nat.cast_add]
  calc
    _ ≤ 10 * truncKernel (b / M) b x y + 10 * truncKernel (b / M) b x y :=
      add_le_add (tubePairCount_slopeStrip_le_truncKernel o x y hb hM false)
        (tubePairCount_slopeStrip_le_truncKernel o x y hb hM true)
    _ = _ := by ring

/-- The pair-counting energy estimate is proved for this actual finite tube family. -/
theorem sum_measure_slopeTube_sq_le_truncEnergy
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (o : EuclideanSpace ℝ (Fin 2))
    {b : ℝ} (hb : 0 < b) {M : ℕ} (hM : 0 < M) :
    (∑ i ∈ slopeTubeLabels M, μ (slopeTube o b M i) ^ 2) ≤
      20 * truncEnergy μ (b / M) b := by
  rw [sum_measure_sq_eq_lintegral_tubePairCount μ _ _
    (fun i _ ↦ measurableSet_slopeStrip o b M i.1 i.2)]
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, 20 * truncKernel (b / M) b x y ∂μ ∂μ :=
      lintegral_mono fun x ↦ lintegral_mono fun y ↦
        tubePairCount_slopeTube_le_truncKernel o x y hb hM
    _ = _ := by
      simp_rw [lintegral_const_mul' 20 _ (by norm_num)]
      rfl

/-- Heavy pin tubes in the explicit family have the weighted deletion bound from their
actual truncated conditional energy. -/
theorem prod_union_heavy_slopeTubes_le {β : Type*} [MeasurableSpace β]
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) (ν : Measure β) [SFinite ν]
    (o : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) (S : Bool × (ℤ × ℤ) → Set β)
    {a c : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞)
    (hS : ∀ i ∈ slopeTubeLabels M, ν (S i) ≤ c) :
    (μ.prod ν) (⋃ i ∈ (slopeTubeLabels M).filter (fun i ↦ a < μ (slopeTube o b M i)),
      slopeTube o b M i ×ˢ S i) ≤ 20 * (c / a) * truncEnergy μ (b / M) b := by
  refine (prod_union_heavy_tubes_le μ ν _ _ S ha hat hS).trans ?_
  calc
    _ ≤ (c / a) * (20 * truncEnergy μ (b / M) b) :=
      mul_le_mul_right (sum_measure_slopeTube_sq_le_truncEnergy μ o hb hM) _
    _ = _ := by ring

end FalconerPacking
