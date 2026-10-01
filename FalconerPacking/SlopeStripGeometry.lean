/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.TubePairCounting
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max

/-!
# An explicit slope net for strip pair counting

The two bounded-slope charts replace trigonometric angle counting by integer interval
counting. Strip offsets are half-open, so one point has at most one offset per slope.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A finite set of integers of real diameter at most `R` has at most `R+1` members. -/
theorem int_finset_card_le_real_diameter (S : Finset ℤ) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : ∀ k ∈ S, ∀ l ∈ S, |(k : ℝ) - l| ≤ R) :
    (S.card : ℝ) ≤ R + 1 := by
  classical
  by_cases hS : S.Nonempty
  · have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨S.min'_le k hk, S.le_max' k hk⟩
    have hminmax : S.min' hS ≤ S.max' hS := S.min'_le _ (S.max'_mem hS)
    have hcard : (S.card : ℤ) ≤ S.max' hS + 1 - S.min' hS := by
      have h := Finset.card_le_card hsub
      have hcast : (S.card : ℤ) ≤ (Finset.Icc (S.min' hS) (S.max' hS)).card := by
        exact_mod_cast h
      rw [Int.card_Icc_of_le (a := S.min' hS) (b := S.max' hS) (by omega)] at hcast
      exact hcast
    have hcard' : (S.card : ℝ) ≤ (S.max' hS : ℝ) + 1 - S.min' hS := by
      exact_mod_cast hcard
    have hd := (abs_le.mp (hdiam _ (S.max'_mem hS) _ (S.min'_mem hS))).2
    linarith
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
    linarith

/-- The directions are uniformly spaced slopes between minus one and one. -/
def slopeNet (M : ℕ) : Finset ℤ := Finset.Icc (-(M : ℤ)) M

theorem abs_slope_le_one {M : ℕ} (hM : 0 < M) {k : ℤ} (hk : k ∈ slopeNet M) :
    |(k : ℝ) / M| ≤ 1 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hk' := Finset.mem_Icc.mp hk
  have hlow : -(M : ℝ) ≤ k := by exact_mod_cast hk'.1
  have hupp : (k : ℝ) ≤ M := by exact_mod_cast hk'.2
  rw [abs_div, abs_of_pos hMr, div_le_one hMr]
  exact abs_le.mpr ⟨hlow, hupp⟩

/-- Admissible slopes for a pair have integer diameter controlled by its second coordinate. -/
theorem slope_pair_index_diameter {M : ℕ} (hM : 0 < M) {a v w : ℝ}
    (hw : w ≠ 0) {k l : ℤ}
    (hk : |v - (k : ℝ) / M * w| ≤ a) (hl : |v - (l : ℝ) / M * w| ≤ a) :
    |(k : ℝ) - l| ≤ 2 * a * M / |w| := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have heq : ((k : ℝ) - l) * w =
      (M : ℝ) * ((v - (l : ℝ) / M * w) - (v - (k : ℝ) / M * w)) := by
    field_simp
    ring
  have hab : |(k : ℝ) - l| * |w| ≤ 2 * a * M := by
    calc
      _ = |((k : ℝ) - l) * w| := (abs_mul _ _).symm
      _ = (M : ℝ) * |(v - (l : ℝ) / M * w) - (v - (k : ℝ) / M * w)| := by
        rw [heq, abs_mul, abs_of_pos hMr]
      _ ≤ (M : ℝ) * (|v - (l : ℝ) / M * w| + |v - (k : ℝ) / M * w|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hMr.le
      _ ≤ 2 * a * M := by nlinarith
  exact (le_div_iff₀ (abs_pos.mpr hw)).mpr hab

theorem card_slopeNet (M : ℕ) : (slopeNet M).card = 2 * M + 1 := by
  have h := Int.card_Icc_of_le (a := -(M : ℤ)) (b := M) (by omega)
  unfold slopeNet
  omega

/-- The admissible slopes of a separated pair have the required inverse-distance count. -/
theorem card_slope_pair_indices_le {M : ℕ} (hM : 0 < M) {b v w D : ℝ}
    (hD : 0 < D) (hDb : D ≤ 2 * b) (hcoord : D ≤ |v| + |w|) :
    ((slopeNet M).filter (fun k : ℤ ↦ |v - (k : ℝ) / M * w| ≤ b / M)).card ≤
      (10 * b / D : ℝ) := by
  classical
  let J := (slopeNet M).filter (fun k : ℤ ↦ |v - (k : ℝ) / M * w| ≤ b / M)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hb : 0 < b := by linarith
  have hcard : (J.card : ℝ) ≤ 3 * M := by
    have h := Finset.card_le_card (Finset.filter_subset
      (fun k : ℤ ↦ |v - (k : ℝ) / M * w| ≤ b / M) (slopeNet M))
    rw [card_slopeNet] at h
    change J.card ≤ 2 * M + 1 at h
    have h' : (J.card : ℝ) ≤ 2 * M + 1 := by
      calc
        _ ≤ ((2 * M + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h
        _ = _ := by push_cast; rfl
    have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  by_cases hsmall : D ≤ 2 * (b / M)
  · apply (le_div_iff₀ hD).mpr
    have hsmall' : D * M ≤ 2 * b := by
      have h := (le_div_iff₀ hMr).mp (show D ≤ 2 * b / M by simpa [mul_div_assoc] using hsmall)
      exact h
    have := mul_le_mul_of_nonneg_right hcard hD.le
    nlinarith
  · by_cases hJ : J.Nonempty
    · obtain ⟨k, hk⟩ := hJ
      have hknet : k ∈ slopeNet M := (Finset.mem_filter.mp hk).1
      have hkstrip := (Finset.mem_filter.mp hk).2
      have hv : |v| ≤ b / M + |w| := by
        calc
          _ = |(v - (k : ℝ) / M * w) + (k : ℝ) / M * w| := by congr 1; ring
          _ ≤ |v - (k : ℝ) / M * w| + |(k : ℝ) / M * w| := abs_add_le _ _
          _ ≤ b / M + |w| := by
            rw [abs_mul]
            exact add_le_add hkstrip (by simpa using
              (mul_le_mul_of_nonneg_right (abs_slope_le_one hM hknet) (abs_nonneg w)))
      have hDw : D < 4 * |w| := by linarith
      have hw : w ≠ 0 := by intro hw; simp [hw] at hDw; linarith
      have hcount : (J.card : ℝ) ≤ 2 * b / |w| + 1 := by
        apply int_finset_card_le_real_diameter J (by positivity)
        intro k hk l hl
        have h := slope_pair_index_diameter hM hw
          (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2
        have he : 2 * (b / (M : ℝ)) * M / |w| = 2 * b / |w| := by
          field_simp
        rwa [he] at h
      have hratio : 2 * b / |w| ≤ 8 * b / D := by
        apply (div_le_div_iff₀ (abs_pos.mpr hw) hD).mpr
        nlinarith
      have hfinish : 8 * b / D + 1 ≤ 10 * b / D := by
        apply (le_div_iff₀ hD).mpr
        have he : (8 * b / D + 1) * D = 8 * b + D := by field_simp
        rw [he]
        linarith
      exact hcount.trans ((add_le_add_left hratio 1).trans hfinish)
    · have hzero : J.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hJ)
      change (J.card : ℝ) ≤ _
      rw [hzero, Nat.cast_zero]
      positivity

/-- Either coordinate chart, without introducing another type for the plane. -/
def slopeCoordinate (c : Bool) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if c then x 1 else x 0

/-- The unnormalized normal coordinate in a bounded-slope chart. -/
def slopeLinearCoordinate (c : Bool) (t : ℝ) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  slopeCoordinate c x - t * slopeCoordinate (!c) x

theorem slopeLinearCoordinate_sub (c : Bool) (t : ℝ)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    slopeLinearCoordinate c t (x - y) =
      slopeLinearCoordinate c t x - slopeLinearCoordinate c t y := by
  cases c <;> simp [slopeLinearCoordinate, slopeCoordinate] <;> ring

/-- Explicit finite labels: a slope and a parallel half-open strip offset. -/
def slopeStripLabels (M : ℕ) : Finset (ℤ × ℤ) :=
  (slopeNet M) ×ˢ (Finset.Icc (-(3 * M : ℤ)) (3 * M))

/-- An actual parallel strip of width `b/M`, cut off to the radius-`b` support ball. -/
def slopeStrip (o : EuclideanSpace ℝ (Fin 2)) (b : ℝ) (M : ℕ) (c : Bool)
    (kl : ℤ × ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Metric.ball o b ∩ {x | slopeLinearCoordinate c ((kl.1 : ℝ) / M) (x - o) ∈
    Ico ((kl.2 : ℝ) * (b / M)) (((kl.2 : ℝ) + 1) * (b / M))}

theorem measurableSet_slopeStrip (o : EuclideanSpace ℝ (Fin 2))
    (b : ℝ) (M : ℕ) (c : Bool) (kl : ℤ × ℤ) :
    MeasurableSet (slopeStrip o b M c kl) := by
  unfold slopeStrip
  apply Metric.isOpen_ball.measurableSet.inter
  apply MeasurableSet.preimage measurableSet_Ico
  cases c <;> simp only [slopeLinearCoordinate, slopeCoordinate, Bool.false_eq_true,
    if_false, Bool.not_false, if_true, Bool.not_true]
  all_goals fun_prop

/-- Half-open parallel strips have at most one offset at every point. -/
theorem slopeStrip_offset_unique {o : EuclideanSpace ℝ (Fin 2)} {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) {c : Bool} {k l l' : ℤ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ slopeStrip o b M c (k, l)) (hx' : x ∈ slopeStrip o b M c (k, l')) :
    l = l' := by
  have ha : 0 < b / M := div_pos hb (by exact_mod_cast hM)
  have h : (l : ℝ) < (l' : ℝ) + 1 := by
    apply (mul_lt_mul_iff_of_pos_right ha).mp
    exact hx.2.1.trans_lt hx'.2.2
  have h' : (l' : ℝ) < (l : ℝ) + 1 := by
    apply (mul_lt_mul_iff_of_pos_right ha).mp
    exact hx'.2.1.trans_lt hx.2.2
  have hi : l < l' + 1 := by exact_mod_cast h
  have hi' : l' < l + 1 := by exact_mod_cast h'
  omega

/-- A common strip forces the expected small normal-coordinate difference. -/
theorem abs_slopeLinearCoordinate_sub_le_of_mem_strip
    {o x y : EuclideanSpace ℝ (Fin 2)} {b : ℝ} {M : ℕ} {c : Bool} {kl : ℤ × ℤ}
    (hx : x ∈ slopeStrip o b M c kl) (hy : y ∈ slopeStrip o b M c kl) :
    |slopeLinearCoordinate c ((kl.1 : ℝ) / M) (x - y)| ≤ b / M := by
  have he : slopeLinearCoordinate c ((kl.1 : ℝ) / M) (x - y) =
      slopeLinearCoordinate c ((kl.1 : ℝ) / M) (x - o) -
        slopeLinearCoordinate c ((kl.1 : ℝ) / M) (y - o) := by
    rw [slopeLinearCoordinate_sub, slopeLinearCoordinate_sub, slopeLinearCoordinate_sub]
    ring
  rw [he, abs_le]
  constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]

theorem dist_le_sum_abs_slopeCoordinates (c : Bool)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ≤ |slopeCoordinate c (x - y)| + |slopeCoordinate (!c) (x - y)| := by
  rw [dist_eq_norm]
  have h := EuclideanSpace.real_norm_sq_eq (x - y)
  rw [Fin.sum_univ_two] at h
  have hsum : ‖x - y‖ ≤ |(x - y) 0| + |(x - y) 1| := by
    nlinarith [sq_abs ((x - y) 0), sq_abs ((x - y) 1),
      abs_nonneg ((x - y) 0), abs_nonneg ((x - y) 1),
      mul_nonneg (abs_nonneg ((x - y) 0)) (abs_nonneg ((x - y) 1)), norm_nonneg (x - y)]
  cases c <;> simpa [slopeCoordinate, add_comm] using hsum

/-- Distinct common strips have distinct slope labels. -/
theorem tubePairCount_slopeStrip_le_slope_count
    (o x y : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) (c : Bool) :
    tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y ≤
      ((slopeNet M).filter (fun k : ℤ ↦
        |slopeCoordinate c (x - y) - (k : ℝ) / M * slopeCoordinate (!c) (x - y)| ≤
          b / M)).card := by
  classical
  unfold tubePairCount
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro kl hkl
    have hkl' := Finset.mem_filter.mp hkl
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hkl'.1).1, ?_⟩
    exact abs_slopeLinearCoordinate_sub_le_of_mem_strip hkl'.2.1 hkl'.2.2
  · intro kl hkl kl' hkl' heq
    obtain ⟨k, l⟩ := kl
    obtain ⟨k', l'⟩ := kl'
    dsimp only at heq
    subst k'
    have hll := slopeStrip_offset_unique hb hM
      (Finset.mem_filter.mp hkl).2.1 (Finset.mem_filter.mp hkl').2.1
    exact congrArg (fun z ↦ (k, z)) hll

/-- At every pair, including the diagonal, there are at most three times `M` common strips. -/
theorem tubePairCount_slopeStrip_le_three_mul
    (o x y : EuclideanSpace ℝ (Fin 2)) {b : ℝ} (hb : 0 < b)
    {M : ℕ} (hM : 0 < M) (c : Bool) :
    tubePairCount (slopeStripLabels M) (slopeStrip o b M c) x y ≤ 3 * M := by
  have h := (tubePairCount_slopeStrip_le_slope_count o x y hb hM c).trans
    (Finset.card_le_card (Finset.filter_subset _ _))
  rw [card_slopeNet] at h
  omega

end FalconerPacking
