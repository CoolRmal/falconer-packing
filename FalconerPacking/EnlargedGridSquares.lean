/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SelectedTubeGeometry
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Overlap and support margins for enlarged grid squares

The grid has arbitrary positive spacing. Closed boundary conventions are allowed, so the
overlap estimate applies to all concentric enlargements without exceptional null sets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

attribute [local instance] Classical.propDecidable

/-- The center of the grid cell with integer address k and positive spacing a. -/
def gridSquareCenter (a : ℝ) (k : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i ↦ a * ((k i : ℝ) + 1 / 2))

/-- The concentric enlargement by t of a square of the a-grid. -/
def enlargedGridSquare (a t : ℝ) (k : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  frameRectangle (LinearIsometryEquiv.refl ℝ _) (gridSquareCenter a k) (t * a / 2) (t * a / 2)

/-- Grid-square membership is given by the two coordinate inequalities. -/
theorem mem_enlargedGridSquare_iff (a t : ℝ) (k : Fin 2 → ℤ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ enlargedGridSquare a t k ↔
      ∀ i, |x i - a * ((k i : ℝ) + 1 / 2)| ≤ t * a / 2 := by
  simp [enlargedGridSquare, frameRectangle, gridSquareCenter, Fin.forall_fin_two]

/-- Every enlarged grid square is measurable. -/
theorem measurableSet_enlargedGridSquare (a t : ℝ) (k : Fin 2 → ℤ) :
    MeasurableSet (enlargedGridSquare a t k) :=
  measurableSet_frameRectangle _ _ _ _

/-- A point in an enlarged square is within its side length of the center. -/
theorem norm_sub_gridSquareCenter_le {a t : ℝ} {k : Fin 2 → ℤ}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ enlargedGridSquare a t k) :
    ‖x - gridSquareCenter a k‖ ≤ t * a :=
  frameRectangle_square_norm_le _ hx

/-- An integer center contributing at x lies in a uniformly short integer interval. -/
theorem grid_index_bounds_of_coordinate {a t x : ℝ} {k : ℤ}
    (ha : 0 < a)
    (hx : |x - a * ((k : ℝ) + 1 / 2)| ≤ t * a / 2) :
    ⌊x / a⌋ - (⌈t⌉₊ + 1 : ℕ) ≤ k ∧ k ≤ ⌊x / a⌋ + (⌈t⌉₊ + 1 : ℕ) := by
  have hs : |x / a - ((k : ℝ) + 1 / 2)| ≤ t / 2 := by
    have he : x / a - ((k : ℝ) + 1 / 2) = (x - a * ((k : ℝ) + 1 / 2)) / a := by
      field_simp
    rw [he, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr (by linarith)
  have hlo := Int.floor_le (x / a)
  have hhi := Int.lt_floor_add_one (x / a)
  have hceil := Nat.le_ceil t
  obtain ⟨hs₀, hs₁⟩ := abs_le.mp hs
  constructor
  · have hr : (⌊x / a⌋ : ℝ) - ((⌈t⌉₊ : ℝ) + 1) ≤ k := by linarith
    exact_mod_cast hr
  · have hr : (k : ℝ) ≤ (⌊x / a⌋ : ℝ) + ((⌈t⌉₊ : ℝ) + 1) := by linarith
    exact_mod_cast hr

/-- The pointwise overlap of enlarged grid squares is quadratic in the enlargement. -/
theorem card_enlargedGridSquare_overlap_le {a t : ℝ} (ha : 0 < a)
    (I : Finset (Fin 2 → ℤ)) (x : EuclideanSpace ℝ (Fin 2)) :
    (I.filter fun k ↦ x ∈ enlargedGridSquare a t k).card ≤ (2 * ⌈t⌉₊ + 3) ^ 2 := by
  classical
  let N := ⌈t⌉₊ + 1
  let J := Fintype.piFinset (fun i : Fin 2 ↦
    Finset.Icc (⌊x i / a⌋ - (N : ℤ)) (⌊x i / a⌋ + (N : ℤ)))
  have hsub : I.filter (fun k ↦ x ∈ enlargedGridSquare a t k) ⊆ J := by
    intro k hk
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (grid_index_bounds_of_coordinate ha
      ((mem_enlargedGridSquare_iff a t k x).mp (Finset.mem_filter.mp hk).2 i))
  have hcard (z : ℤ) : (Finset.Icc (z - (N : ℤ)) (z + (N : ℤ))).card = 2 * N + 1 := by
    rw [Int.card_Icc]
    have he : z + (N : ℤ) + 1 - (z - (N : ℤ)) = (2 * N + 1 : ℕ) := by push_cast; ring
    rw [he, Int.toNat_natCast]
  calc
    _ ≤ J.card := Finset.card_le_card hsub
    _ = (2 * ⌈t⌉₊ + 3) ^ 2 := by
      simp only [J, Fintype.card_piFinset, hcard, Fin.prod_univ_two]
      dsimp [N]
      ring

/-- For enlargement at least one, the overlap is bounded by 49 times its square. -/
theorem card_enlargedGridSquare_overlap_le_real {a t : ℝ}
    (ha : 0 < a) (ht : 1 ≤ t)
    (I : Finset (Fin 2 → ℤ)) (x : EuclideanSpace ℝ (Fin 2)) :
    ((I.filter fun k ↦ x ∈ enlargedGridSquare a t k).card : ℝ) ≤ 49 * t ^ 2 := by
  have ht₀ : 0 ≤ t := le_trans (by norm_num) ht
  have hc := card_enlargedGridSquare_overlap_le (t := t) ha I x
  have hr : (((I.filter fun k ↦ x ∈ enlargedGridSquare a t k).card : ℕ) : ℝ) ≤
      (2 * (⌈t⌉₊ : ℝ) + 3) ^ 2 := by exact_mod_cast hc
  have hceil := Nat.ceil_lt_add_one ht₀
  have hbase : 0 ≤ 2 * (⌈t⌉₊ : ℝ) + 3 := by positivity
  have hu : 2 * (⌈t⌉₊ : ℝ) + 3 ≤ 7 * t := by linarith
  nlinarith [sq_le_sq₀ hbase (by positivity : 0 ≤ 7 * t) |>.mpr hu]

/-- A child center in a square and a controlled enlargement leave an explicit margin
inside a sufficiently enlarged parent. The conclusion is pointwise, not merely almost everywhere. -/
theorem dist_le_margin_of_square_enlargement
    {a b t R L : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t)
    (hR : 1 + t + 2 * L ≤ R)
    {p q x y : EuclideanSpace ℝ (Fin 2)}
    (hq : ∀ i, |q i - p i| ≤ b / 2)
    (hx : ∀ i, |x i - q i| ≤ t * a / 2)
    (hy : y ∉ frameRectangle (LinearIsometryEquiv.refl ℝ _) p (R * b / 2) (R * b / 2)) :
    L * b ≤ dist x y := by
  have hb : 0 ≤ b := ha.trans hab
  have hxP (i : Fin 2) : |x i - p i| ≤ (1 + t) * b / 2 := by
    calc
      _ ≤ |x i - q i| + |q i - p i| := abs_sub_le _ _ _
      _ ≤ t * a / 2 + b / 2 := add_le_add (hx i) (hq i)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hab ht]
  have hy' : ∃ i : Fin 2, R * b / 2 < |y i - p i| := by
    by_contra hn
    push Not at hn
    apply hy
    exact ⟨hn 0, hn 1⟩
  obtain ⟨i, hi⟩ := hy'
  have hxy : |y i - x i| ≤ dist x y := by
    have h := PiLp.norm_apply_le (y - x) i
    change |y i - x i| ≤ ‖y - x‖ at h
    simpa only [dist_eq_norm, norm_sub_rev x y] using h
  have htriangle := abs_sub_le (y i) (x i) (p i)
  have hscale := mul_le_mul_of_nonneg_right hR hb
  nlinarith [hxP i]

/-- The powers prescribed by the embedding construction provide a margin of Lb. -/
theorem embedding_parent_margin_powers {L : ℝ} (hL : 4 ≤ L) (j : ℕ) :
    1 + L ^ (2 * j + 3) + 2 * L ≤ L ^ (2 * j + 4) := by
  have hL₁ : 1 ≤ L := by linarith
  have ht : L ≤ L ^ (2 * j + 3) := le_self_pow₀ hL₁ (by omega)
  have hp : L ^ (2 * j + 4) = L ^ (2 * j + 3) * L := by
    rw [show 2 * j + 4 = (2 * j + 3) + 1 by omega, pow_succ]
  rw [hp]
  nlinarith

/-- Enlarged child squares have the full Lb margin from the complement of the parent
enlargement used in the embedding lemma. -/
theorem enlargedGridSquare_parent_margin
    {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hL : 4 ≤ L) (j : ℕ)
    {k : Fin 2 → ℤ} {p x y : EuclideanSpace ℝ (Fin 2)}
    (hq : ∀ i, |(gridSquareCenter a k) i - p i| ≤ b / 2)
    (hx : x ∈ enlargedGridSquare a (L ^ (2 * j + 3)) k)
    (hy : y ∉ frameRectangle (LinearIsometryEquiv.refl ℝ _) p
      (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2)) :
    L * b ≤ dist x y := by
  apply dist_le_margin_of_square_enlargement ha.le hab
    (pow_nonneg (by linarith : 0 ≤ L) _) (embedding_parent_margin_powers hL j) hq
    ((mem_enlargedGridSquare_iff _ _ _ _).mp hx) hy

/-- In particular the enlarged child lies entirely inside the enlarged parent. -/
theorem enlargedGridSquare_subset_parent
    {a b L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hL : 4 ≤ L) (j : ℕ)
    {k : Fin 2 → ℤ} {p : EuclideanSpace ℝ (Fin 2)}
    (hq : ∀ i, |(gridSquareCenter a k) i - p i| ≤ b / 2) :
    enlargedGridSquare a (L ^ (2 * j + 3)) k ⊆
      frameRectangle (LinearIsometryEquiv.refl ℝ _) p
        (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2) := by
  intro x hx
  by_contra h
  have hc := enlargedGridSquare_parent_margin ha hab hL j hq hx h
  rw [dist_self] at hc
  have hp : 0 < L * b := mul_pos (by linarith) (ha.trans_le hab)
  exact hp.not_ge hc

/-- The overlap exponent in the embedding construction is 4j+4. -/
theorem embedding_grid_overlap {a L : ℝ} (ha : 0 < a) (hL : 1 ≤ L)
    (j : ℕ) (I : Finset (Fin 2 → ℤ)) (x : EuclideanSpace ℝ (Fin 2)) :
    ((I.filter fun k ↦ x ∈ enlargedGridSquare a (L ^ (2 * j + 2)) k).card : ℝ) ≤
      49 * L ^ (4 * j + 4) := by
  have h := card_enlargedGridSquare_overlap_le_real (t := L ^ (2 * j + 2))
    ha (one_le_pow₀ hL) I x
  convert h using 1
  rw [← pow_mul]
  congr 2
  omega

/-- The prescribed tested tube is wide enough for the proved containment constant,
once the fixed dilation parameter is chosen in terms of the directional mismatch. -/
theorem embedding_tested_tube_size {L C₀ : ℝ} (hL : 1 ≤ L)
    (hsize : 2 * (5 + 7 * C₀) ≤ L) (j K : ℕ) (hj : j < K) :
    2 * (5 + 7 * C₀) * L ^ (2 * j + 3) ≤ L ^ (4 * K + 20) := by
  calc
    _ ≤ L * L ^ (2 * j + 3) :=
      mul_le_mul_of_nonneg_right hsize (pow_nonneg (by linarith) _)
    _ = L ^ (2 * j + 4) := by
      rw [show 2 * j + 4 = (2 * j + 3) + 1 by omega, pow_succ L (2 * j + 3)]
      ring
    _ ≤ _ := pow_le_pow_right₀ hL (by omega)

end FalconerPacking
