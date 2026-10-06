/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.FiniteHardPoints
public import Mathlib.Data.Finset.Sort

/-!
# Ordered finite partitions of hard-point sets

Sorting the endpoints of finitely many closed intervals gives consecutive cells which either
lie in their union or have no interior point in that union. For a hard-point set, all partition
nodes are hard, including the right endpoints of complementary cells.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerPacking

private theorem exists_finset_partition_aux {A : Finset ℝ}
    (hzero : 0 ∈ A) (hone : 1 ∈ A) (hA : ∀ x ∈ A, x ∈ Icc (0 : ℝ) 1) :
    ∃ (x : ℕ → ℝ) (N : ℕ), 0 < N ∧ Monotone x ∧ x 0 = 0 ∧ x N = 1 ∧
      (∀ i, x i ∈ A) ∧ ∀ i < N, ∀ z ∈ Ioo (x i) (x (i + 1)), z ∉ A := by
  have hcard : 1 < A.card := Finset.one_lt_card.mpr ⟨0, hzero, 1, hone, by norm_num⟩
  let N := A.card - 1
  have hN : N < A.card := by dsimp [N]; omega
  let index (i : ℕ) : Fin A.card := ⟨min i N, (min_le_right i N).trans_lt hN⟩
  let e := A.orderEmbOfFin rfl
  let x (i : ℕ) : ℝ := e (index i)
  have hmem : ∀ i, x i ∈ A := fun i ↦ A.orderEmbOfFin_mem rfl (index i)
  have hmono : Monotone x := by
    intro i j hij
    exact e.monotone (show index i ≤ index j from min_le_min_right N hij)
  have hpreimage : ∀ z ∈ A, ∃ k : Fin A.card, e k = z := by
    intro z hz
    have hz' : z ∈ Set.range e := by simpa only [e, Finset.range_orderEmbOfFin,
      Finset.mem_coe] using hz
    exact hz'
  have hxzero : x 0 = 0 := by
    obtain ⟨k, hk⟩ := hpreimage 0 hzero
    apply le_antisymm _ (hA _ (hmem 0)).1
    rw [← hk]
    exact e.monotone (show index 0 ≤ k by change min 0 N ≤ k.val; omega)
  have hxone : x N = 1 := by
    obtain ⟨k, hk⟩ := hpreimage 1 hone
    apply le_antisymm (hA _ (hmem N)).2
    rw [← hk]
    exact e.monotone (show k ≤ index N by
      change k.val ≤ min N N
      dsimp [N]
      omega)
  refine ⟨x, N, by dsimp [N]; omega, hmono, hxzero, hxone, hmem, ?_⟩
  intro i hi z hz hza
  obtain ⟨k, hk⟩ := hpreimage z hza
  have hleft : index i < k := e.lt_iff_lt.mp (by simpa only [x, hk] using hz.1)
  have hright : k < index (i + 1) := e.lt_iff_lt.mp (by simpa only [x, hk] using hz.2)
  have hiN : min i N = i := min_eq_left hi.le
  have hiN' : min (i + 1) N = i + 1 := min_eq_left hi
  change min i N < k.val at hleft
  change k.val < min (i + 1) N at hright
  omega

private def intervalEndpoints (intervals : Finset (ℝ × ℝ)) : Finset ℝ :=
  insert 0 (insert 1 ((intervals.filter (fun p ↦ p.1 ≤ p.2)).biUnion
    (fun p ↦ {p.1, p.2})))

private theorem intervalEndpoints_mem_aux {intervals : Finset (ℝ × ℝ)} {p : ℝ × ℝ}
    (hp : p ∈ intervals) (hle : p.1 ≤ p.2) :
    p.1 ∈ intervalEndpoints intervals ∧ p.2 ∈ intervalEndpoints intervals := by
  classical
  constructor <;> simp only [intervalEndpoints, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_singleton]
  · exact Or.inr (Or.inr ⟨p, ⟨hp, hle⟩, Or.inl rfl⟩)
  · exact Or.inr (Or.inr ⟨p, ⟨hp, hle⟩, Or.inr rfl⟩)

private theorem intervalEndpoints_subset_aux {H : Set ℝ} {intervals : Finset (ℝ × ℝ)}
    (hzero : 0 ∈ H) (hone : 1 ∈ H)
    (hintervals : H = ⋃ p ∈ intervals, Icc p.1 p.2) :
    ∀ z ∈ intervalEndpoints intervals, z ∈ H := by
  intro z hz
  simp only [intervalEndpoints, Finset.mem_insert, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | ⟨p, ⟨hp, hle⟩, rfl | rfl⟩
  · exact hzero
  · exact hone
  · rw [hintervals]
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, le_rfl, hle⟩⟩
  · rw [hintervals]
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, hle, le_rfl⟩⟩

private theorem interval_cell_dichotomy_aux {H : Set ℝ} {intervals : Finset (ℝ × ℝ)}
    (hintervals : H = ⋃ p ∈ intervals, Icc p.1 p.2) {a b : ℝ}
    (hno : ∀ z ∈ Ioo a b, z ∉ intervalEndpoints intervals) :
    Icc a b ⊆ H ∨ ∀ z ∈ Ioo a b, z ∉ H := by
  by_cases hsome : ∃ z ∈ Ioo a b, z ∈ H
  · obtain ⟨z, hz, hzH⟩ := hsome
    rw [hintervals] at hzH
    obtain ⟨p, hp, hzp⟩ := mem_iUnion.mp hzH |>.imp fun _ h ↦ mem_iUnion.mp h
    obtain ⟨hpleft, hpright⟩ := intervalEndpoints_mem_aux hp (hzp.1.trans hzp.2)
    have hpa : p.1 ≤ a := by
      by_contra h
      exact hno p.1 ⟨lt_of_not_ge h, hzp.1.trans_lt hz.2⟩ hpleft
    have hbp : b ≤ p.2 := by
      by_contra h
      exact hno p.2 ⟨hz.1.trans_le hzp.2, lt_of_not_ge h⟩ hpright
    left
    intro y hy
    rw [hintervals]
    exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hp, hpa.trans hy.1, hy.2.trans hbp⟩⟩
  · exact Or.inr (fun z hz hzH ↦ hsome ⟨z, hz, hzH⟩)

/-- Sorting the interval endpoints gives cells wholly inside the set or disjoint in the interior. -/
theorem exists_finite_interval_partition {H : Set ℝ} {intervals : Finset (ℝ × ℝ)}
    (hzero : 0 ∈ H) (hone : 1 ∈ H) (hunit : H ⊆ Icc (0 : ℝ) 1)
    (hintervals : H = ⋃ p ∈ intervals, Icc p.1 p.2) :
    ∃ (x : ℕ → ℝ) (N : ℕ), 0 < N ∧ Monotone x ∧ x 0 = 0 ∧ x N = 1 ∧
      (∀ i, x i ∈ H) ∧
      ∀ i < N, Icc (x i) (x (i + 1)) ⊆ H ∨
        (x (i + 1) ∈ H ∧ ∀ z ∈ Ioo (x i) (x (i + 1)), z ∉ H) := by
  have hsub := intervalEndpoints_subset_aux hzero hone hintervals
  obtain ⟨x, N, hN, hmono, hxzero, hxone, hmem, hno⟩ := exists_finset_partition_aux
    (A := intervalEndpoints intervals) (by simp [intervalEndpoints])
    (by simp [intervalEndpoints]) (fun z hz ↦ hunit (hsub z hz))
  refine ⟨x, N, hN, hmono, hxzero, hxone, fun i ↦ hsub _ (hmem i), ?_⟩
  intro i hi
  rcases interval_cell_dichotomy_aux hintervals (hno i hi) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨hsub _ (hmem (i + 1)), h⟩

/-- A finite interval description supplies exactly the hard and gap budgets used by chains. -/
theorem exists_hardProfile_partition_of_finite_intervals {f : ℝ → ℝ}
    {intervals : Finset (ℝ × ℝ)} (hzero : 0 ∈ hardProfilePoints f)
    (hone : 1 ∈ hardProfilePoints f)
    (hintervals : hardProfilePoints f = ⋃ p ∈ intervals, Icc p.1 p.2) :
    ∃ (x c : ℕ → ℝ) (M : ℕ), 0 < M ∧ Monotone x ∧ x 0 = 0 ∧ x M = 1 ∧
      (∀ i, x i ∈ hardProfilePoints f) ∧
      ∀ i < M, (Icc (x i) (x (i + 1)) ⊆ hardProfilePoints f ∧ c i = 0) ∨
        (x (i + 1) ∈ hardProfilePoints f ∧
          (∀ z ∈ Ioo (x i) (x (i + 1)), z ∉ hardProfilePoints f) ∧
          c i = f (x i) - f (x (i + 1))) := by
  classical
  obtain ⟨x, M, hM, hmono, hxzero, hxone, hmem, hseg⟩ :=
    exists_finite_interval_partition hzero hone (fun _ h ↦ h.1) hintervals
  let c (i : ℕ) : ℝ := if Icc (x i) (x (i + 1)) ⊆ hardProfilePoints f then 0
    else f (x i) - f (x (i + 1))
  refine ⟨x, c, M, hM, hmono, hxzero, hxone, hmem, ?_⟩
  intro i hi
  by_cases h : Icc (x i) (x (i + 1)) ⊆ hardProfilePoints f
  · exact Or.inl ⟨h, if_pos h⟩
  · obtain ⟨hright, hgap⟩ := (hseg i hi).resolve_left h
    exact Or.inr ⟨hright, hgap, if_neg h⟩

private theorem normalizedProfileInterpolation_nonneg_aux {g : ℕ → ℝ} {N : ℕ}
    (hnonneg : ∀ j, j ≤ N → 0 ≤ g j) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ normalizedProfileInterpolation g N x := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNx : (N : ℝ) * x ∈ Icc (0 : ℝ) N :=
    ⟨mul_nonneg hN hx.1, by nlinarith [hx.2]⟩
  have hmin : 0 ≤ gMin g 0 N := le_gMin (Nat.zero_le N) (fun j _ hj ↦ hnonneg j hj)
  exact div_nonneg (hmin.trans (gMin_le_profileInterpolation (Nat.zero_le N) le_rfl
    (by simpa only [Nat.cast_zero] using hNx))) hN

/-- The actual normalized interpolation has a finite ordered hard/gap partition.
The only endpoint hypothesis is that the original profile is nonnegative and vanishes at zero. -/
theorem exists_normalized_hardProfile_partition {g : ℕ → ℝ} {N : ℕ}
    (hN : 0 < N) (hzero : g 0 = 0) (hnonneg : ∀ j, j ≤ N → 0 ≤ g j) :
    ∃ (x c : ℕ → ℝ) (M : ℕ), 0 < M ∧ Monotone x ∧ x 0 = 0 ∧ x M = 1 ∧
      (∀ i, x i ∈ hardProfilePoints (normalizedProfileInterpolation g N)) ∧
      ∀ i < M,
        (Icc (x i) (x (i + 1)) ⊆ hardProfilePoints (normalizedProfileInterpolation g N) ∧
          c i = 0) ∨
        (x (i + 1) ∈ hardProfilePoints (normalizedProfileInterpolation g N) ∧
          (∀ z ∈ Ioo (x i) (x (i + 1)),
            z ∉ hardProfilePoints (normalizedProfileInterpolation g N)) ∧
          c i = normalizedProfileInterpolation g N (x i) -
            normalizedProfileInterpolation g N (x (i + 1))) := by
  obtain ⟨intervals, hintervals⟩ := hardProfilePoints_normalized_finite_intervals (g := g) hN
  have hfzero : normalizedProfileInterpolation g N 0 = 0 := by
    simpa only [Nat.cast_zero, zero_div, hzero] using
      normalizedProfileInterpolation_natCast g hN (Nat.zero_le N)
  apply exists_hardProfile_partition_of_finite_intervals _
    (one_mem_hardProfilePoints _) hintervals
  exact zero_mem_hardProfilePoints hfzero
    (fun _ hx ↦ normalizedProfileInterpolation_nonneg_aux hnonneg hx)

end FalconerPacking
