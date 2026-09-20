/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Statement
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Dyadic cubes in the plane

Module 4 of the implementation ledger, first half: the geometric cube hierarchy used by the
conditional measures of the manuscript.  A dyadic square of generation `n` is a product of
half-open coordinate intervals of side `2⁻ⁿ`, indexed by integers.

* `mem_dyadicCube_iff` — membership is exactly the statement that the index is the floor index,
  so the generation-`n` cubes partition the plane;
* `dyadicCube_disjoint` — distinct cubes of one generation are disjoint;
* `dyadicCube_succ_subset` — each cube is contained in its parent, whose index is `k / 2`;
* `dist_le_of_mem_dyadicCube` — a generation-`n` cube has diameter at most `√2 / 2ⁿ`;
* `measurableSet_dyadicCube` — cubes are Borel.

This is the geometric hierarchy, not `Data.Dyadic`, which is an arithmetic number type.
-/

noncomputable section

open Set

namespace FalconerPacking

/-- The dyadic square of generation `n` with integer index `k`, half-open in each coordinate. -/
def dyadicCube (n : ℕ) (k : Fin 2 → ℤ) : Set Plane :=
  {x | ∀ i, (k i : ℝ) ≤ 2 ^ n * x i ∧ 2 ^ n * x i < (k i : ℝ) + 1}

/-- The index of the generation-`n` cube containing `x`. -/
def cubeIndex (n : ℕ) (x : Plane) : Fin 2 → ℤ := fun i ↦ ⌊(2 : ℝ) ^ n * x i⌋

theorem mem_dyadicCube_iff {n : ℕ} {k : Fin 2 → ℤ} {x : Plane} :
    x ∈ dyadicCube n k ↔ cubeIndex n x = k := by
  constructor
  · intro h
    funext i
    exact Int.floor_eq_iff.2 ⟨(h i).1, (h i).2⟩
  · intro h i
    have hi : ⌊(2 : ℝ) ^ n * x i⌋ = k i := congrFun h i
    rw [← hi]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

theorem mem_dyadicCube_cubeIndex (n : ℕ) (x : Plane) : x ∈ dyadicCube n (cubeIndex n x) :=
  mem_dyadicCube_iff.2 rfl

/-- Distinct cubes of the same generation are disjoint. -/
theorem dyadicCube_disjoint {n : ℕ} {k k' : Fin 2 → ℤ} (h : k ≠ k') :
    Disjoint (dyadicCube n k) (dyadicCube n k') := by
  refine Set.disjoint_left.2 fun x hx hx' ↦ h ?_
  rw [← mem_dyadicCube_iff.1 hx, mem_dyadicCube_iff.1 hx']

/-- The index of the parent cube is the index halved. -/
theorem cubeIndex_succ (n : ℕ) (x : Plane) :
    cubeIndex n x = fun i ↦ cubeIndex (n + 1) x i / 2 := by
  funext i
  have h : (2 : ℝ) ^ n * x i = ((2 : ℝ) ^ (n + 1) * x i) / (2 : ℕ) := by
    push_cast
    ring
  rw [cubeIndex, cubeIndex, h, Int.floor_div_natCast]
  norm_num

/-- Each cube is contained in its parent. -/
theorem dyadicCube_succ_subset (n : ℕ) (x : Plane) :
    dyadicCube (n + 1) (cubeIndex (n + 1) x) ⊆ dyadicCube n (cubeIndex n x) := by
  intro y hy
  have hy' : cubeIndex (n + 1) y = cubeIndex (n + 1) x := mem_dyadicCube_iff.1 hy
  refine mem_dyadicCube_iff.2 ?_
  rw [cubeIndex_succ n y, cubeIndex_succ n x, hy']

/-- A generation-`n` cube has diameter at most `√2 / 2ⁿ`. -/
theorem dist_le_of_mem_dyadicCube {n : ℕ} {k : Fin 2 → ℤ} {x y : Plane}
    (hx : x ∈ dyadicCube n k) (hy : y ∈ dyadicCube n k) :
    dist x y ≤ Real.sqrt 2 / (2 : ℝ) ^ n := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hcoord : ∀ i, |x i - y i| < 1 / (2 : ℝ) ^ n := by
    intro i
    have h₁ := hx i
    have h₂ := hy i
    have hd : |(2 : ℝ) ^ n * (x i - y i)| < 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [h₁.1, h₁.2, h₂.1, h₂.2]
    rw [abs_mul, abs_of_pos hpow] at hd
    rw [lt_div_iff₀ hpow, mul_comm]
    exact hd
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist (x i) (y i) ^ 2 ≤ 2 * (1 / (2 : ℝ) ^ n) ^ 2 := by
    have hterm : ∀ i : Fin 2, dist (x i) (y i) ^ 2 ≤ (1 / (2 : ℝ) ^ n) ^ 2 := by
      intro i
      rw [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) (hcoord i).le 2
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin 2, (1 / (2 : ℝ) ^ n) ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 2 * (1 / (2 : ℝ) ^ n) ^ 2 := by
          simp [Finset.sum_const]
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2)
      ≤ Real.sqrt (2 * (1 / (2 : ℝ) ^ n) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 2 / (2 : ℝ) ^ n := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity), mul_one_div]

theorem measurableSet_dyadicCube (n : ℕ) (k : Fin 2 → ℤ) :
    MeasurableSet (dyadicCube n k) := by
  have hset : dyadicCube n k
      = ⋂ i, (fun x : Plane ↦ (2 : ℝ) ^ n * x i) ⁻¹' Ico ((k i : ℝ)) ((k i : ℝ) + 1) := by
    ext x
    simp [dyadicCube, Set.mem_Ico]
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hmeas : Measurable fun x : Plane ↦ (2 : ℝ) ^ n * x i := by fun_prop
  exact hmeas measurableSet_Ico

end FalconerPacking
