/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.FiniteRegularization
public import FalconerPacking.OccupiedCubes
public import FalconerPacking.StrictFiniteProfile

/-!
# Profiles of regularized original measures

The profile is the cumulative sum of the exponents produced by finite regularization, read
from the root toward the leaves. The factor-eight regularity errors accumulate linearly in
the number of blocks. Frostman and covering estimates then give its two affine barriers.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory Set

namespace FalconerPacking

/-- Cumulative branching exponent, read from the root of a depth-`L` regular tree. -/
def regularProfileExponent (L : ℕ) (e : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (e (L - 1 - i) : ℝ)

/-- The profile on the block grid, with its linear part subtracted. -/
def regularBlockProfile (T L : ℕ) (e : ℕ → ℕ) (j : ℕ) : ℝ :=
  regularProfileExponent L e j / T - j

@[simp] theorem regularProfileExponent_zero (L : ℕ) (e : ℕ → ℕ) :
    regularProfileExponent L e 0 = 0 := by simp [regularProfileExponent]

theorem regularProfileExponent_succ (L : ℕ) (e : ℕ → ℕ) (j : ℕ) :
    regularProfileExponent L e (j + 1) =
      regularProfileExponent L e j + e (L - 1 - j) := by
  simp [regularProfileExponent, sum_range_succ]

@[simp] theorem regularBlockProfile_zero (T L : ℕ) (e : ℕ → ℕ) :
    regularBlockProfile T L e 0 = 0 := by simp [regularBlockProfile]

theorem regularBlockProfile_lipschitz {T L : ℕ} (hT : 0 < T) {e : ℕ → ℕ}
    (he : ∀ j < L, e j ≤ 2 * T) :
    ∀ j < L, |regularBlockProfile T L e (j + 1) - regularBlockProfile T L e j| ≤ 1 := by
  intro j hj
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have he' : (e (L - 1 - j) : ℝ) ≤ 2 * T := by
    exact_mod_cast he (L - 1 - j) (by omega)
  have hnonneg : (0 : ℝ) ≤ e (L - 1 - j) := Nat.cast_nonneg _
  rw [regularBlockProfile, regularBlockProfile, regularProfileExponent_succ]
  push_cast
  rw [abs_le]
  constructor <;> field_simp <;> nlinarith

private lemma profile_lower_step_power_aux (L : ℕ) (e : ℕ → ℕ) (j : ℕ) :
    (4 * (2 : ℝ) ^ e (L - 1 - j)) *
        (2 : ℝ) ^ (-regularProfileExponent L e (j + 1) - 2 * (j + 1)) =
      (2 : ℝ) ^ (-regularProfileExponent L e j - 2 * j) := by
  rw [regularProfileExponent_succ, ← Real.rpow_natCast (2 : ℝ),
    show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
    ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  ring

private lemma profile_upper_step_power_aux (L : ℕ) (e : ℕ → ℕ) (j : ℕ) :
    (2 : ℝ) ^ e (L - 1 - j) *
        (2 : ℝ) ^ (-regularProfileExponent L e (j + 1) + (j + 1)) =
      2 * (2 : ℝ) ^ (-regularProfileExponent L e j + j) := by
  rw [regularProfileExponent_succ, ← Real.rpow_natCast (2 : ℝ),
    ← Real.rpow_add (by norm_num)]
  have hexp : (e (L - 1 - j) : ℝ) +
      (-(regularProfileExponent L e j + e (L - 1 - j)) + (j + 1)) =
      1 + (-regularProfileExponent L e j + j) := by ring
  rw [hexp, Real.rpow_add (by norm_num), Real.rpow_one]

private lemma regular_sequence_mass_bounds_aux (L : ℕ) (e : ℕ → ℕ) (M : ℕ → ℝ)
    (hM : M 0 = 1)
    (hstep : ∀ j < L,
      2 ^ e (L - 1 - j) * M (j + 1) ≤ 2 * M j ∧
      M j ≤ 4 * 2 ^ e (L - 1 - j) * M (j + 1)) :
    ∀ j ≤ L, (2 : ℝ) ^ (-regularProfileExponent L e j - 2 * j) ≤ M j ∧
      M j ≤ (2 : ℝ) ^ (-regularProfileExponent L e j + j) := by
  intro j hj
  induction j with
  | zero => simp [hM]
  | succ j ih =>
    obtain ⟨hlo, hhi⟩ := ih (by omega)
    obtain ⟨hstep₁, hstep₂⟩ := hstep j (by omega)
    have hp : 0 < (2 : ℝ) ^ e (L - 1 - j) := by positivity
    have hloeq := profile_lower_step_power_aux L e j
    have hhieq := profile_upper_step_power_aux L e j
    simp only [Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith

variable {α : Type*} [DecidableEq α]

/-- Actual regular tree masses satisfy the cumulative profile estimates. -/
theorem FiniteTreeRegular.profile_mass_bounds
    {A : Finset α} {w : α → ℝ} {p : α → α} {L : ℕ} {e : ℕ → ℕ}
    (hreg : FiniteTreeRegular A w p L e) (hroot : ∀ x ∈ A, ∀ y ∈ A, p^[L] x = p^[L] y)
    (hmass : ∑ x ∈ A, w x = 1) {x : α} (hx : x ∈ A) :
    ∀ j ≤ L,
      (2 : ℝ) ^ (-regularProfileExponent L e j - 2 * j) ≤
          finiteTreeMass A w p (L - j) (p^[L - j] x) ∧
      finiteTreeMass A w p (L - j) (p^[L - j] x) ≤
          (2 : ℝ) ^ (-regularProfileExponent L e j + j) := by
  apply regular_sequence_mass_bounds_aux L e
    (fun j ↦ finiteTreeMass A w p (L - j) (p^[L - j] x))
  · simp only [Nat.sub_zero, finiteTreeMass]
    rw [filter_eq_self.2 (fun y hy ↦ hroot y hy x hx)]
    exact hmass
  · intro j hj
    have h := hreg (L - 1 - j) (by omega) x hx
    have h₁ : L - 1 - j = L - (j + 1) := by omega
    have h₂ : L - (j + 1) + 1 = L - j := by omega
    simpa only [h₂, h₁] using h

/-- A power upper bound for one occupied mass gives the lower profile barrier. -/
theorem FiniteTreeRegular.profile_lower_barrier
    {A : Finset α} {w : α → ℝ} {p : α → α} {L : ℕ} {e : ℕ → ℕ}
    (hreg : FiniteTreeRegular A w p L e) (hroot : ∀ x ∈ A, ∀ y ∈ A, p^[L] x = p^[L] y)
    (hmass : ∑ x ∈ A, w x = 1) {j : ℕ} (hj : j ≤ L) {v : ℝ}
    (hupper : ∀ x ∈ A, finiteTreeMass A w p (L - j) (p^[L - j] x) ≤ (2 : ℝ) ^ (-v)) :
    v - 2 * j ≤ regularProfileExponent L e j := by
  have hA : A.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty.1 h, sum_empty] at hmass
    norm_num at hmass
  obtain ⟨x, hx⟩ := hA
  have h := (hreg.profile_mass_bounds hroot hmass hx j hj).1.trans (hupper x hx)
  have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 h
  linarith

/-- Counting the occupied cubes gives the upper profile barrier. -/
theorem FiniteTreeRegular.profile_upper_barrier
    {A : Finset α} {w : α → ℝ} {p : α → α} {L : ℕ} {e : ℕ → ℕ}
    (hreg : FiniteTreeRegular A w p L e) (hroot : ∀ x ∈ A, ∀ y ∈ A, p^[L] x = p^[L] y)
    (hmass : ∑ x ∈ A, w x = 1) {j : ℕ} (hj : j ≤ L) {v : ℝ}
    (hcard : ((A.image (p^[L - j])).card : ℝ) ≤ (2 : ℝ) ^ v) :
    regularProfileExponent L e j ≤ v + j := by
  have hsum : (∑ q ∈ A.image (p^[L - j]), finiteTreeMass A w p (L - j) q) = 1 := by
    unfold finiteTreeMass
    rw [sum_fiberwise_of_maps_to (fun x hx ↦ mem_image_of_mem _ hx) w]
    exact hmass
  have hbound : 1 ≤ (A.image (p^[L - j])).card *
      (2 : ℝ) ^ (-regularProfileExponent L e j + j) := by
    rw [← hsum]
    calc
      _ ≤ ∑ _q ∈ A.image (p^[L - j]),
          (2 : ℝ) ^ (-regularProfileExponent L e j + j) := by
        apply sum_le_sum
        intro q hq
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hq
        exact (hreg.profile_mass_bounds hroot hmass hx j hj).2
      _ = _ := by simp
  have hpower : (2 : ℝ) ^ (0 : ℝ) ≤
      (2 : ℝ) ^ (v + (-regularProfileExponent L e j + j)) := by
    rw [Real.rpow_zero, Real.rpow_add (by norm_num)]
    exact hbound.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 hpower
  linarith

private lemma ancestor_iterate_profile_aux (T j : ℕ) :
    (ancestor T)^[j] = ancestor (T * j) := by
  funext x
  induction j with
  | zero => simp [ancestor_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, ancestor_ancestor, Nat.mul_succ]
    congr 1
    omega

private lemma normalized_component_mass_sum_aux
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (n : ℕ) (A : Finset (Fin 2 → ℤ)) (hA : μ (finiteDyadicUnion n A) ≠ 0) :
    ∑ k ∈ A, (normalizedRestrict μ (finiteDyadicUnion n A)).real (dyadicCube n k) = 1 := by
  haveI := isProbabilityMeasure_normalizedRestrict (measurableSet_finiteDyadicUnion n A)
    hA (measure_ne_top μ _)
  rw [← measureReal_finiteDyadicUnion, measureReal_def,
    normalizedRestrict_apply _ _ _ (measurableSet_finiteDyadicUnion n A), Set.inter_self,
    ENNReal.inv_mul_cancel hA (measure_ne_top μ _), ENNReal.toReal_one]

private lemma normalized_component_tree_mass_aux
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (T L j : ℕ) (hj : j ≤ L) (A : Finset (Fin 2 → ℤ)) (q : Fin 2 → ℤ)
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0) :
    finiteTreeMass A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) (L - j) q =
      (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real (dyadicCube (T * j) q) := by
  haveI := isProbabilityMeasure_normalizedRestrict (measurableSet_finiteDyadicUnion _ _)
    hA (measure_ne_top μ _)
  rw [finiteTreeMass_dyadic_eq _ _ _ _ (Nat.mul_le_mul_left T (Nat.sub_le L j))]
  have hdepth : T * L - T * (L - j) = T * j := by
    rw [Nat.mul_sub, Nat.sub_sub_self (Nat.mul_le_mul_left T hj)]
  rw [hdepth]
  simp only [measureReal_def, normalizedRestrict_apply _ _ _
      ((measurableSet_finiteDyadicUnion _ _).inter (measurableSet_dyadicCube _ _)),
    normalizedRestrict_apply _ _ _ (measurableSet_dyadicCube _ _)]
  congr 3
  ext x
  simp only [Set.mem_inter_iff]
  tauto

/-- The original normalized component has the cube-mass bounds required by the analytic argument. -/
theorem normalized_regular_component_cube_bounds
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {j : ℕ} (hj : j ≤ L) {x : Fin 2 → ℤ} (hx : x ∈ A) :
    (2 : ℝ) ^ (-regularProfileExponent L e j - 2 * j) ≤
        (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
          (dyadicCube (T * j) (ancestor (T * (L - j)) x)) ∧
      (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
          (dyadicCube (T * j) (ancestor (T * (L - j)) x)) ≤
        (2 : ℝ) ^ (-regularProfileExponent L e j + j) := by
  have h := hreg.profile_mass_bounds
    (by simpa only [ancestor_iterate_profile_aux] using hroot)
    (normalized_component_mass_sum_aux μ (T * L) A hA) hx j hj
  rw [normalized_component_tree_mass_aux μ T L j hj A _ hA,
    ancestor_iterate_profile_aux] at h
  exact h

private lemma exists_nonneg_power_exponent_aux (C : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ C ≤ (2 : ℝ) ^ c := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (show (1 : ℝ) < 2 by norm_num)
  exact ⟨n, Nat.cast_nonneg n, by simpa only [Real.rpow_natCast] using hn.le⟩

/-- Frostman's ball estimate gives a cube-mass exponent with a uniform additive constant. -/
theorem exists_frostman_dyadic_power_bound
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hfr : IsFrostman μ s C) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, 2 ≤ n → ∀ q : Fin 2 → ℤ,
      μ.real (dyadicCube n q) ≤ (2 : ℝ) ^ (c - s * n) := by
  obtain ⟨c, hc, hpow⟩ := exists_nonneg_power_exponent_aux (C * (2 * Real.sqrt 2) ^ s)
  refine ⟨c, hc, fun n hn q ↦ ?_⟩
  have hμ := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (measure_dyadicCube_le_of_isFrostman hs hfr hn q)
  rw [ENNReal.toReal_ofReal (by positivity)] at hμ
  calc
    μ.real (dyadicCube n q) ≤ C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ s := hμ
    _ = (C * (2 * Real.sqrt 2) ^ s) * (2 : ℝ) ^ (-(n : ℝ) * s) := by
      rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by norm_num),
        div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
      rw [neg_mul]
      ring
    _ ≤ (2 : ℝ) ^ c * (2 : ℝ) ^ (-(n : ℝ) * s) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (2 : ℝ) ^ (c - s * n) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      ring

/-- A box-covering estimate gives cube covers with a uniform additive counting exponent. -/
theorem exists_dyadic_cover_power_bound
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u : ℝ} (hK : HasUpperBoxBound K u) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ, ∃ Q : Finset (Fin 2 → ℤ),
      K ⊆ finiteDyadicUnion n Q ∧ (Q.card : ℝ) ≤ (2 : ℝ) ^ (u * n + c) := by
  obtain ⟨C, hC, hcover⟩ := exists_occupiedCubeIndices_card_le_of_hasUpperBoxBound hK
  obtain ⟨c, hc, hpow⟩ := exists_nonneg_power_exponent_aux (4 * C * (2 : ℝ) ^ u)
  refine ⟨c, hc, fun n ↦ ?_⟩
  obtain ⟨Q, hQ, hQc⟩ := hcover n
  refine ⟨Q, hQ, hQc.trans ?_⟩
  calc
    4 * C * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) =
        (4 * C * (2 : ℝ) ^ u) * (2 : ℝ) ^ (u * n) := by
      rw [show (((n + 1 : ℕ) : ℝ) * u) = u + u * n by push_cast; ring,
        Real.rpow_add (by norm_num)]
      ring
    _ ≤ (2 : ℝ) ^ c * (2 : ℝ) ^ (u * n) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num), add_comm]

/-- Component normalization costs exactly its reciprocal mass in the dyadic power bound. -/
theorem normalizedRestrict_dyadic_power_bound
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {X : Set (EuclideanSpace ℝ (Fin 2))} {n : ℕ} {q : Fin 2 → ℤ} {v τ : ℝ}
    (hmass : (2 : ℝ) ^ (-τ) ≤ μ.real X)
    (hμ : μ.real (dyadicCube n q) ≤ (2 : ℝ) ^ v) :
    (normalizedRestrict μ X).real (dyadicCube n q) ≤ (2 : ℝ) ^ (v + τ) := by
  have hpos : 0 < μ.real X := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hmass
  have hinv : (μ.real X)⁻¹ ≤ (2 : ℝ) ^ τ := by
    have h := inv_anti₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hmass
    simpa only [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv] using h
  rw [measureReal_def, normalizedRestrict_apply _ _ _ (measurableSet_dyadicCube n q),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  calc
    (μ X).toReal⁻¹ * (μ (dyadicCube n q ∩ X)).toReal ≤
        (2 : ℝ) ^ τ * (2 : ℝ) ^ v :=
      mul_le_mul hinv ((measureReal_mono Set.inter_subset_left).trans hμ)
        measureReal_nonneg (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num), add_comm]

private lemma cubeIndex_mem_cover_of_measure_pos_aux
    {σ : Measure (EuclideanSpace ℝ (Fin 2))}
    {K : Set (EuclideanSpace ℝ (Fin 2))} {Q : Finset (Fin 2 → ℤ)} {n : ℕ}
    {q : Fin 2 → ℤ} (hnull : σ Kᶜ = 0) (hcover : K ⊆ finiteDyadicUnion n Q)
    (hpos : 0 < σ.real (dyadicCube n q)) : q ∈ Q := by
  have hmeet : (K ∩ dyadicCube n q).Nonempty := by
    by_contra h
    have hsub : dyadicCube n q ⊆ Kᶜ := by
      intro x hx hxK
      exact h ⟨x, hxK, hx⟩
    have hz := measure_mono_null hsub hnull
    simp [measureReal_def, hz] at hpos
  obtain ⟨x, hxK, hxq⟩ := hmeet
  have hxQ := mem_finiteDyadicUnion_iff.1 (hcover hxK)
  rwa [(mem_dyadicCube_iff.1 hxq)] at hxQ

/-- All occupied ancestors of an actual regular component occur in every cube cover of
its conull source set. -/
theorem normalized_regular_component_ancestors_subset
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K) (hnull : μ Kᶜ = 0)
    {T L : ℕ} {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {j : ℕ} (hj : j ≤ L) {Q : Finset (Fin 2 → ℤ)}
    (hcover : K ⊆ finiteDyadicUnion (T * j) Q) :
    A.image ((ancestor T)^[L - j]) ⊆ Q := by
  have hnull' : normalizedRestrict μ (finiteDyadicUnion (T * L) A) Kᶜ = 0 := by
    rw [normalizedRestrict_apply _ _ _ hK.compl,
      measure_mono_null Set.inter_subset_left hnull, mul_zero]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hq
  rw [ancestor_iterate_profile_aux]
  apply cubeIndex_mem_cover_of_measure_pos_aux hnull' hcover
  exact (Real.rpow_pos_of_pos (by norm_num) _).trans_le
    (normalized_regular_component_cube_bounds μ hA hreg hroot hj hx).1

/-- Dimension estimates give the unscaled barriers of an actual normalized component.
The parameter `τ` is an explicit lower bound for its original mass, not its normalized mass. -/
theorem normalized_regular_component_exponent_barriers
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : MeasurableSet K) (hnull : μ Kᶜ = 0)
    {s u c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hfr : ∀ n : ℕ, 2 ≤ n → ∀ q : Fin 2 → ℤ,
      μ.real (dyadicCube n q) ≤ (2 : ℝ) ^ (c₀ - s * n))
    (hcover : ∀ n : ℕ, ∃ Q : Finset (Fin 2 → ℤ),
      K ⊆ finiteDyadicUnion n Q ∧ (Q.card : ℝ) ≤ (2 : ℝ) ^ (u * n + c₁))
    {T L : ℕ} (hT : 2 ≤ T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ} {τ : ℝ}
    (hτ : 0 ≤ τ) (hmass : (2 : ℝ) ^ (-τ) ≤ μ.real (finiteDyadicUnion (T * L) A))
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {j : ℕ} (hj : j ≤ L) :
    s * T * j - 2 * j - c₀ - τ ≤ regularProfileExponent L e j ∧
      regularProfileExponent L e j ≤ u * T * j + j + c₁ := by
  have hpos : 0 < μ.real (finiteDyadicUnion (T * L) A) :=
    (Real.rpow_pos_of_pos (by norm_num) _).trans_le hmass
  have hA : μ (finiteDyadicUnion (T * L) A) ≠ 0 := by
    intro hz
    simp [measureReal_def, hz] at hpos
  have hroot' : ∀ x ∈ A, ∀ y ∈ A,
      (ancestor T)^[L] x = (ancestor T)^[L] y := by
    simpa only [ancestor_iterate_profile_aux] using hroot
  have htotal := normalized_component_mass_sum_aux μ (T * L) A hA
  constructor
  · by_cases hj0 : j = 0
    · simp only [hj0, Nat.cast_zero, mul_zero, sub_zero, regularProfileExponent_zero]
      linarith
    · have hjpos : 1 ≤ j := by omega
      have hdepth : 2 ≤ T * j := hT.trans (Nat.le_mul_of_pos_right T hjpos)
      have hbound := hreg.profile_lower_barrier hroot' htotal hj
        (v := s * T * j - c₀ - τ) (fun x hx ↦ ?_)
      · linarith
      · rw [normalized_component_tree_mass_aux μ T L j hj A _ hA]
        have h := normalizedRestrict_dyadic_power_bound hmass
          (hfr (T * j) hdepth ((ancestor T)^[L - j] x))
        convert h using 1
        push_cast
        congr 1
        ring
  · obtain ⟨Q, hQ, hQc⟩ := hcover (T * j)
    have hcardle := Finset.card_le_card
      (normalized_regular_component_ancestors_subset μ hK hnull hA hreg hroot hj hQ)
    have hcard : ((A.image ((ancestor T)^[L - j])).card : ℝ) ≤
        (2 : ℝ) ^ (u * (T * j) + c₁) :=
      (Nat.cast_le.2 hcardle).trans (by simpa only [Nat.cast_mul] using hQc)
    have hbound := hreg.profile_upper_barrier hroot' htotal hj hcard
    linarith

/-- Frostman and upper box bounds give uniform constants for the profiles of all actual
regular components. The displayed errors include both regularization and normalization. -/
theorem exists_regular_component_profile_barriers
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s u C : ℝ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hfr : IsFrostman μ s C)
    (hK : MeasurableSet K) (hnull : μ Kᶜ = 0) (hbox : HasUpperBoxBound K u) :
    ∃ c₀ c₁ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧
      ∀ (T L : ℕ) (A : Finset (Fin 2 → ℤ)) (e : ℕ → ℕ) (τ : ℝ),
        2 ≤ T → 0 ≤ τ → (2 : ℝ) ^ (-τ) ≤ μ.real (finiteDyadicUnion (T * L) A) →
        FiniteTreeRegular A
          (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
            (dyadicCube (T * L) k)) (ancestor T) L e →
        (∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y) →
        (∀ j ≤ L, (s - 1) * j - (2 * L + c₀ + τ) / T ≤ regularBlockProfile T L e j) ∧
        (∀ j ≤ L, regularBlockProfile T L e j ≤ (u - 1) * j + (L + c₁) / T) := by
  obtain ⟨c₀, hc₀, hfr'⟩ := exists_frostman_dyadic_power_bound hs hC hfr
  obtain ⟨c₁, hc₁, hcover⟩ := exists_dyadic_cover_power_bound hbox
  refine ⟨c₀, c₁, hc₀, hc₁, fun T L A e τ hT hτ hmass hreg hroot ↦ ?_⟩
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  constructor
  · intro j hj
    have h := (normalized_regular_component_exponent_barriers μ hK hnull hc₀ hfr'
      hcover hT hτ hmass hreg hroot hj).1
    have hj' : (j : ℝ) ≤ L := by exact_mod_cast hj
    dsimp [regularBlockProfile]
    rw [le_sub_iff_add_le, le_div_iff₀ hT']
    field_simp
    nlinarith
  · intro j hj
    have h := (normalized_regular_component_exponent_barriers μ hK hnull hc₀ hfr'
      hcover hT hτ hmass hreg hroot hj).2
    have hj' : (j : ℝ) ≤ L := by exact_mod_cast hj
    dsimp [regularBlockProfile]
    rw [sub_le_iff_le_add, div_le_iff₀ hT']
    field_simp
    nlinarith

/-- A finite dyadic decomposition of the original measure has actual profiles with a strict
chain-cost margin. All errors are numerical: the original component mass, the block size,
and the two fixed geometric constants. No profile or profile barrier is assumed. -/
theorem exists_regular_dyadic_partition_with_strict_profiles
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s u C ζ : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hfr : IsFrostman μ s C)
    (hK : MeasurableSet K) (hnull : μ Kᶜ = 0) (hbox : HasUpperBoxBound K u) :
    ∃ c₀ c₁ ε η : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 < ε ∧ 0 < η ∧
      ∃ M L₀ : ℕ, 0 < M ∧ 0 < L₀ ∧
      ∀ (S : Finset (Fin 2 → ℤ)) (T L n : ℕ) (δ τ : ℝ),
        2 ≤ T → L₀ ≤ L → 0 < δ → 0 ≤ τ →
        (2 * (2 * T + 1) ^ 2 : ℝ) ^ L * (2 : ℝ) ^ (-τ) ≤ δ →
        (2 * L + c₀ + τ) / T ≤ ε * L → (L + c₁) / T ≤ ε * L →
        (∀ x ∈ S, ∀ y ∈ S, ancestor (T * L) x = ancestor (T * L) y) →
        (n : ℝ) ≤ (1 - ζ) * L →
        ∃ F : Finset (Finset (Fin 2 → ℤ)),
          (↑F : Set (Finset (Fin 2 → ℤ))).PairwiseDisjoint (finiteDyadicUnion (T * L)) ∧
          (∀ A ∈ F, A ⊆ S ∧
            δ ≤ (2 * (2 * T + 1) ^ 2) ^ L * μ.real (finiteDyadicUnion (T * L) A) ∧
            IsProbabilityMeasure (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) ∧
            ∃ e : ℕ → ℕ, (∀ j < L, e j ≤ 2 * T) ∧
              FiniteTreeRegular A
                (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
                  (dyadicCube (T * L) k)) (ancestor T) L e ∧
              ∃ l : List ℕ, l.length ≤ M ∧
                List.IsChain (fun n m ↦ m < n ∧ Admissible L m n) (n :: l) ∧
                chainEnd n l = 0 ∧
                chainCost (regularBlockProfile T L e) n l ≤ (s - 1 - η) * L) ∧
          μ.real (finiteDyadicUnion (T * L) S \
            finiteDyadicUnion (T * L) (F.biUnion id)) ≤ δ ∧
          (F.card : ℝ) * δ ≤
            (2 * (2 * T + 1) ^ 2) ^ L * μ.real (finiteDyadicUnion (T * L) S) := by
  obtain ⟨c₀, c₁, hc₀, hc₁, hbarriers⟩ :=
    exists_regular_component_profile_barriers (by linarith : 0 ≤ s) hC hfr hK hnull hbox
  obtain ⟨ε, η, hε, hη, M, L₀, hM, hL₀, hchain⟩ :=
    exists_strict_uniform_finite_profile hs hs' hu hu' hζ
  refine ⟨c₀, c₁, ε, η, hc₀, hc₁, hε, hη, M, L₀, hM, hL₀,
    fun S T L n δ τ hT hL hδ hτ hbudget herr₀ herr₁ hroot hstart ↦ ?_⟩
  obtain ⟨F, hFd, hF, hrem, hcard⟩ :=
    exists_normalized_regular_dyadic_measure_partition μ S T L hδ
  refine ⟨F, hFd, ?_, hrem, hcard⟩
  intro A hA
  obtain ⟨hAS, hmass, hprob, e, he, hreg⟩ := hF A hA
  have hmass' : (2 : ℝ) ^ (-τ) ≤ μ.real (finiteDyadicUnion (T * L) A) := by
    have hfactor : (0 : ℝ) < (2 * (2 * T + 1) ^ 2 : ℝ) ^ L := by positivity
    nlinarith [hbudget.trans hmass]
  have hroot' : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y :=
    fun x hx y hy ↦ hroot x (hAS hx) y (hAS hy)
  obtain ⟨hlo, hup⟩ := hbarriers T L A e τ hT hτ hmass' hreg hroot'
  refine ⟨hAS, hmass, hprob, e, he, hreg, ?_⟩
  apply hchain L n (regularBlockProfile T L e) hL
    (regularBlockProfile_lipschitz (by omega) he) _ _ hstart
  · intro j hj
    exact (by linarith [hlo j hj])
  · intro j hj
    exact (by linarith [hup j hj])

end FalconerPacking
