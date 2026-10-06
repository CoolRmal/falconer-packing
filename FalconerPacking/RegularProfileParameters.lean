/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RegularMeasureProfile
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Choosing regularization parameters

A polynomial cost per regularization block is absorbed in an arbitrarily small exponential
loss by choosing the block size first. At sufficiently large depths, the fixed Frostman and
covering constants are absorbed as well. The resulting partition theorem has no numerical
side conditions supplied by its caller.
-/

@[expose] public section

noncomputable section

open Filter Finset MeasureTheory Set

namespace FalconerPacking

/-- The actual finite-regularization factor is subexponential in the block size. -/
theorem eventually_regularization_factor_le {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ T : ℕ in atTop,
      (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T) := by
  have hb : 0 < θ * Real.log 2 := mul_pos hθ (Real.log_pos (by norm_num))
  have h := (isLittleO_pow_exp_pos_mul_atTop 2 hb).bound
    (show (0 : ℝ) < 1 / 18 by norm_num)
  have h' := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h', eventually_ge_atTop 1] with T hT hT1
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T : ℝ)),
    abs_of_pos (Real.exp_pos _)] at hT
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hexp : Real.exp (θ * Real.log 2 * T) =
      Real.exp (Real.log 2 * (θ * T)) := by congr 1; ring
  rw [hexp] at hT
  nlinarith [sq_nonneg ((T : ℝ) - 1)]

/-- The block size can be chosen arbitrarily large while making its overhead small. -/
theorem exists_regularization_block {θ : ℝ} (hθ : 0 < θ) (T₀ : ℕ) :
    ∃ T : ℕ, T₀ ≤ T ∧ 2 ≤ T ∧ 2 ≤ θ * T ∧
      (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_regularization_factor_le hθ)
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / θ)
  let T := max N (max T₀ (max 2 M))
  have hNT : N ≤ T := le_max_left _ _
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hT2 : 2 ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hMT : M ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hMT' : (M : ℝ) ≤ T := by exact_mod_cast hMT
  refine ⟨T, hT₀, hT2, ?_, hN T hNT⟩
  have hmul := (div_lt_iff₀ hθ).1 hM
  nlinarith

private lemma regularization_power_bound_aux {T : ℕ} {θ : ℝ}
    (hpoly : (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T)) (L : ℕ) :
    (2 * (2 * T + 1) ^ 2 : ℝ) ^ L ≤ (2 : ℝ) ^ (θ * T * L) := by
  rw [Real.rpow_mul_natCast (by norm_num)]
  exact pow_le_pow_left₀ (by positivity) hpoly L

private lemma regularization_budget_aux {T L : ℕ} {θ : ℝ}
    (hpoly : (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T)) :
    (2 * (2 * T + 1) ^ 2 : ℝ) ^ L * (2 : ℝ) ^ (-(2 * θ * T * L)) ≤
      (2 : ℝ) ^ (-(θ * T * L)) := by
  calc
    _ ≤ (2 : ℝ) ^ (θ * T * L) * (2 : ℝ) ^ (-(2 * θ * T * L)) :=
      mul_le_mul_of_nonneg_right (regularization_power_bound_aux hpoly L) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; ring

private lemma regularization_mass_aux {T L : ℕ} {θ m : ℝ}
    (hpoly : (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T)) (hm : 0 ≤ m)
    (hbudget : (2 : ℝ) ^ (-(θ * T * L)) ≤ (2 * (2 * T + 1) ^ 2 : ℝ) ^ L * m) :
    (2 : ℝ) ^ (-(2 * θ * T * L)) ≤ m := by
  have h := hbudget.trans (mul_le_mul_of_nonneg_right
    (regularization_power_bound_aux hpoly L) hm)
  have hpos : 0 < (2 : ℝ) ^ (θ * T * L) := by positivity
  have heq : (2 : ℝ) ^ (θ * T * L) * (2 : ℝ) ^ (-(2 * θ * T * L)) =
      (2 : ℝ) ^ (-(θ * T * L)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  nlinarith

private lemma regularization_card_bound_aux {T L : ℕ} {θ a m : ℝ}
    (hpoly : (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T)) (hm : 0 ≤ m)
    (hcard : a * (2 : ℝ) ^ (-(θ * T * L)) ≤ (2 * (2 * T + 1) ^ 2 : ℝ) ^ L * m) :
    a ≤ (2 : ℝ) ^ (2 * θ * T * L) * m := by
  have hδ : 0 < (2 : ℝ) ^ (-(θ * T * L)) := by positivity
  have hcmp : a * (2 : ℝ) ^ (-(θ * T * L)) ≤
      ((2 : ℝ) ^ (2 * θ * T * L) * m) * (2 : ℝ) ^ (-(θ * T * L)) := by
    calc
      _ ≤ (2 : ℝ) ^ (θ * T * L) * m := hcard.trans
        (mul_le_mul_of_nonneg_right (regularization_power_bound_aux hpoly L) hm)
      _ = ((2 : ℝ) ^ (2 * θ * T * L) * (2 : ℝ) ^ (-(θ * T * L))) * m := by
        rw [← Real.rpow_add (by norm_num)]
        congr 2
        ring
      _ = _ := by ring
  nlinarith

/-- For every requested normalization loss, sufficiently large fixed blocks and depths give
actual regular partitions with exponentially small remainder and strict profile chains.
The chain length and cost margin are chosen before the loss parameter. -/
theorem exists_regular_partition_small_loss
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s u C ζ : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hfr : IsFrostman μ s C)
    (hK : MeasurableSet K) (hnull : μ Kᶜ = 0) (hbox : HasUpperBoxBound K u) :
    ∃ η : ℝ, 0 < η ∧ ∃ M : ℕ, 0 < M ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ T₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ ≤ ρ ∧
        ∃ T L₁ : ℕ, T₀ ≤ T ∧ 2 ≤ T ∧ 0 < L₁ ∧
        ∀ (S : Finset (Fin 2 → ℤ)) (L n : ℕ), L₁ ≤ L →
          (∀ x ∈ S, ∀ y ∈ S, ancestor (T * L) x = ancestor (T * L) y) →
          (n : ℝ) ≤ (1 - ζ) * L →
          ∃ F : Finset (Finset (Fin 2 → ℤ)),
            (↑F : Set (Finset (Fin 2 → ℤ))).PairwiseDisjoint (finiteDyadicUnion (T * L)) ∧
            (∀ A ∈ F, A ⊆ S ∧
              (2 : ℝ) ^ (-(ρ * T * L)) ≤ μ.real (finiteDyadicUnion (T * L) A) ∧
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
              finiteDyadicUnion (T * L) (F.biUnion id)) ≤ (2 : ℝ) ^ (-(θ * T * L)) ∧
            (F.card : ℝ) ≤ (2 : ℝ) ^ (ρ * T * L) *
              μ.real (finiteDyadicUnion (T * L) S) := by
  obtain ⟨c₀, c₁, ε, η, hc₀, hc₁, hε, hη, M, L₀, hM, hL₀, hpartition⟩ :=
    exists_regular_dyadic_partition_with_strict_profiles hs hs' hu hu' hζ
      hC hfr hK hnull hbox
  refine ⟨η, hη, M, hM, fun ρ hρ T₀ ↦ ?_⟩
  let θ := min ε ρ / 8
  have hθ : 0 < θ := div_pos (lt_min hε hρ) (by norm_num)
  have hθε : 4 * θ ≤ ε := by dsimp [θ]; linarith [min_le_left ε ρ]
  have hθρ : 2 * θ ≤ ρ := by dsimp [θ]; linarith [min_le_right ε ρ]
  obtain ⟨T, hT₀, hT, hθT, hpoly⟩ := exists_regularization_block hθ T₀
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hθT' : 0 < θ * T := mul_pos hθ hT'
  obtain ⟨N, hN⟩ := exists_nat_gt (max c₀ c₁ / (θ * T))
  let L₁ := max L₀ N
  have hL₁ : 0 < L₁ := hL₀.trans_le (le_max_left _ _)
  refine ⟨θ, hθ, by linarith, T, L₁, hT₀, hT, hL₁, fun S L n hL hroot hstart ↦ ?_⟩
  have hL₀L : L₀ ≤ L := (le_max_left _ _).trans hL
  have hNL : N ≤ L := (le_max_right _ _).trans hL
  have hNL' : (N : ℝ) ≤ L := by exact_mod_cast hNL
  have hcmax : max c₀ c₁ ≤ θ * T * L := by
    have hmul := (div_lt_iff₀ hθT').1 hN
    nlinarith
  have hc₀L := (le_max_left c₀ c₁).trans hcmax
  have hc₁L := (le_max_right c₀ c₁).trans hcmax
  have herr₀ : (2 * L + c₀ + 2 * θ * T * L) / T ≤ ε * L := by
    rw [div_le_iff₀ hT']
    nlinarith [mul_le_mul_of_nonneg_right hθT (Nat.cast_nonneg L),
      mul_le_mul_of_nonneg_right hθε (mul_nonneg hT'.le (Nat.cast_nonneg L))]
  have herr₁ : (L + c₁) / T ≤ ε * L := by
    rw [div_le_iff₀ hT']
    nlinarith [mul_le_mul_of_nonneg_right hθT (Nat.cast_nonneg L),
      mul_le_mul_of_nonneg_right hθε (mul_nonneg hT'.le (Nat.cast_nonneg L))]
  obtain ⟨F, hFd, hF, hrem, hcard⟩ := hpartition S T L n
    ((2 : ℝ) ^ (-(θ * T * L))) (2 * θ * T * L) hT hL₀L (by positivity)
    (by positivity) (regularization_budget_aux hpoly) herr₀ herr₁ hroot hstart
  have hexp : 2 * θ * T * L ≤ ρ * T * L := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hθρ (Nat.cast_nonneg T)) (Nat.cast_nonneg L)
  refine ⟨F, hFd, ?_, hrem, ?_⟩
  · intro A hA
    obtain ⟨hAS, hmass, hprob, e, he, hreg, hchain⟩ := hF A hA
    refine ⟨hAS, ?_, hprob, e, he, hreg, hchain⟩
    exact ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2
      (neg_le_neg hexp)).trans (regularization_mass_aux hpoly measureReal_nonneg hmass)
  · exact (regularization_card_bound_aux hpoly measureReal_nonneg hcard).trans
      (mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).2 hexp)
        measureReal_nonneg)

private lemma exists_compact_dyadic_cover_in_root_aux
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) {q₀ : Fin 2 → ℤ}
    (hroot : K ⊆ dyadicCube 0 q₀) (N : ℕ) :
    ∃ S : Finset (Fin 2 → ℤ), K ⊆ finiteDyadicUnion N S ∧
      ∀ k ∈ S, ancestor N k = q₀ := by
  obtain ⟨S, pt, hcover, hpt⟩ := exists_occupiedCubeIndices_and_points hK N
  refine ⟨S, hcover, fun k hk ↦ ?_⟩
  have hx : pt k ∈ dyadicCube (0 + N) k := by simpa using (hpt k hk).2
  have hparent := mem_dyadicCube_iff.1 (dyadicCube_subset_ancestor 0 N k hx)
  have hroot' := mem_dyadicCube_iff.1 (hroot (hpt k hk).1)
  exact hparent.symm.trans hroot'

private lemma measureReal_compl_le_remainder_aux
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K X U : Set (EuclideanSpace ℝ (Fin 2))} (hnull : μ Kᶜ = 0) (hcover : K ⊆ X) :
    μ.real Uᶜ ≤ μ.real (X \ U) := by
  have hnullX : μ Xᶜ = 0 := measure_mono_null (compl_subset_compl.2 hcover) hnull
  have hsub : Uᶜ ⊆ (X \ U) ∪ Xᶜ := by
    intro x hx
    by_cases hxX : x ∈ X
    · exact Or.inl ⟨hxX, hx⟩
    · exact Or.inr hxX
  calc
    μ.real Uᶜ ≤ μ.real ((X \ U) ∪ Xᶜ) := measureReal_mono hsub
    _ ≤ μ.real (X \ U) + μ.real Xᶜ := measureReal_union_le _ _
    _ = μ.real (X \ U) := by simp [measureReal_def, hnullX]

/-- A compact probability measure in one unit dyadic cube admits the actual regularized
profiles needed by the improved branch, with arbitrarily small normalization loss.
The initial finite cube cover and every numerical regularization parameter are constructed. -/
theorem exists_compact_regular_partition_strict_profiles
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s u C ζ : ℝ} {q₀ : Fin 2 → ℤ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hζ : 0 < ζ)
    (hC : 0 ≤ C) (hfr : IsFrostman μ s C) (hK : IsCompact K)
    (hnull : μ Kᶜ = 0) (hroot : K ⊆ dyadicCube 0 q₀) (hbox : HasUpperBoxBound K u) :
    ∃ η : ℝ, 0 < η ∧ ∃ M : ℕ, 0 < M ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ T₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧ θ ≤ ρ ∧
        ∃ T L₁ : ℕ, T₀ ≤ T ∧ 2 ≤ T ∧ 0 < L₁ ∧
        ∀ L n : ℕ, L₁ ≤ L → (n : ℝ) ≤ (1 - ζ) * L →
          ∃ F : Finset (Finset (Fin 2 → ℤ)),
            (↑F : Set (Finset (Fin 2 → ℤ))).PairwiseDisjoint (finiteDyadicUnion (T * L)) ∧
            (∀ A ∈ F,
              (2 : ℝ) ^ (-(ρ * T * L)) ≤ μ.real (finiteDyadicUnion (T * L) A) ∧
              IsProbabilityMeasure (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) ∧
              (∀ k ∈ A, ancestor (T * L) k = q₀) ∧
              ∃ e : ℕ → ℕ, (∀ j < L, e j ≤ 2 * T) ∧
                FiniteTreeRegular A
                  (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
                    (dyadicCube (T * L) k)) (ancestor T) L e ∧
                ∃ l : List ℕ, l.length ≤ M ∧
                  List.IsChain (fun n m ↦ m < n ∧ Admissible L m n) (n :: l) ∧
                  chainEnd n l = 0 ∧
                  chainCost (regularBlockProfile T L e) n l ≤ (s - 1 - η) * L) ∧
            μ.real (finiteDyadicUnion (T * L) (F.biUnion id))ᶜ ≤
              (2 : ℝ) ^ (-(θ * T * L)) ∧
            (F.card : ℝ) ≤ (2 : ℝ) ^ (ρ * T * L) := by
  obtain ⟨η, hη, M, hM, hparameters⟩ := exists_regular_partition_small_loss
    hs hs' hu hu' hζ hC hfr hK.measurableSet hnull hbox
  refine ⟨η, hη, M, hM, fun ρ hρ T₀ ↦ ?_⟩
  obtain ⟨θ, hθ, hθρ, T, L₁, hT₀, hT, hL₁, hpartition⟩ := hparameters ρ hρ T₀
  refine ⟨θ, hθ, hθρ, T, L₁, hT₀, hT, hL₁, fun L n hL hstart ↦ ?_⟩
  obtain ⟨S, hcover, hSroot⟩ := exists_compact_dyadic_cover_in_root_aux hK hroot (T * L)
  obtain ⟨F, hFd, hF, hrem, hcard⟩ := hpartition S L n hL
    (fun x hx y hy ↦ (hSroot x hx).trans (hSroot y hy).symm) hstart
  refine ⟨F, hFd, ?_, (measureReal_compl_le_remainder_aux hnull hcover).trans hrem, ?_⟩
  · intro A hA
    obtain ⟨hAS, hmass, hprob, e, he, hreg, hchain⟩ := hF A hA
    exact ⟨hmass, hprob, fun k hk ↦ hSroot k (hAS hk), e, he, hreg, hchain⟩
  · have hμS : μ.real (finiteDyadicUnion (T * L) S) ≤ 1 := measureReal_le_one
    apply hcard.trans
    simpa using mul_le_mul_of_nonneg_left hμS
      (show 0 ≤ (2 : ℝ) ^ (ρ * T * L) by positivity)

end FalconerPacking
