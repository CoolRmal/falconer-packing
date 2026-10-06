/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.StrictShellParameters

/-!
# Regular partitions with the initial localization loss already absorbed

The strict margin is fixed before the initial spatial scale. The decomposition below uses
this same margin, so choosing the later regularization block does not restart the parameter
selection or change the localization budget.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- A finite dyadic decomposition of the original measure has actual profiles with a strict
chain-cost margin. All errors are numerical: the original component mass, the block size,
and the two fixed geometric constants. No profile or profile barrier is assumed. -/
theorem exists_regular_dyadic_partition_with_initial_loss
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {s u C A₀ : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hA₀ : 0 ≤ A₀)
    (hC : 0 ≤ C) (hfr : IsFrostman μ s C)
    (hK : MeasurableSet K) (hnull : μ Kᶜ = 0) (hbox : HasUpperBoxBound K u) :
    ∃ c₀ c₁ ε η ζ : ℝ, 0 ≤ c₀ ∧ 0 ≤ c₁ ∧ 0 < ε ∧ 0 < η ∧
      0 < ζ ∧ ζ < 1 / 4 ∧ A₀ * ζ ≤ η / 8 ∧
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
  obtain ⟨η, ζ, ε, hη, hζ, hζ₁, hζloss, hε, M, L₀, hM, hL₀, hchain⟩ :=
    exists_strict_profile_with_initial_loss hs hs' hu hu' hA₀
  refine ⟨c₀, c₁, ε, η, ζ, hc₀, hc₁, hε, hη, hζ, hζ₁, hζloss, M, L₀, hM, hL₀,
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


/-- Compact regular components retain the same strict cost margin after the initial loss
and all block parameters are chosen. The caller may prescribe any sufficiently small
normalization loss and any minimum block size. -/
theorem exists_compact_regular_partition_with_initial_loss
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μ]
    {X : Set (EuclideanSpace ℝ (Fin 2))} {s u C A₀ : ℝ} {q₀ : Fin 2 → ℤ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s) (hA₀ : 0 ≤ A₀)
    (hC : 0 ≤ C) (hfr : IsFrostman μ s C) (hX : IsCompact X)
    (hnull : μ Xᶜ = 0) (hroot : X ⊆ dyadicCube 0 q₀) (hbox : HasUpperBoxBound X u) :
    ∃ η ζ ε : ℝ, 0 < η ∧ 0 < ζ ∧ ζ < 1 / 4 ∧ A₀ * ζ ≤ η / 8 ∧ 0 < ε ∧
      ∃ M : ℕ, 0 < M ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ε / 2 →
      ∀ T₀ : ℕ, ∃ θ : ℝ, 0 < θ ∧ 2 * θ ≤ ρ ∧
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
  obtain ⟨c₀, c₁, ε, η, ζ, hc₀, hc₁, hε, hη, hζ, hζ₁, hζloss,
    M, L₀, hM, hL₀, hpartition⟩ :=
    exists_regular_dyadic_partition_with_initial_loss hs hs' hu hu' hA₀
      hC hfr hX.measurableSet hnull hbox
  refine ⟨η, ζ, ε, hη, hζ, hζ₁, hζloss, hε, M, hM, fun ρ hρ hρε T₀ ↦ ?_⟩
  obtain ⟨θ, hθ, hθρ, T, L₁, hT₀, hT, hL₀L₁, hL₁, hpoly, hparameters⟩ :=
    exists_regularization_parameters_for_barriers hε hρ hρε hc₀ hc₁ T₀ L₀
  refine ⟨θ, hθ, hθρ, T, L₁, hT₀, hT, hL₁, fun L n hL hstart ↦ ?_⟩
  obtain ⟨S, pt, hcover, hpt⟩ := exists_occupiedCubeIndices_and_points hX (T * L)
  have hSroot : ∀ k ∈ S, ancestor (T * L) k = q₀ := by
    intro k hk
    have hx : pt k ∈ dyadicCube (0 + T * L) k := by simpa using (hpt k hk).2
    have hp := mem_dyadicCube_iff.mp (dyadicCube_subset_ancestor 0 (T * L) k hx)
    exact hp.symm.trans (mem_dyadicCube_iff.mp (hroot (hpt k hk).1))
  obtain ⟨herr₀, herr₁, hbudget⟩ := hparameters L hL
  obtain ⟨F, hFd, hF, hrem, hcard⟩ := hpartition S T L n
    ((2 : ℝ) ^ (-(θ * T * L))) (ρ * T * L) hT (hL₀L₁.trans hL)
    (by positivity) (by positivity) hbudget herr₀ herr₁
    (fun x hx y hy ↦ (hSroot x hx).trans (hSroot y hy).symm) hstart
  refine ⟨F, hFd, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨hAS, hmass, hprob, e, he, hreg, hchain⟩ := hF A hA
    have hfactor : (0 : ℝ) < (2 * (2 * T + 1) ^ 2 : ℝ) ^ L := by positivity
    have hmass' : (2 : ℝ) ^ (-(ρ * T * L)) ≤
        μ.real (finiteDyadicUnion (T * L) A) := by
      nlinarith [hbudget.trans hmass]
    exact ⟨hmass', hprob, fun k hk ↦ hSroot k (hAS hk), e, he, hreg, hchain⟩
  · have hnullS : μ (finiteDyadicUnion (T * L) S)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr hcover) hnull
    have hsub : (finiteDyadicUnion (T * L) (F.biUnion id))ᶜ ⊆
        (finiteDyadicUnion (T * L) S \ finiteDyadicUnion (T * L) (F.biUnion id)) ∪
          (finiteDyadicUnion (T * L) S)ᶜ := by
      intro x hx
      by_cases hxS : x ∈ finiteDyadicUnion (T * L) S
      · exact Or.inl ⟨hxS, hx⟩
      · exact Or.inr hxS
    calc
      _ ≤ μ.real ((finiteDyadicUnion (T * L) S \
          finiteDyadicUnion (T * L) (F.biUnion id)) ∪
            (finiteDyadicUnion (T * L) S)ᶜ) := measureReal_mono hsub
      _ ≤ μ.real (finiteDyadicUnion (T * L) S \
          finiteDyadicUnion (T * L) (F.biUnion id)) +
            μ.real (finiteDyadicUnion (T * L) S)ᶜ := measureReal_union_le _ _
      _ = μ.real (finiteDyadicUnion (T * L) S \
          finiteDyadicUnion (T * L) (F.biUnion id)) := by
        simp [measureReal_def, hnullS]
      _ ≤ _ := hrem
  · have hfactor : (2 * (2 * T + 1) ^ 2 : ℝ) ^ L ≤
        (2 : ℝ) ^ (θ * T * L) := by
      rw [Real.rpow_mul_natCast (by norm_num)]
      exact pow_le_pow_left₀ (by positivity) hpoly L
    have hm : μ.real (finiteDyadicUnion (T * L) S) ≤ 1 := measureReal_le_one
    have hbound : (F.card : ℝ) * (2 : ℝ) ^ (-(θ * T * L)) ≤
        (2 : ℝ) ^ (θ * T * L) := by
      exact hcard.trans ((mul_le_mul hfactor hm measureReal_nonneg (by positivity)).trans_eq
        (mul_one _))
    have hproduct : (2 : ℝ) ^ (ρ * T * L) * (2 : ℝ) ^ (-(θ * T * L)) ≥
        (2 : ℝ) ^ (θ * T * L) := by
      rw [← Real.rpow_add (by norm_num)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hθρ
        (show 0 ≤ (T : ℝ) * L by positivity)]
    nlinarith [hbound.trans hproduct,
      show 0 < (2 : ℝ) ^ (-(θ * T * L)) by positivity]

end FalconerPacking
