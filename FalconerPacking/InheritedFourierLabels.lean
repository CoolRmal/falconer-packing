/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.FiniteFourierOrthogonality

/-!
# Exact regrouping of surviving Fourier labels

Terminal labels are grouped by their ancestors. A current mark is constant on each
current label, while later marks are retained inside the inherited function. Regrouping
these finite sums gives the exact identity used by selected-cap inflation.
-/

@[expose] public section

noncomputable section

open Classical

namespace FalconerPacking

/-- The sum of retained terminal functions with the specified ancestor label. -/
def inheritedLabelSum {ι κ V : Type*} [AddCommMonoid V]
    (I : Finset ι) (label : ι → κ) (θ : κ) (keep : ι → Prop) (f : ι → V) : V :=
  ∑ i ∈ I.filter (fun i ↦ label i = θ ∧ keep i), f i

/-- Regrouping preserves exactly the selected labels, including arbitrary later marks. -/
theorem inheritedLabelSum_regroup {ι κ α V : Type*} [AddCommMonoid V]
    (I : Finset ι) (J : Finset κ) (label : ι → κ) (parent : κ → α)
    (hlabel : ∀ i ∈ I, label i ∈ J) (a : α)
    (good : κ → Prop) (keep : ι → Prop) (f : ι → V) :
    inheritedLabelSum I (parent ∘ label) a (fun i ↦ good (label i) ∧ keep i) f =
      ∑ θ ∈ J.filter (fun θ ↦ parent θ = a ∧ good θ),
        inheritedLabelSum I label θ keep f := by
  have hi (θ : κ) : I.filter (fun i ↦ label i = θ ∧ keep i) =
      (I.filter keep).filter (fun i ↦ label i = θ) := by
    ext i
    simp only [Finset.mem_filter]
    tauto
  simp only [inheritedLabelSum, hi]
  rw [Finset.sum_fiberwise_eq_sum_filter (I.filter keep)
    (J.filter (fun θ ↦ parent θ = a ∧ good θ)) label f]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Function.comp_apply]
    constructor
    · rintro ⟨hi, hp, hg, hk⟩
      exact ⟨⟨hi, hk⟩, hlabel i hi, hp, hg⟩
    · rintro ⟨⟨hi, hk⟩, _, hp, hg⟩
      exact ⟨hi, hp, hg, hk⟩
  · intro i hi
    rfl

/-- A terminal label survives exactly when every remaining ancestor mark permits it. -/
def survivesFrom {ι κ : Type*} (label : ℕ → ι → κ)
    (good : ℕ → κ → Prop) (j K : ℕ) (i : ι) : Prop :=
  ∀ k, j ≤ k → k < K → good k (label k i)

theorem survivesFrom_succ {ι κ : Type*} (label : ℕ → ι → κ)
    (good : ℕ → κ → Prop) {j K : ℕ} (hj : j < K) (i : ι) :
    survivesFrom label good j K i ↔
      good j (label j i) ∧ survivesFrom label good (j + 1) K i := by
  constructor
  · intro h
    exact ⟨h j le_rfl hj, fun k hk hK ↦ h k (by omega) hK⟩
  · rintro ⟨h, hs⟩ k hk hK
    rcases eq_or_lt_of_le hk with rfl | hk
    · exact h
    · exact hs k (by omega) hK

@[simp]
theorem survivesFrom_terminal {ι κ : Type*} (label : ℕ → ι → κ)
    (good : ℕ → κ → Prop) (K : ℕ) (i : ι) : survivesFrom label good K K i := by
  intro k hk hK
  omega

/-- The inherited identity follows from the definitions of survival and ancestry. -/
theorem inheritedLabelSum_chain_step {ι κ α V : Type*} [AddCommMonoid V]
    (I : Finset ι) (J : Finset κ) (label : ℕ → ι → κ) (parent : κ → α)
    (good : ℕ → κ → Prop) (j K : ℕ) (hj : j < K)
    (hlabel : ∀ i ∈ I, label j i ∈ J) (a : α) (f : ι → V) :
    inheritedLabelSum I (parent ∘ label j) a (survivesFrom label good j K) f =
      ∑ θ ∈ J.filter (fun θ ↦ parent θ = a ∧ good j θ),
        inheritedLabelSum I (label j) θ (survivesFrom label good (j + 1) K) f := by
  have he : survivesFrom label good j K =
      (fun i ↦ good j (label j i) ∧ survivesFrom label good (j + 1) K i) := by
    funext i
    exact propext (survivesFrom_succ label good hj i)
  rw [he]
  exact inheritedLabelSum_regroup I J (label j) parent hlabel a
    (good j) (survivesFrom label good (j + 1) K) f

/-- Finite inherited sums inherit an actual common Fourier support. -/
theorem fourier_support_inheritedLabelSum {ι κ : Type*}
    (I : Finset ι) (label : ι → κ) (θ : κ) (keep : ι → Prop)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (hf : ∀ i ∈ I, label i = θ → keep i →
      Function.support (fun z ↦ FourierTransform.fourier (f i) z) ⊆ S) :
    Function.support (fun z ↦
      FourierTransform.fourier (inheritedLabelSum I label θ keep f) z) ⊆ S := by
  intro z hz
  by_contra hS
  apply hz
  change (SchwartzMap.fourierTransformCLM ℂ
    (∑ i ∈ I.filter (fun i ↦ label i = θ ∧ keep i), f i)) z = 0
  rw [map_sum]
  simp only [sum_apply]
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hi, hθ, hk⟩ := Finset.mem_filter.mp hi
  exact Function.notMem_support.mp (fun h ↦ hS (hf i hi hθ hk h))

end FalconerPacking
