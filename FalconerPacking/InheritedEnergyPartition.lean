/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InheritedFourierLabels

/-!
# Summing inherited angular energies without counting parent labels

Restriction to a parent label is already inside each inherited terminal sum. At each
current label exactly one parent restriction survives, so both localized energies and
global error energies sum exactly, with no factor counting angular parents.
-/

noncomputable section

open MeasureTheory Classical
open scoped ENNReal

namespace FalconerPacking

/-- Restricting terminal descendants to an angular parent is an exact zero-or-original operation. -/
theorem inheritedLabelSum_parent_restriction {ι κ α V : Type*} [AddCommMonoid V]
    (I : Finset ι) (label : ι → κ) (parent : κ → α) (a : α) (θ : κ)
    (keep : ι → Prop) (f : ι → V) :
    inheritedLabelSum I label θ (fun i ↦ parent (label i) = a ∧ keep i) f =
      if parent θ = a then inheritedLabelSum I label θ keep f else 0 := by
  by_cases ha : parent θ = a
  · simp only [if_pos ha, inheritedLabelSum]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi, hθ, _, hk⟩
        exact ⟨hi, hθ, hk⟩
      · rintro ⟨hi, hθ, hk⟩
        exact ⟨hi, hθ, hθ ▸ ha, hk⟩
    · intro i _
      rfl
  · simp only [if_neg ha, inheritedLabelSum]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨_, hθ, hp, _⟩ := Finset.mem_filter.mp hi
    exact (ha (hθ ▸ hp)).elim

/-- Exactly one parent-restricted current function contributes to each energy. -/
theorem sum_parent_inherited_energy {ι κ α X : Type*} [MeasurableSpace X]
    (I : Finset ι) (J : Finset κ) (A : Finset α)
    (label : ι → κ) (parent : κ → α) (hparent : ∀ θ ∈ J, parent θ ∈ A)
    (keep : ι → Prop) (f : ι → X → ℂ) (ν : Measure X) :
    (∑ a ∈ A, ∑ θ ∈ J, ∫⁻ x,
      ‖inheritedLabelSum I label θ (fun i ↦ parent (label i) = a ∧ keep i) f x‖ₑ ^ 2 ∂ν) =
      ∑ θ ∈ J, ∫⁻ x, ‖inheritedLabelSum I label θ keep f x‖ₑ ^ 2 ∂ν := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ hθ
  rw [Finset.sum_eq_single_of_mem (parent θ) (hparent θ hθ)]
  · simp only [inheritedLabelSum_parent_restriction, ↓reduceIte]
  · intro a _ ha
    simp only [inheritedLabelSum_parent_restriction, if_neg (Ne.symm ha), Pi.zero_apply,
      enorm_zero, zero_pow (by decide : 2 ≠ 0), lintegral_zero]

/-- The selected parent sum is exactly the corresponding filtered sum of current functions. -/
theorem sum_parent_restricted_inherited {ι κ α V : Type*} [AddCommMonoid V]
    (I : Finset ι) (J : Finset κ) (label : ι → κ) (parent : κ → α)
    (a : α) (keep : ι → Prop) (f : ι → V) :
    (∑ θ ∈ J, inheritedLabelSum I label θ (fun i ↦ parent (label i) = a ∧ keep i) f) =
      ∑ θ ∈ J.filter (fun θ ↦ parent θ = a), inheritedLabelSum I label θ keep f := by
  simp only [inheritedLabelSum_parent_restriction, Finset.sum_filter]

/-- Parent angular labels do not multiply the global error or localized-energy terms. -/
theorem sum_parent_inherited_energy_linear {ι κ α X : Type*} [MeasurableSpace X]
    (I : Finset ι) (J : Finset κ) (A : Finset α)
    (label : ι → κ) (parent : κ → α) (hparent : ∀ θ ∈ J, parent θ ∈ A)
    (keep : ι → Prop) (f : ι → X → ℂ) (ν₁ ν₂ : Measure X) (c₁ c₂ : ℝ≥0∞) :
    (∑ a ∈ A,
      ((c₁ * ∑ θ ∈ J, ∫⁻ x,
        ‖inheritedLabelSum I label θ (fun i ↦ parent (label i) = a ∧ keep i) f x‖ₑ ^ 2 ∂ν₁) +
      (c₂ * ∑ θ ∈ J, ∫⁻ x,
        ‖inheritedLabelSum I label θ (fun i ↦ parent (label i) = a ∧ keep i) f x‖ₑ ^ 2 ∂ν₂))) =
      c₁ * (∑ θ ∈ J, ∫⁻ x, ‖inheritedLabelSum I label θ keep f x‖ₑ ^ 2 ∂ν₁) +
      c₂ * (∑ θ ∈ J, ∫⁻ x, ‖inheritedLabelSum I label θ keep f x‖ₑ ^ 2 ∂ν₂) := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_parent_inherited_energy I J A label parent hparent keep f ν₁,
    sum_parent_inherited_energy I J A label parent hparent keep f ν₂]

end FalconerPacking
