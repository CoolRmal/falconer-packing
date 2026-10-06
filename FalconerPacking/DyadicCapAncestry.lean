/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.InheritedCoarseCapSupport

/-!
# Exact dyadic angular ancestry through the standard scale

Coarse labels group whole standard caps; fine labels retain a standard index and an
auxiliary cell. A single explicit parent map covers coarse, fine, and crossing edges.
-/

@[expose] public section

noncomputable section

open Classical

namespace FalconerPacking

/-- The actual active angular labels at a power-of-two level. -/
def dyadicCapLabels (s e : ℕ) : Finset (ℕ ⊕ (ℕ × ℕ)) :=
  if e ≤ s then (Finset.range (2 ^ e)).image Sum.inl
  else (fineCapLabels (2 ^ s) (2 ^ e)).image Sum.inr

/-- The ancestor of a terminal standard-cap/cell pair. -/
def dyadicCapAncestor (s t e : ℕ) (q : ℕ × ℕ) : ℕ ⊕ (ℕ × ℕ) :=
  if e ≤ s then Sum.inl (q.1 / 2 ^ (s - e))
  else Sum.inr (q.1, q.2 / 2 ^ (t - e))

/-- The unique parent label; crossing discards the fine cell and groups the standard index. -/
def dyadicCapParent (s c f : ℕ) : (ℕ ⊕ (ℕ × ℕ)) → (ℕ ⊕ (ℕ × ℕ))
  | Sum.inl j => Sum.inl (j / 2 ^ (f - c))
  | Sum.inr q => if c ≤ s then Sum.inl (q.1 / 2 ^ (s - c))
    else Sum.inr (q.1, q.2 / 2 ^ (f - c))

/-- Refinement factors multiply exactly at every admissible triple of integer levels. -/
theorem dyadic_refinement_factor {c f t : ℕ} (hcf : c ≤ f) (hft : f ≤ t) :
    2 ^ (t - f) * 2 ^ (f - c) = (2 : ℕ) ^ (t - c) := by
  rw [← pow_add]
  congr 1
  omega

/-- Actual angular ancestors compose across every combination of coarse and fine levels. -/
theorem dyadicCapParent_ancestor {s t c f : ℕ} (hcf : c ≤ f) (hft : f ≤ t)
    (q : ℕ × ℕ) :
    dyadicCapParent s c f (dyadicCapAncestor s t f q) = dyadicCapAncestor s t c q := by
  by_cases hf : f ≤ s
  · have hc : c ≤ s := hcf.trans hf
    simp only [dyadicCapAncestor, if_pos hf, if_pos hc, dyadicCapParent,
      Nat.div_div_eq_div_mul, dyadic_refinement_factor hcf hf]
  · by_cases hc : c ≤ s
    · simp only [dyadicCapAncestor, if_neg hf, if_pos hc, dyadicCapParent]
    · simp only [dyadicCapAncestor, if_neg hf, if_neg hc, dyadicCapParent,
        Nat.div_div_eq_div_mul, dyadic_refinement_factor hcf hft]

/-- Every terminal label has an active ancestor; no partition hypothesis is assumed. -/
theorem dyadicCapAncestor_mem {s t e : ℕ} (het : e ≤ t)
    {q : ℕ × ℕ} (hq : q ∈ fineCapLabels (2 ^ s) (2 ^ t)) :
    dyadicCapAncestor s t e q ∈ dyadicCapLabels s e := by
  by_cases he : e ≤ s
  · simp only [dyadicCapAncestor, dyadicCapLabels, if_pos he]
    apply Finset.mem_image.mpr
    refine ⟨q.1 / 2 ^ (s - e), ?_, rfl⟩
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < (2 : ℕ) ^ (s - e))).mpr
    have hq' := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have hpow : (2 : ℕ) ^ e * 2 ^ (s - e) = 2 ^ s := by
      rw [← pow_add, Nat.add_sub_of_le he]
    rwa [hpow]
  · simp only [dyadicCapAncestor, dyadicCapLabels, if_neg he]
    apply Finset.mem_image.mpr
    refine ⟨(q.1, q.2 / 2 ^ (t - e)), ?_, rfl⟩
    have hpow : (2 : ℕ) ^ (t - e) * 2 ^ e = 2 ^ t := by
      rw [← pow_add, Nat.sub_add_cancel het]
    have hq' : q ∈ fineCapLabels (2 ^ s) (2 ^ (t - e) * 2 ^ e) := hpow.symm ▸ hq
    exact fineCapLabels_parent_mem (by positivity) (by positivity) hq'

/-- An actual finer active label has an actual coarser parent. -/
theorem dyadicCapParent_mem {s c f : ℕ} (hcf : c ≤ f)
    {α : ℕ ⊕ (ℕ × ℕ)} (hα : α ∈ dyadicCapLabels s f) :
    dyadicCapParent s c f α ∈ dyadicCapLabels s c := by
  by_cases hf : f ≤ s
  · have hc : c ≤ s := hcf.trans hf
    simp only [dyadicCapLabels, if_pos hf] at hα
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hα
    simp only [dyadicCapParent, dyadicCapLabels, if_pos hc]
    refine Finset.mem_image.mpr ⟨j / 2 ^ (f - c), Finset.mem_range.mpr ?_, rfl⟩
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < (2 : ℕ) ^ (f - c))).mpr
    have he : (2 : ℕ) ^ c * 2 ^ (f - c) = 2 ^ f := by
      rw [← pow_add, Nat.add_sub_of_le hcf]
    rw [he]
    exact Finset.mem_range.mp hj
  · simp only [dyadicCapLabels, if_neg hf] at hα
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hα
    have h := dyadicCapAncestor_mem (s := s) (t := f) hcf hq
    simpa only [dyadicCapParent, dyadicCapAncestor] using h

/-- Every earlier terminal label is recovered by its exact set of current ancestors. -/
theorem dyadicCapInherited_regroup {V : Type*} [AddCommMonoid V]
    {s t c f : ℕ} (hcf : c ≤ f) (hft : f ≤ t)
    (α : ℕ ⊕ (ℕ × ℕ)) (good : (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (keep : ℕ × ℕ → Prop) (v : ℕ × ℕ → V) :
    inheritedLabelSum (fineCapLabels (2 ^ s) (2 ^ t)) (dyadicCapAncestor s t c) α
      (fun q ↦ good (dyadicCapAncestor s t f q) ∧ keep q) v =
      ∑ β ∈ (dyadicCapLabels s f).filter
        (fun β ↦ dyadicCapParent s c f β = α ∧ good β),
        inheritedLabelSum (fineCapLabels (2 ^ s) (2 ^ t)) (dyadicCapAncestor s t f) β keep v := by
  have he : dyadicCapParent s c f ∘ dyadicCapAncestor s t f = dyadicCapAncestor s t c := by
    funext q
    exact dyadicCapParent_ancestor hcf hft q
  rw [← he]
  convert inheritedLabelSum_regroup (fineCapLabels (2 ^ s) (2 ^ t)) (dyadicCapLabels s f)
    (dyadicCapAncestor s t f) (dyadicCapParent s c f)
    (fun q hq ↦ dyadicCapAncestor_mem hft hq) α good keep v using 1
  apply Finset.sum_congr
  · ext β
    simp only [Finset.mem_filter]
  · intro β _
    rfl

end FalconerPacking
