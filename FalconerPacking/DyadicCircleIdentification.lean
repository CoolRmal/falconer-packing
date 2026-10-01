/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.MarkedDyadicCircle

/-!
# Identification of marked dyadic labels with the analytic circle families

These identities connect the single dyadic ancestry, including crossing edges, to the
coarse and fine functions used by the actual selected-cap estimates.
-/

noncomputable section

open MeasureTheory Filter Classical SchwartzMap
open scoped Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (s t : ℕ) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)

/-- Coarse dyadic labels group whole standard caps, including every future mark. -/
theorem markedDyadicCircle_coarse (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (j K : ℕ) (Q : Fin 2 → ℤ) (c : ℕ) (he : e j ≤ s) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q (Sum.inl c) =
      inheritedCoarseCapCircle ψ hψ hzero (2 ^ s) (by positivity) r hg k hk
        (2 ^ (s - e j)) (2 ^ t) (dyadicCapSpatialSurvives s t n e good j K Q) c := by
  simp only [markedDyadicCircle, inheritedCoarseCapCircle, inheritedLabelSum,
    dyadicCapAncestor, if_pos he, Sum.inl.injEq]

/-- Fine dyadic labels keep the standard cap and use the exact auxiliary ancestor cell. -/
theorem markedDyadicCircle_fine (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (j K : ℕ) (Q : Fin 2 → ℤ) (p : ℕ × ℕ) (he : s < e j) (het : e j ≤ t) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q (Sum.inr p) =
      inheritedFineCapCircle ψ hψ hzero (2 ^ s) (by positivity) r hg k hk
        (2 ^ (t - e j)) (2 ^ (e j)) (dyadicCapSpatialSurvives s t n e good j K Q) p := by
  have hp : (2 : ℕ) ^ (t - e j) * 2 ^ (e j) = 2 ^ t := by
    rw [← pow_add, Nat.sub_add_cancel het]
  simp only [markedDyadicCircle, inheritedFineCapCircle, inheritedLabelSum,
    dyadicCapAncestor, if_neg (not_le.mpr he), Sum.inr.injEq, hp]

/-- Sums over actual coarse labels have no inactive or duplicate terms. -/
theorem sum_dyadicCapLabels_coarse {V : Type*} [AddCommMonoid V]
    {s e : ℕ} (he : e ≤ s) (f : (ℕ ⊕ (ℕ × ℕ)) → V) :
    ∑ α ∈ dyadicCapLabels s e, f α = ∑ c ∈ Finset.range (2 ^ e), f (Sum.inl c) := by
  simp only [dyadicCapLabels, if_pos he]
  exact Finset.sum_image (fun _ _ _ _ h ↦ Sum.inl.inj h)

/-- Sums over actual fine labels retain exactly the active cap/cell pairs. -/
theorem sum_dyadicCapLabels_fine {V : Type*} [AddCommMonoid V]
    {s e : ℕ} (he : s < e) (f : (ℕ ⊕ (ℕ × ℕ)) → V) :
    ∑ α ∈ dyadicCapLabels s e, f α =
      ∑ p ∈ fineCapLabels (2 ^ s) (2 ^ e), f (Sum.inr p) := by
  simp only [dyadicCapLabels, if_neg (not_le.mpr he)]
  exact Finset.sum_image (fun _ _ _ _ h ↦ Sum.inr.inj h)

/-- A coarse current level gives the exact selected sum in the analytic edge estimate. -/
theorem markedDyadicCircle_step_coarse (n e : ℕ → ℕ) (hn : Antitone n)
    (he : Monotone e) (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    {j K : ℕ} (hj : j < K) (het : e (j + 1) ≤ t)
    (hes : e (j + 1) ≤ s) (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ)) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α =
      ∑ c ∈ (Finset.range (2 ^ (e (j + 1)))).filter
        (fun c ↦ dyadicCapParent s (e j) (e (j + 1)) (Sum.inl c) = α ∧
          good j Q (Sum.inl c)),
        inheritedCoarseCapCircle ψ hψ hzero (2 ^ s) (by positivity) r hg k hk
          (2 ^ (s - e (j + 1))) (2 ^ t)
          (dyadicCapSpatialSurvives s t n e good (j + 1) K
            (ancestor (n j - n (j + 1)) Q)) c := by
  rw [markedDyadicCircle_step ψ hψ hzero s t r hg k hk n e hn he good hj het]
  simp only [Finset.sum_filter]
  rw [sum_dyadicCapLabels_coarse hes]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · exact markedDyadicCircle_coarse ψ hψ hzero s t r hg k hk n e good _ _ _ c hes
  · rfl

/-- A fine current level gives the exact selected sum, including a crossing from a coarse parent. -/
theorem markedDyadicCircle_step_fine (n e : ℕ → ℕ) (hn : Antitone n)
    (he : Monotone e) (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    {j K : ℕ} (hj : j < K) (het : e (j + 1) ≤ t)
    (hse : s < e (j + 1)) (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ)) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α =
      ∑ p ∈ (fineCapLabels (2 ^ s) (2 ^ (e (j + 1)))).filter
        (fun p ↦ dyadicCapParent s (e j) (e (j + 1)) (Sum.inr p) = α ∧
          good j Q (Sum.inr p)),
        inheritedFineCapCircle ψ hψ hzero (2 ^ s) (by positivity) r hg k hk
          (2 ^ (t - e (j + 1))) (2 ^ (e (j + 1)))
          (dyadicCapSpatialSurvives s t n e good (j + 1) K
            (ancestor (n j - n (j + 1)) Q)) p := by
  rw [markedDyadicCircle_step ψ hψ hzero s t r hg k hk n e hn he good hj het]
  simp only [Finset.sum_filter]
  rw [sum_dyadicCapLabels_fine hse]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs
  · exact markedDyadicCircle_fine ψ hψ hzero s t r hg k hk n e good _ _ _ p hse het
  · rfl

end FalconerPacking
