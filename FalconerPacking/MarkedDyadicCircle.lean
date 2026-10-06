/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicCapAncestry
public import FalconerPacking.Dyadic

/-!
# Actual circle functions with inherited spatial and angular marks

The future marks for a child cube are precisely the future marks of its unique parent.
Combined with the constructed angular ancestry, this gives the exact spatial-edge
identity for actual circle functions, through coarse and fine levels alike.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Classical SchwartzMap
open scoped Topology

namespace FalconerPacking

/-- All future marks, evaluated at the actual dyadic spatial and angular ancestors. -/
def dyadicCapSpatialSurvives (s t : ℕ) (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (j K : ℕ) (Q : Fin 2 → ℤ) (q : ℕ × ℕ) : Prop :=
  ∀ i, j ≤ i → i < K →
    good i (ancestor (n j - n i) Q) (dyadicCapAncestor s t (e (i + 1)) q)

/-- Composing the actual dyadic parent with any later ancestor gives the original ancestor. -/
theorem ancestor_along_antitone_depths {n : ℕ → ℕ} (hn : Antitone n)
    {j i : ℕ} (hji : j + 1 ≤ i) (Q : Fin 2 → ℤ) :
    ancestor (n (j + 1) - n i) (ancestor (n j - n (j + 1)) Q) = ancestor (n j - n i) Q := by
  rw [ancestor_ancestor]
  have h₀ : n (j + 1) ≤ n j := hn (Nat.le_succ j)
  have h₁ : n i ≤ n (j + 1) := hn hji
  have he : n (j + 1) - n i + (n j - n (j + 1)) = n j - n i := by omega
  rw [he]

/-- The current decision is separated from one common parent family of all future decisions. -/
theorem dyadicCapSpatialSurvives_succ (s t : ℕ) (n e : ℕ → ℕ) (hn : Antitone n)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    {j K : ℕ} (hj : j < K) (Q : Fin 2 → ℤ) (q : ℕ × ℕ) :
    dyadicCapSpatialSurvives s t n e good j K Q q ↔
      good j Q (dyadicCapAncestor s t (e (j + 1)) q) ∧
      dyadicCapSpatialSurvives s t n e good (j + 1) K
        (ancestor (n j - n (j + 1)) Q) q := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Nat.sub_self, ancestor_zero] using h j le_rfl hj
    · intro i hji hiK
      rw [ancestor_along_antitone_depths hn hji]
      exact h i (by omega) hiK
  · rintro ⟨hcur, hnext⟩ i hji hiK
    rcases eq_or_lt_of_le hji with rfl | hji'
    · simpa only [Nat.sub_self, ancestor_zero] using hcur
    · have h := hnext i (by omega) hiK
      rwa [ancestor_along_antitone_depths hn (by omega)] at h

@[simp]
theorem dyadicCapSpatialSurvives_terminal (s t : ℕ) (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (K : ℕ) (Q : Fin 2 → ℤ) (q : ℕ × ℕ) :
    dyadicCapSpatialSurvives s t n e good K K Q q := by
  intro i hi hiK
  omega

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (s t : ℕ) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)

/-- The actual function indexed by a spatial cube and an earlier angular ancestor. -/
def markedDyadicCircle (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (j K : ℕ) (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ)) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  inheritedLabelSum (fineCapLabels (2 ^ s) (2 ^ t)) (dyadicCapAncestor s t (e j)) α
    (dyadicCapSpatialSurvives s t n e good j K Q)
    (fineCapCircleSchwartz ψ hψ hzero (2 ^ s) (by positivity) r hg k hk (2 ^ t))

/-- The exact spatial-edge identity, including every actual angular crossing and future mark. -/
theorem markedDyadicCircle_step (n e : ℕ → ℕ) (hn : Antitone n) (he : Monotone e)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    {j K : ℕ} (hj : j < K) (het : e (j + 1) ≤ t)
    (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ)) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α =
      ∑ β ∈ (dyadicCapLabels s (e (j + 1))).filter
        (fun β ↦ dyadicCapParent s (e j) (e (j + 1)) β = α ∧ good j Q β),
        markedDyadicCircle ψ hψ hzero s t r hg k hk n e good (j + 1) K
          (ancestor (n j - n (j + 1)) Q) β := by
  have hsurv : dyadicCapSpatialSurvives s t n e good j K Q = fun q ↦
      good j Q (dyadicCapAncestor s t (e (j + 1)) q) ∧
      dyadicCapSpatialSurvives s t n e good (j + 1) K
        (ancestor (n j - n (j + 1)) Q) q := by
    funext q
    exact propext (dyadicCapSpatialSurvives_succ s t n e hn good hj Q q)
  simp only [markedDyadicCircle, hsurv]
  exact dyadicCapInherited_regroup (he (Nat.le_succ j)) het α (good j Q)
    (dyadicCapSpatialSurvives s t n e good (j + 1) K (ancestor (n j - n (j + 1)) Q))
    (fineCapCircleSchwartz ψ hψ hzero (2 ^ s) (by positivity) r hg k hk (2 ^ t))

/-- Terminal functions contain no spatial mark and are independent of the terminal cube. -/
theorem markedDyadicCircle_terminal (n e : ℕ → ℕ)
    (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
    (K : ℕ) (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ)) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e good K K Q α =
      inheritedLabelSum (fineCapLabels (2 ^ s) (2 ^ t)) (dyadicCapAncestor s t (e K)) α
        (fun _ ↦ True)
        (fineCapCircleSchwartz ψ hψ hzero (2 ^ s) (by positivity) r hg k hk (2 ^ t)) := by
  unfold markedDyadicCircle
  congr 1
  funext q
  exact propext ⟨fun _ ↦ trivial, fun _ ↦ dyadicCapSpatialSurvives_terminal s t n e good K Q q⟩

end FalconerPacking
