/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InitialCellRemoteGeometry
import FalconerPacking.InheritedPacketDeletion

/-!
# Exact agreement of retained and deleted source packets

At a pin in an initial cube, the whole-packet deletion rule is exactly complementary to
the retained source used in the initial spectral reconstruction. The underlying source
packets and their common annular source are unchanged.
-/

noncomputable section

open MeasureTheory Set Classical FourierTransform
open scoped ENNReal

namespace FalconerPacking

private theorem sum_retained_deleted {α β A : Type*} [AddCommMonoid A]
    (I : Finset α) (J : Finset β) (P : α → Prop) (R : α → β → Prop)
    (f : α → β → A) :
    (∑ i ∈ I, ∑ j ∈ J, f i j) =
      ((∑ i ∈ I.filter P, ∑ j ∈ J, f i j) +
        ∑ i ∈ I.filter (fun i ↦ ¬P i), ∑ j ∈ J.filter (R i), f i j) +
      ∑ i ∈ I, ∑ j ∈ J, if ¬P i ∧ ¬R i j then f i j else 0 := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : P i
  · simp [hp]
  · simp only [hp, not_false_eq_true, ↓reduceIte, zero_add, true_and,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hr : R i j <;> simp [hr]

/-- The unique initial cube removes the apparent union in the deletion rule. -/
theorem mem_inheritedPacketDeletionPins_of_mem_cube
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (Y : Set (EuclideanSpace ℝ (Fin 2))) (w C : ℝ) (i : ℕ × ℤ)
    {Q : Fin 2 → ℤ} (hQ : Q ∈ I)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ dyadicCube (n 0) Q) (hyY : y ∈ Y) :
    y ∈ inheritedPacketDeletionPins σ n e s t K L H I Y w C i ↔
      ¬standardPacketSurvives σ n e s t K L H 0 Q i.1 ∧
        (dyadicCube (n 0) Q ∩
          packetSourceStrip (sourceWavePacketNormal (2 ^ s) i.1) (w * i.2)
            (C * w)).Nonempty := by
  rw [mem_inheritedPacketDeletionPins_iff]
  constructor
  · rintro ⟨_, Q', _, hy', hbad, hnear⟩
    have he : Q' = Q := (mem_dyadicCube_iff.mp hy').symm.trans
      (mem_dyadicCube_iff.mp hy)
    subst Q'
    exact ⟨hbad, hnear⟩
  · rintro ⟨hbad, hnear⟩
    exact ⟨hyY, Q, hQ, hy, hbad, hnear⟩

/-- The exact retained and deleted sums partition all constructed standard packets. -/
theorem initialRetainedSource_add_deletedPacketSum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (Y : Set (EuclideanSpace ℝ (Fin 2))) (w : ℝ)
    {Q : Fin 2 → ℤ} (hQ : Q ∈ I)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ dyadicCube (n 0) Q) (hyY : y ∈ Y) :
    let N := 2 ^ s
    let hN : 0 < N := by dsimp only [N]; positivity
    let G := (Finset.range N).filter (standardPacketSurvives σ n e s t K L H 0 Q)
    initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G
        (fun j ↦ initialCellRemoteIndices χ hχ w N j (dyadicCube (n 0) Q)) +
      deletedPacketSum ((Finset.range N) ×ˢ sourceWavePacketIndices χ hχ w)
        (inheritedPacketDeletionPins σ n e s t K L H I Y w 4)
        (fun i ↦ sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w i.1 i.2) y =
      ∑ j ∈ Finset.range N, ∑ k ∈ sourceWavePacketIndices χ hχ w,
        sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k := by
  dsimp only
  have hdiff : Finset.range (2 ^ s) \
      (Finset.range (2 ^ s)).filter (standardPacketSurvives σ n e s t K L H 0 Q) =
      (Finset.range (2 ^ s)).filter
        (fun j ↦ ¬standardPacketSurvives σ n e s t K L H 0 Q j) := by
    ext j
    simp
    tauto
  unfold initialRetainedSource deletedPacketSum initialCellRemoteIndices
  rw [hdiff]
  simp only [Finset.sum_filter, Finset.sum_product]
  simp_rw [mem_inheritedPacketDeletionPins_of_mem_cube σ n e s t K L H I Y w 4
    _ hQ hy hyY]
  have he := sum_retained_deleted (Finset.range (2 ^ s)) (sourceWavePacketIndices χ hχ w)
    (standardPacketSurvives σ n e s t K L H 0 Q)
    (fun j k ↦ Disjoint (dyadicCube (n 0) Q)
      (packetSourceStrip (sourceWavePacketNormal (2 ^ s) j) (w * k) (4 * w)))
    (fun j k ↦ sourceWavePacket μ hμ ψ hψ hzero χ hχ (2 ^ s) (by positivity) w j k)
  simp only [Finset.sum_filter] at he
  convert he.symm using 1
  simp only [Set.disjoint_iff_inter_eq_empty, Set.nonempty_iff_ne_empty]

end FalconerPacking
