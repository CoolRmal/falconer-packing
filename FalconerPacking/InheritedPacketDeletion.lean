/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.WeightedConditionalDeletion
public import FalconerPacking.DyadicPacketDeletion

/-!
# Actual whole-packet deletion from inherited physical marks

A bad standard packet is deleted near an initial pin cube precisely when its enlarged
physical strip meets that cube. The resulting measurable pin sets are covered by the actual
bad ancestor events, without introducing auxiliary angular labels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical FourierTransform
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Pins where a whole standard packet is deleted by the inherited marks and the near test. -/
def inheritedPacketDeletionPins
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (Y : Set (EuclideanSpace ℝ (Fin 2))) (w C : ℝ) (i : ℕ × ℤ) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  Y ∩ ⋃ Q ∈ I.filter (fun Q ↦
    ¬ standardPacketSurvives σ n e s t K L H 0 Q i.1 ∧
      (dyadicCube (n 0) Q ∩
        packetSourceStrip (sourceWavePacketNormal (2 ^ s) i.1) (w * i.2) (C * w)).Nonempty),
    dyadicCube (n 0) Q

/-- Membership exposes the actual initial cube, failed whole-packet mark, and meeting test. -/
theorem mem_inheritedPacketDeletionPins_iff
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (Y : Set (EuclideanSpace ℝ (Fin 2))) (w C : ℝ) (i : ℕ × ℤ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    y ∈ inheritedPacketDeletionPins σ n e s t K L H I Y w C i ↔
      y ∈ Y ∧ ∃ Q ∈ I, y ∈ dyadicCube (n 0) Q ∧
        ¬ standardPacketSurvives σ n e s t K L H 0 Q i.1 ∧
        (dyadicCube (n 0) Q ∩
          packetSourceStrip (sourceWavePacketNormal (2 ^ s) i.1) (w * i.2) (C * w)).Nonempty := by
  simp only [inheritedPacketDeletionPins, mem_inter_iff, mem_iUnion, Finset.mem_filter]
  aesop

/-- The initial family is finite, so no measurability of the marks as pointwise functions
is needed. -/
theorem measurableSet_inheritedPacketDeletionPins
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    {Y : Set (EuclideanSpace ℝ (Fin 2))} (hY : MeasurableSet Y)
    (w C : ℝ) (i : ℕ × ℤ) :
    MeasurableSet (inheritedPacketDeletionPins σ n e s t K L H I Y w C i) :=
  hY.inter (Finset.measurableSet_biUnion _ fun Q _ ↦ measurableSet_dyadicCube _ Q)

/-- A meeting enlarged strip contains the entire initial cube after increasing its half-width
by twice the cube side length. -/
theorem dyadicCube_subset_packetSourceStrip_of_meets {n : ℕ} {Q : Fin 2 → ℤ}
    {w C : ℝ} (hscale : ((2 : ℝ) ^ n)⁻¹ ≤ w) (N c : ℕ) (k : ℤ)
    (hmeet : (dyadicCube n Q ∩
      packetSourceStrip (sourceWavePacketNormal N c) (w * k) (C * w)).Nonempty) :
    dyadicCube n Q ⊆ packetSourceStrip (sourceWavePacketNormal N c) (w * k) ((C + 2) * w) := by
  obtain ⟨z, hz, hzs⟩ := hmeet
  intro y hy
  have hdiam := dist_le_of_mem_dyadicCube hy hz
  have hroot : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hd : dist y z ≤ 2 * w := by
    apply hdiam.trans
    rw [div_eq_mul_inv]
    calc
      _ ≤ 2 * ((2 : ℝ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right hroot (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)
  have hi : |⟪sourceWavePacketNormal N c, y⟫ - ⟪sourceWavePacketNormal N c, z⟫| ≤
      dist y z := by
    rw [← inner_sub_right]
    simpa only [norm_sourceWavePacketNormal, one_mul, dist_eq_norm] using
      abs_real_inner_le_norm (sourceWavePacketNormal N c) (y - z)
  have hz' : |⟪sourceWavePacketNormal N c, z⟫ - w * k| ≤ C * w := hzs
  change |⟪sourceWavePacketNormal N c, y⟫ - w * k| ≤ (C + 2) * w
  linarith [abs_sub_le ⟪sourceWavePacketNormal N c, y⟫ ⟪sourceWavePacketNormal N c, z⟫
    (w * k)]

/-- Every selected pin lies in the actual enlarged standard-packet strip. -/
theorem inheritedPacketDeletionPins_subset_strip
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (Y : Set (EuclideanSpace ℝ (Fin 2))) {w C : ℝ}
    (hscale : ((2 : ℝ) ^ n 0)⁻¹ ≤ w) (i : ℕ × ℤ) :
    inheritedPacketDeletionPins σ n e s t K L H I Y w C i ⊆
      packetSourceStrip (sourceWavePacketNormal (2 ^ s) i.1) (w * i.2) ((C + 2) * w) := by
  intro y hy
  obtain ⟨_, Q, _, hyQ, _, hmeet⟩ :=
    (mem_inheritedPacketDeletionPins_iff σ n e s t K L H I Y w C i y).mp hy
  exact dyadicCube_subset_packetSourceStrip_of_meets hscale _ _ _ hmeet hyQ

/-- The actual deleted source-pin pairs have a bad ancestor in the same finite physical chain. -/
theorem inheritedPacketDeletionPairs_subset_bad_ancestors
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (hn : Antitone n)
    (s t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (X Y : Set (EuclideanSpace ℝ (Fin 2))) {w C D : ℝ}
    (hscale : ((2 : ℝ) ^ n 0)⁻¹ ≤ w)
    (hD : ∀ y ∈ Y, ∀ x ∈ X, ‖x - y‖ ≤ D) (J : Finset ℤ) :
    (⋃ i ∈ (Finset.range (2 ^ s)) ×ˢ J,
      inheritedPacketDeletionPins σ n e s t K L H I Y w C i ×ˢ
        (X ∩ packetSourceStrip (sourceWavePacketNormal (2 ^ s) i.1) (w * i.2) (2 * w))) ⊆
      ⋃ j ∈ Finset.range K, ⋃ P ∈ I.image (ancestor (n 0 - n (j + 1))),
        physicalBadPacketPairs σ n e s t K L H X j P w (C + 2) D := by
  rintro ⟨y, x⟩ hp
  obtain ⟨i, hi, hy, hx, hxs⟩ := mem_iUnion₂.mp hp
  obtain ⟨hyY, Q, hQ, hyQ, hbad, _⟩ :=
    (mem_inheritedPacketDeletionPins_iff σ n e s t K L H I Y w C i y).mp hy
  obtain ⟨j, _, hjK, hjbad⟩ :=
    (not_standardPacketSurvives_iff σ n e s t K L H 0 Q i.1).mp hbad
  have hjn := hn (Nat.zero_le j)
  have hnext : n (j + 1) ≤ n j := hn (by omega)
  have hyj : y ∈ dyadicCube (n j) (ancestor (n 0 - n j) Q) := by
    apply dyadicCube_subset_ancestor (n j) (n 0 - n j) Q
    simpa only [Nat.add_sub_of_le hjn] using hyQ
  have hparent : ancestor (n j - n (j + 1)) (ancestor (n 0 - n j) Q) =
      ancestor (n 0 - n (j + 1)) Q := by
    rw [ancestor_ancestor]
    congr 1
    omega
  apply mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjK, ?_⟩
  apply mem_iUnion₂.mpr
    ⟨ancestor (n 0 - n (j + 1)) Q, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩, ?_⟩
  exact ⟨ancestor (n 0 - n j) Q, i.1, i.2, hparent,
    Finset.mem_range.mp (Finset.mem_product.mp hi).1, hjbad, hyj, hx, hxs,
    inheritedPacketDeletionPins_subset_strip σ n e s t K L H I Y hscale i hy,
    hD y hyY x hx⟩

/-- The union of the actual near deleted pairs has the sum of the proved conditional parent
bounds. All dependence on the number of initial cells is removed by geometric overlap. -/
theorem prod_inheritedPacketDeletionPairs_le
    (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ] [SFinite ν]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
    (X Y : Set (EuclideanSpace ℝ (Fin 2))) {w C D : ℝ}
    (hscale : ((2 : ℝ) ^ n 0)⁻¹ ≤ w)
    (hD : ∀ y ∈ Y, ∀ x ∈ X, ‖x - y‖ ≤ D) (J : Finset ℤ)
    (q : ℝ) (c d energy : ℕ → ℝ≥0∞)
    (hlocal : ∀ j < K, ∀ P ∈ I.image (ancestor (n 0 - n (j + 1))),
      σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹ (L ^ (2 * (j + 1) + 2)) P) ≠ 0 →
      ((normalizedRestrict σ
        (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
          (L ^ (2 * (j + 1) + 2)) P)).prod ν)
        (physicalBadPacketPairs σ n e s t K L H X j P w (C + 2) D) ≤
      c j * (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure
        ∂normalizedRestrict σ (enlargedGridSquare ((2 : ℝ) ^ n (j + 1))⁻¹
          (L ^ (2 * (j + 1) + 2)) P)) + d j * energy j) :
    (σ.prod ν) (⋃ i ∈ (Finset.range (2 ^ s)) ×ˢ J,
      inheritedPacketDeletionPins σ n e s t K L H I Y w C i ×ˢ
        (X ∩ packetSourceStrip (sourceWavePacketNormal (2 ^ s) i.1) (w * i.2) (2 * w))) ≤
      ∑ j ∈ Finset.range K, ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) *
        (c j * (∫⁻ y, ∫⁻ θ, radialProjectionDensity ν y θ ^ q ∂radialAngularMeasure ∂σ) +
          d j * energy j * σ univ) := by
  calc
    _ ≤ (σ.prod ν) (⋃ j ∈ Finset.range K,
        ⋃ P ∈ I.image (ancestor (n 0 - n (j + 1))),
          physicalBadPacketPairs σ n e s t K L H X j P w (C + 2) D) :=
      measure_mono (inheritedPacketDeletionPairs_subset_bad_ancestors
        σ n e hn s t K L H I X Y hscale hD J)
    _ ≤ ∑ j ∈ Finset.range K, (σ.prod ν)
        (⋃ P ∈ I.image (ancestor (n 0 - n (j + 1))),
          physicalBadPacketPairs σ n e s t K L H X j P w (C + 2) D) :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact prod_biUnion_physicalBadPacketPairs_le σ ν n e hn s t K hL H X j
        (I.image (ancestor (n 0 - n (j + 1)))) w (C + 2) D q (c j) (d j) (energy j)
        (hlocal j (Finset.mem_range.mp hj))

end FalconerPacking
