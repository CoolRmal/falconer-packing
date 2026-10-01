/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PhysicalDyadicMarks
import FalconerPacking.AllDirectionTubeDeletion

/-!
# Actual bad physical marks give the source-pin pairs used by deletion

The pin lies in its actual dyadic child; the conditional measure uses exactly the enlarged
parent of the circle-energy edge. A failed physical test and an actual source packet strip
place the pair in the coarsening theorem's heavy-tube event.
-/

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- A dyadic child pin belongs to the same enlarged parent used by its physical test. -/
theorem mem_physicalDyadicParent {n : ℕ → ℕ} (hn : Antitone n) {L : ℝ} (hL : 1 ≤ L)
    {j : ℕ} {Q : Fin 2 → ℤ} {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ dyadicCube (n j) Q) : y ∈ physicalDyadicParent n L j Q := by
  apply dyadicCube_subset_enlargedGridSquare _ (one_le_pow₀ hL)
  apply dyadicCube_subset_ancestor (n (j + 1)) (n j - n (j + 1)) Q
  simpa only [Nat.add_sub_of_le (hn (Nat.le_succ j))] using hy

/-- The entire physical enlarged parent fits in an explicit open ball with twice its side. -/
theorem physicalDyadicParent_subset_ball (n : ℕ → ℕ) {L : ℝ} (hL : 0 < L)
    (j : ℕ) (Q : Fin 2 → ℤ) :
    physicalDyadicParent n L j Q ⊆
      Metric.ball (gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹
        (ancestor (n j - n (j + 1)) Q))
        (2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹) := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have h := norm_sub_gridSquareCenter_le hy
  apply h.trans_lt
  have hp : 0 < L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹ := by positivity
  linarith

/-- A physical tested rectangle is contained in the strip with its actual effective normal. -/
theorem physicalDyadicTube_subset_effective_strip (n e : ℕ → ℕ) (s t K : ℕ)
    (L : ℝ) (j : ℕ) (Q : Fin 2 → ℤ) (c k : ℕ) :
    physicalDyadicTube n e s K L j Q (dyadicCapAncestor s t (e (j + 1)) (c, k)) ⊆
      {y | |⟪packetEffectiveNormal s (e (j + 1)) c,
        y - gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ Q⟫| ≤
          L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2} := by
  intro y hy
  change |⟪packetEffectiveNormal s (e (j + 1)) c, _⟫| ≤ _
  rw [abs_inner_packetEffectiveNormal s t (e (j + 1)) (c, k)]
  exact hy.1

/-- The actual child pin is inside its own effective tested strip. -/
theorem dyadic_pin_mem_effective_strip (n e : ℕ → ℕ) (s K : ℕ)
    {L : ℝ} (hL : 2 ≤ L) (j : ℕ) (Q : Fin 2 → ℤ) (c : ℕ)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ dyadicCube (n j) Q) :
    |⟪packetEffectiveNormal s (e (j + 1)) c,
      y - gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ Q⟫| ≤
        L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2 := by
  have hnorm := norm_sub_gridSquareCenter_le
    (dyadicCube_subset_enlargedGridSquare Q le_rfl hy)
  simp only [one_mul] at hnorm
  have hpow : 2 ≤ L ^ (4 * K + 20) := by
    apply hL.trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ L)
      (show 1 ≤ 4 * K + 20 by omega)
  calc
    _ ≤ ‖packetEffectiveNormal s (e (j + 1)) c‖ *
        ‖y - gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ Q‖ := abs_real_inner_le_norm _ _
    _ ≤ ((2 : ℝ) ^ n j)⁻¹ := by simpa only [norm_packetEffectiveNormal, one_mul] using hnorm
    _ ≤ _ := by nlinarith [inv_pos.mpr (by positivity : (0 : ℝ) < 2 ^ n j)]

/-- A failed actual physical mark puts every associated standard packet pair in the heavy
conditional tube event. Its angular uncertainty is derived from the actual standard grid. -/
theorem bad_physical_mark_pair_mem
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (n e : ℕ → ℕ) (hn : Antitone n) (s t K : ℕ) {L : ℝ} (hL : 2 ≤ L)
    (H : ℕ → ℝ≥0∞) (j : ℕ) (Q : Fin 2 → ℤ) (c : ℕ)
    (hQ : σ (physicalDyadicParent n L j Q) ≠ 0)
    (hbad : ¬ physicalDyadicGood σ n e s K L H j Q
      (dyadicCapAncestor s t (e (j + 1)) (c, 0)))
    {X : Set (EuclideanSpace ℝ (Fin 2))} {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ X) (hy : y ∈ dyadicCube (n j) Q) {center u v D : ℝ}
    (hxs : x ∈ packetSourceStrip (sourceWavePacketNormal (2 ^ s) c) center u)
    (hys : y ∈ packetSourceStrip (sourceWavePacketNormal (2 ^ s) c) center v)
    (hD : ‖x - y‖ ≤ D) :
    (y, x) ∈ heavyTestedTubePairs (normalizedRestrict σ (physicalDyadicParent n L j Q)) X
      (gridSquareCenter ((2 : ℝ) ^ n (j + 1))⁻¹ (ancestor (n j - n (j + 1)) Q))
      (gridSquareCenter ((2 : ℝ) ^ n j)⁻¹ Q) (packetEffectiveNormal s (e (j + 1)) c)
      (2 * L ^ (2 * (j + 1) + 2) * ((2 : ℝ) ^ n (j + 1))⁻¹)
      (L ^ (4 * K + 20) * ((2 : ℝ) ^ n j)⁻¹ / 2)
      (u + v + (2 * Real.pi / (2 : ℝ) ^ min s (e (j + 1))) * D) D
      (H j * ENNReal.ofReal (((2 : ℝ) ^ n j)⁻¹ / ((2 : ℝ) ^ n (j + 1))⁻¹)) := by
  have hL₁ : 1 ≤ L := by linarith
  have hL₀ : 0 < L := by linarith
  have hyU := mem_physicalDyadicParent hn hL₁ hy
  have hyB := physicalDyadicParent_subset_ball n hL₀ j Q hyU
  have hyS := dyadic_pin_mem_effective_strip n e s K hL j Q c hy
  refine ⟨⟨hyB, hyS⟩, hx, packetEffectiveNormal_pair_bound s (e (j + 1)) c hxs hys hD,
    hD, ?_⟩
  have hheavy := lt_of_not_ge
    ((physicalDyadicGood_iff_normalized σ n e s K L H j Q _ hQ).not.mp hbad)
  apply hheavy.trans_le
  have hm : MeasurableSet (physicalDyadicTube n e s K L j Q
      (dyadicCapAncestor s t (e (j + 1)) (c, 0))) := measurableSet_frameRectangle _ _ _ _
  rw [normalizedRestrict_apply _ _ _ hm]
  rw [normalizedRestrict_apply _ _ _
    (Metric.isOpen_ball.measurableSet.inter (isClosed_le (by fun_prop)
      continuous_const).measurableSet)]
  apply mul_le_mul' le_rfl (measure_mono ?_)
  intro z hz
  exact ⟨⟨physicalDyadicParent_subset_ball n hL₀ j Q hz.2,
    physicalDyadicTube_subset_effective_strip n e s t K L j Q c 0 hz.1⟩, hz.2⟩

end FalconerPacking
