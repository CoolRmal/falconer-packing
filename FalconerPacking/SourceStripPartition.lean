/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PlanarStripPackets

/-!
# An actual finite packet partition for a bounded source ball

The source cutoff and the finite strip grid are constructed explicitly. The packets
sum to one on the source ball, have overlap at most three, and satisfy uniform
scale-correct spatial derivative bounds.
-/

@[expose] public section

noncomputable section

open Set Metric SchwartzMap
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- A fixed smooth source cutoff, equal to one up to radius `R` and zero beyond `2R`. -/
def sourceBallBump (R : ℝ) (hR : 0 < R) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
  ⟨R, 2 * R, hR, by linarith⟩

/-- The explicit source cutoff bundled as a Schwartz function. -/
def sourceBallCutoff (R : ℝ) (hR : 0 < R) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ :=
  (sourceBallBump R hR).hasCompactSupport.toSchwartzMap (sourceBallBump R hR).contDiff

@[simp]
theorem sourceBallCutoff_apply (R : ℝ) (hR : 0 < R) (x : EuclideanSpace ℝ (Fin 2)) :
    sourceBallCutoff R hR x = sourceBallBump R hR x := rfl

theorem sourceBallCutoff_eq_one (R : ℝ) (hR : 0 < R)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ closedBall 0 R) :
    sourceBallCutoff R hR x = 1 := (sourceBallBump R hR).one_of_mem_closedBall hx

theorem support_sourceBallCutoff (R : ℝ) (hR : 0 < R) :
    Function.support (sourceBallCutoff R hR) = ball 0 (2 * R) :=
  (sourceBallBump R hR).support_eq

theorem hasCompactSupport_sourceBallCutoff (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (sourceBallCutoff R hR) := (sourceBallBump R hR).hasCompactSupport

/-- The complete finite strip grid needed for the explicit source cutoff. -/
def sourceStripIndices (R w : ℝ) : Finset ℤ := slopeNet ⌈2 * R / w⌉₊

/-- The index count grows only linearly in inverse width. -/
theorem card_sourceStripIndices_le {R w : ℝ} (hR : 0 ≤ R) (hw : 0 < w) :
    ((sourceStripIndices R w).card : ℝ) ≤ 4 * R / w + 3 := by
  rw [sourceStripIndices, card_slopeNet, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * R / w)
  have he : 4 * R / w = 2 * (2 * R / w) := by ring
  rw [he]
  linarith

/-- The actual compact smooth packet, with every cutoff and grid factor specified. -/
def sourceStripPacket (R : ℝ) (hR : 0 < R) (w : ℝ)
    (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ :=
  (hasCompactSupport_smoothStripPacket (sourceBallCutoff R hR)
    (hasCompactSupport_sourceBallCutoff R hR) w e j).toSchwartzMap
      (contDiff_smoothStripPacket (sourceBallCutoff R hR) w e j)

@[simp]
theorem sourceStripPacket_apply (R : ℝ) (hR : 0 < R) (w : ℝ)
    (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    sourceStripPacket R hR w e j x =
      sourceBallCutoff R hR x * smoothStripWeight w j ⟪e, x⟫ := rfl

theorem sourceStripPacket_nonneg (R : ℝ) (hR : 0 < R) (w : ℝ)
    (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ sourceStripPacket R hR w e j x :=
  mul_nonneg (sourceBallBump R hR).nonneg (smoothStripWeight_nonneg w j _)

theorem sourceStripPacket_le_one (R : ℝ) (hR : 0 < R) (w : ℝ)
    (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)) :
    sourceStripPacket R hR w e j x ≤ 1 :=
  mul_le_one₀ (sourceBallBump R hR).le_one (smoothStripWeight_nonneg w j _)
    (smoothStripWeight_le_one w j _)

/-- The actual finite packets sum exactly to the explicit source cutoff everywhere. -/
theorem sum_sourceStripPacket_eq_cutoff (R : ℝ) (hR : 0 < R)
    {w : ℝ} (hw : 0 < w) {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ ≤ 1)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ j ∈ sourceStripIndices R w, sourceStripPacket R hR w e j x) =
      sourceBallCutoff R hR x := by
  have hs : Function.support (sourceBallCutoff R hR) ⊆ closedBall 0 (2 * R) := by
    rw [support_sourceBallCutoff]
    exact ball_subset_closedBall
  apply sum_smoothStripPacket_eq (sourceBallCutoff R hR) hs hw he
  have h := Nat.le_ceil (2 * R / w)
  exact (div_le_iff₀ hw).mp h |>.trans_eq (mul_comm _ _)

/-- On the source ball the finite sum is exactly one, with no approximate partition hypothesis. -/
theorem sum_sourceStripPacket_eq_one (R : ℝ) (hR : 0 < R)
    {w : ℝ} (hw : 0 < w) {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ ≤ 1)
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ closedBall 0 R) :
    (∑ j ∈ sourceStripIndices R w, sourceStripPacket R hR w e j x) = 1 := by
  rw [sum_sourceStripPacket_eq_cutoff R hR hw he, sourceBallCutoff_eq_one R hR hx]

/-- Every packet lies in the compact source cutoff and its stated strip. -/
theorem support_sourceStripPacket (R : ℝ) (hR : 0 < R)
    {w : ℝ} (hw : 0 < w) (e : EuclideanSpace ℝ (Fin 2)) (j : ℤ) :
    Function.support (sourceStripPacket R hR w e j) ⊆
      ball 0 (2 * R) ∩ {x | |⟪e, x⟫ - w * j| < w} := by
  intro x hx
  have h := support_smoothStripPacket (sourceBallCutoff R hR) hw e j hx
  rwa [support_sourceBallCutoff] at h

/-- The actual spatial packet family has uniform overlap at most three. -/
theorem card_sourceStripPacket_support_le (R : ℝ) (hR : 0 < R) (w : ℝ)
    (e : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)) :
    ((sourceStripIndices R w).filter (fun j ↦ sourceStripPacket R hR w e j x ≠ 0)).card ≤ 3 :=
  card_smoothStripPacket_support_le (sourceBallCutoff R hR) w e (sourceStripIndices R w) x

/-- All packet derivatives have a uniform bound depending only on the source radius and order. -/
theorem exists_sourceStripPacket_derivative_bound (R : ℝ) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      ∀ e : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j : ℤ) (x : EuclideanSpace ℝ (Fin 2)),
        ‖iteratedFDeriv ℝ n (sourceStripPacket R hR w e j) x‖ ≤ C * w⁻¹ ^ n :=
  exists_smoothStripPacket_derivative_bound_of_le_one (sourceBallCutoff R hR) n

end FalconerPacking
