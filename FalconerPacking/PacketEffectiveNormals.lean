/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.MarkedCircleParentEdge
public import FalconerPacking.PhysicalDyadicCapKernels
public import FalconerPacking.LocalizedPacketMass

/-!
# Actual effective directions of marked standard source packets

Coarse tests use the nominal ancestor of a whole standard cap. Fine tests keep its
original normal. In either regime the physical direction is independent of the auxiliary
terminal cell, and its discrepancy is controlled by the actual dyadic angular mesh.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- The normal used to test a whole standard source cap at any selected angular level. -/
def packetEffectiveNormal (s e j : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  if e ≤ s then sourceWavePacketNormal (2 ^ e) (j / 2 ^ (s - e))
  else sourceWavePacketNormal (2 ^ s) j

@[simp]
theorem norm_packetEffectiveNormal (s e j : ℕ) : ‖packetEffectiveNormal s e j‖ = 1 := by
  unfold packetEffectiveNormal
  split <;> exact norm_sourceWavePacketNormal _ _

/-- The actual angular ancestor's physical transverse coordinate uses the effective normal. -/
theorem abs_inner_packetEffectiveNormal (s t e : ℕ) (q : ℕ × ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    |⟪packetEffectiveNormal s e q.1, x⟫| =
      |dyadicCapPhysicalFrame s e (dyadicCapAncestor s t e q) x 0| := by
  unfold packetEffectiveNormal dyadicCapAncestor
  split <;> exact abs_inner_sourceWavePacketNormal _ _ _

/-- Rotating the nominal directions by a right angle preserves their distance. -/
theorem dist_sourceWavePacketNormal (N M j k : ℕ) :
    dist (sourceWavePacketNormal N j) (sourceWavePacketNormal M k) =
      dist (angularDirection (angularGridPoint N j))
        (angularDirection (angularGridPoint M k)) := by
  have h := (planarRotation (Real.pi / 2)).dist_map
    (angularDirection (angularGridPoint N j)) (angularDirection (angularGridPoint M k))
  simpa only [planarRotation_angularDirection, sourceWavePacketNormal, add_comm] using h

/-- A standard source normal differs from its effective test normal by at most the coarse
mesh width. After crossing the standard scale their difference is exactly zero. -/
theorem dist_packetEffectiveNormal_le (s e j : ℕ) :
    dist (packetEffectiveNormal s e j) (sourceWavePacketNormal (2 ^ s) j) ≤
      2 * Real.pi / (2 : ℝ) ^ min s e := by
  by_cases he : e ≤ s
  · have hpow : (2 : ℕ) ^ (s - e) * 2 ^ e = 2 ^ s := by
      rw [← pow_add, Nat.sub_add_cancel he]
    rw [packetEffectiveNormal, if_pos he, dist_comm, dist_sourceWavePacketNormal,
      min_eq_right he]
    have h := angularGridDirection_ancestor_bound
      (by positivity : 0 < (2 : ℕ) ^ (s - e)) (by positivity : 0 < (2 : ℕ) ^ e) j
    simpa only [hpow, Nat.cast_pow, Nat.cast_ofNat] using h
  · rw [packetEffectiveNormal, if_neg he, dist_self]
    positivity

/-- The elementary strip-pair estimate uses the same standard source normal for both points. -/
theorem packetSourceStrip_pair_bound {e x y : EuclideanSpace ℝ (Fin 2)} {c u v : ℝ}
    (hx : x ∈ packetSourceStrip e c u) (hy : y ∈ packetSourceStrip e c v) :
    |⟪e, x - y⟫| ≤ u + v := by
  change |⟪e, x⟫ - c| ≤ u at hx
  change |⟪e, y⟫ - c| ≤ v at hy
  rw [inner_sub_right, show ⟪e, x⟫ - ⟪e, y⟫ =
    (⟪e, x⟫ - c) - (⟪e, y⟫ - c) by ring]
  exact (abs_sub _ _).trans (add_le_add hx hy)

/-- Actual source-strip pairs obey the effective test direction with only its geometric
angular uncertainty, independently of how many auxiliary fine labels were introduced. -/
theorem packetEffectiveNormal_pair_bound (s e j : ℕ)
    {x y : EuclideanSpace ℝ (Fin 2)} {c u v D : ℝ}
    (hx : x ∈ packetSourceStrip (sourceWavePacketNormal (2 ^ s) j) c u)
    (hy : y ∈ packetSourceStrip (sourceWavePacketNormal (2 ^ s) j) c v)
    (hD : ‖x - y‖ ≤ D) :
    |⟪packetEffectiveNormal s e j, x - y⟫| ≤
      u + v + (2 * Real.pi / (2 : ℝ) ^ min s e) * D := by
  have hpair := packetSourceStrip_pair_bound hx hy
  have hnormal := dist_packetEffectiveNormal_le s e j
  have herror : |⟪packetEffectiveNormal s e j - sourceWavePacketNormal (2 ^ s) j,
      x - y⟫| ≤ (2 * Real.pi / (2 : ℝ) ^ min s e) * D := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [← dist_eq_norm]
    exact mul_le_mul hnormal hD (norm_nonneg _) (by positivity)
  have he : ⟪packetEffectiveNormal s e j, x - y⟫ =
      ⟪sourceWavePacketNormal (2 ^ s) j, x - y⟫ +
        ⟪packetEffectiveNormal s e j - sourceWavePacketNormal (2 ^ s) j, x - y⟫ := by
    rw [inner_sub_left]
    ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hpair herror)

/-- Physical ancestor frames do not depend on the auxiliary terminal cell. -/
theorem dyadicCapPhysicalFrame_ancestor_eq (s t e j k l : ℕ) :
    dyadicCapPhysicalFrame s e (dyadicCapAncestor s t e (j, k)) =
      dyadicCapPhysicalFrame s e (dyadicCapAncestor s t e (j, l)) := by
  unfold dyadicCapAncestor
  split <;> rfl

end FalconerPacking
