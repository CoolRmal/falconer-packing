/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PacketDirectionCounting
import FalconerPacking.SourceWavePackets
import FalconerPacking.LocalizedPacketMass

/-!
# Pair multiplicity of the actual source packet grid

The enlarged strips have bounded overlap in their offset coordinate. For separated pairs,
the simultaneous angular restriction bounds the full packet multiplicity by the inflation
factor, rather than by the total number of packets.
-/

noncomputable section

open Set Metric Classical
open scoped RealInnerProductSpace

namespace FalconerPacking

/-- At one direction, the enlarged offset grid has uniformly bounded overlap. -/
theorem card_enlarged_strip_offsets_le (J : Finset ℤ) {w C t : ℝ}
    (hw : 0 < w) (hC : 0 ≤ C) :
    ((J.filter (fun (k : ℤ) ↦ |t - w * (k : ℝ)| ≤ C * w)).card : ℝ) ≤ 2 * C + 1 := by
  apply int_finset_card_le_real_diameter _ (by positivity)
  intro k hk l hl
  have hk' := (Finset.mem_filter.mp hk).2
  have hl' := (Finset.mem_filter.mp hl).2
  have h : |w * ((k : ℝ) - l)| ≤ 2 * C * w := by
    have he : w * ((k : ℝ) - l) = (t - w * l) - (t - w * k) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith)
  rw [abs_mul, abs_of_pos hw] at h
  nlinarith

/-- The concrete angular and offset grid counts separated source-pin pairs with only
linear inflation loss. -/
theorem card_packet_pair_strips_le {N : ℕ} (hN : 0 < N) (J : Finset ℤ)
    {w C δ : ℝ} (hw : 0 < w) (hC : 0 ≤ C) (hδ : 0 < δ)
    (x y : EuclideanSpace ℝ (Fin 2)) (hxy : δ ≤ ‖y - x‖) :
    ((((Finset.range N) ×ˢ J).filter (fun p ↦
      x ∈ packetSourceStrip (sourceWavePacketNormal N p.1) (w * p.2) (C * w) ∧
      y ∈ packetSourceStrip (sourceWavePacketNormal N p.1) (w * p.2) (C * w))).card : ℝ) ≤
      (2 * C + 1) * (8 * C * w * N / δ + 4 * Real.pi) := by
  let cond (j : ℕ) (k : ℤ) :=
    x ∈ packetSourceStrip (sourceWavePacketNormal N j) (w * k) (C * w) ∧
    y ∈ packetSourceStrip (sourceWavePacketNormal N j) (w * k) (C * w)
  let good (j : ℕ) := |⟪sourceWavePacketNormal N j, y - x⟫| ≤ 2 * C * w
  have htrans {j k} (h : cond j k) : good j := by
    have hx : |⟪sourceWavePacketNormal N j, x⟫ - w * k| ≤ C * w := h.1
    have hy : |⟪sourceWavePacketNormal N j, y⟫ - w * k| ≤ C * w := h.2
    change |⟪sourceWavePacketNormal N j, y - x⟫| ≤ _
    rw [inner_sub_right, show ⟪sourceWavePacketNormal N j, y⟫ -
      ⟪sourceWavePacketNormal N j, x⟫ =
      (⟪sourceWavePacketNormal N j, y⟫ - w * k) -
        (⟪sourceWavePacketNormal N j, x⟫ - w * k) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hcount (j : ℕ) : ((J.filter (cond j)).card : ℝ) ≤
      if good j then 2 * C + 1 else 0 := by
    by_cases hj : good j
    · rw [if_pos hj]
      apply le_trans ?_
        (card_enlarged_strip_offsets_le J (t := ⟪sourceWavePacketNormal N j, x⟫) hw hC)
      exact_mod_cast Finset.card_le_card (show J.filter (cond j) ⊆
        J.filter (fun k ↦ |⟪sourceWavePacketNormal N j, x⟫ - w * k| ≤ C * w) from
        fun k hk ↦ Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2.1⟩)
    · rw [if_neg hj]
      have he : J.filter (cond j) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        exact fun _ _ hk ↦ hj (htrans hk)
      simp only [he, Finset.card_empty, Nat.cast_zero, le_refl]
  have hz : y - x ≠ 0 := norm_pos_iff.mp (hδ.trans_le hxy)
  have hc := card_transverse_angularGrid_le hN hz (by positivity : 0 ≤ 2 * C * w)
  have hcard : (((Finset.range N).filter good).card : ℝ) ≤
      8 * C * w * N / δ + 4 * Real.pi := by
    calc
      _ ≤ 4 * (2 * C * w) * N / ‖y - x‖ + 4 * Real.pi := hc
      _ ≤ 4 * (2 * C * w) * N / δ + 4 * Real.pi := by gcongr
      _ = _ := by ring
  calc
    _ = ∑ j ∈ Finset.range N, ((J.filter (cond j)).card : ℝ) := by
      simp only [Finset.card_filter, Finset.sum_product, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, cond]
    _ ≤ ∑ j ∈ Finset.range N, if good j then 2 * C + 1 else 0 :=
      Finset.sum_le_sum fun j _ ↦ hcount j
    _ = (2 * C + 1) * (((Finset.range N).filter good).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard (by positivity)

end FalconerPacking
