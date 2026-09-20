/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Caps

/-!
# The projection-energy estimate

Module 8 of the manuscript's ledger begins with the projection-energy identity: the `s`-energy of
a measure, averaged over the projections `π_θ x = ⟪x, θ⟫`, is comparable to the `s`-energy of the
measure itself, for `0 < s < 1`.  That comparison is the reason projected measures inherit
Frostman exponents, and it is the starting point of the angular Sobolev estimate of Section 2 of
the manuscript.  Mathlib has no projection theory at all, so it is built here.

The whole comparison reduces to a one-dimensional statement about the slope charts of
`Tubes.lean`: for a fixed displacement `v`, the `s`-Riesz kernel of `a ↦ ⟪v, normalSlope a⟫` is
integrable over the chart, with a bound proportional to the kernel of `v` itself.  That is
`exists_bound_lintegral_inv_rpow`.

The proof is the dyadic-annulus argument that `Energy.lean` uses for Frostman measures, with the
directional estimate `volume_setOf_abs_linear_lt` in the role of the Frostman ball bound: on the
annulus where `|v 0 + a * v 1|` is of size `2 ^ (-k) |v 1|`, the kernel is at most
`2 ^ (k s) |v 1| ^ (-s)` and the slopes occupy measure at most `2 ^ (1 - k)`, so the annuli
contribute a geometric series of ratio `2 ^ (s - 1)`, convergent exactly when `s < 1`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

theorem ofReal_rpow_neg_le {s r r' : ℝ} (hs : 0 ≤ s) (h : r' ≤ r) :
    (ENNReal.ofReal r) ^ (-s) ≤ (ENNReal.ofReal r') ^ (-s) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) hs)

/-- **The projection-energy estimate.**  For `0 < s < 1` the `s`-Riesz kernel of a nonconstant
affine function of the slope is integrable over the chart, with a bound proportional to the
kernel of the slope coefficient.  This is the one-dimensional heart of Marstrand-type projection
theory, and it is what makes projected energies comparable to the original one.

The proof is the dyadic-annulus argument of `Energy.lean`, with the directional estimate
`volume_setOf_abs_linear_lt` in place of the Frostman ball bound. -/
theorem exists_bound_lintegral_inv_rpow {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ v0 v1 : ℝ, v1 ≠ 0 →
      ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v0 + a * v1|) ^ (-s)
        ≤ K * (ENNReal.ofReal |v1|) ^ (-s) := by
  classical
  set q : ℝ := (2 : ℝ) ^ (s - 1) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqlt : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq1
  refine ⟨2 + ENNReal.ofReal (2 * (2 : ℝ) ^ s) * (1 - ENNReal.ofReal q)⁻¹, ?_, ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨by simp, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hqlt).ne'
  intro v0 v1 hv1
  have habs : (0 : ℝ) < |v1| := abs_pos.2 hv1
  set g : ℝ → ℝ := fun a => |v0 + a * v1| with hg
  set A : ℕ → Set ℝ := fun k =>
    {a | g a < dyadicRadius k * |v1|} \ {a | g a < dyadicRadius (k + 1) * |v1|} with hA
  set Z : Set ℝ := {a | g a = 0} with hZ
  set F : Set ℝ := {a ∈ Set.Icc (-1 : ℝ) 1 | |v1| ≤ g a} with hF
  have hgmeas : Measurable g := by
    rw [hg]
    exact ((continuous_const.add (continuous_id'.mul continuous_const)).abs).measurable
  have hAmeas : ∀ k, MeasurableSet (A k) := fun k =>
    (measurableSet_lt hgmeas measurable_const).diff (measurableSet_lt hgmeas measurable_const)
  have hZmeas : MeasurableSet Z := hgmeas (measurableSet_singleton 0)
  have hFmeas : MeasurableSet F :=
    measurableSet_Icc.inter (measurableSet_le measurable_const hgmeas)
  -- the cover
  have hcover : Set.Icc (-1 : ℝ) 1 ⊆ (Z ∪ ⋃ k, A k) ∪ F := by
    intro a ha
    rcases eq_or_lt_of_le (abs_nonneg (v0 + a * v1)) with h0 | h0
    · exact Or.inl (Or.inl h0.symm)
    rcases le_or_gt |v1| (g a) with hbig | hsmall
    · exact Or.inr ⟨ha, hbig⟩
    refine Or.inl (Or.inr (mem_iUnion.2 ?_))
    have hex : ∃ k : ℕ, dyadicRadius k * |v1| ≤ g a := by
      have hto : Filter.Tendsto (fun k => dyadicRadius k * |v1|) Filter.atTop (nhds 0) := by
        simpa using tendsto_dyadicRadius.mul_const |v1|
      obtain ⟨k, hk⟩ := (hto.eventually (gt_mem_nhds h0)).exists
      exact ⟨k, hk.le⟩
    refine ⟨Nat.find hex - 1, ?_, ?_⟩
    · have hmin : ¬ dyadicRadius (Nat.find hex - 1) * |v1| ≤ g a := by
        refine Nat.find_min hex ?_
        have hpos : 0 < Nat.find hex := by
          rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
          · exfalso
            have := Nat.find_spec hex
            rw [h, dyadicRadius_zero, one_mul] at this
            linarith
          · exact h
        omega
      exact not_le.1 hmin
    · have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by
        have hpos : 0 < Nat.find hex := by
          rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
          · exfalso
            have := Nat.find_spec hex
            rw [h, dyadicRadius_zero, one_mul] at this
            linarith
          · exact h
        omega
      rw [Set.mem_setOf_eq, hsucc]
      exact not_lt.2 (Nat.find_spec hex)
  set T : ℝ≥0∞ := (ENNReal.ofReal |v1|) ^ (-s) with hT
  have hZnull : volume Z = 0 := by
    refine measure_mono_null (fun a ha => ?_) (Real.volume_singleton (a := -v0 / v1))
    have hz : v0 + a * v1 = 0 := abs_eq_zero.1 ha
    rw [Set.mem_singleton_iff, eq_div_iff hv1]
    linarith
  have hfar : ∫⁻ a in F, (ENNReal.ofReal (g a)) ^ (-s) ≤ 2 * T := by
    calc ∫⁻ a in F, (ENNReal.ofReal (g a)) ^ (-s)
        ≤ ∫⁻ _a in F, T := by
          refine lintegral_mono_ae ((ae_restrict_iff' hFmeas).2 (Filter.Eventually.of_forall ?_))
          intro a ha
          exact ofReal_rpow_neg_le hs0.le ha.2
      _ = T * volume F := by rw [setLIntegral_const]
      _ ≤ T * 2 := by
          gcongr
          calc volume F ≤ volume (Set.Icc (-1 : ℝ) 1) := measure_mono fun a ha => ha.1
            _ = 2 := by rw [Real.volume_Icc]; norm_num
      _ = 2 * T := by ring
  have hAvol : ∀ k, volume (A k) ≤ ENNReal.ofReal (2 * dyadicRadius k) := by
    intro k
    refine le_trans (measure_mono fun a ha => ha.1) ?_
    refine le_trans (volume_setOf_abs_linear_lt v0 v1 (dyadicRadius k * |v1|) hv1) ?_
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    field_simp
  have hann : ∀ k, ∫⁻ a in A k, (ENNReal.ofReal (g a)) ^ (-s)
      ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ s) * ENNReal.ofReal q ^ k * T := by
    intro k
    have hdr1 : (0 : ℝ) < dyadicRadius (k + 1) * |v1| :=
      mul_pos (dyadicRadius_pos _) habs
    calc ∫⁻ a in A k, (ENNReal.ofReal (g a)) ^ (-s)
        ≤ ∫⁻ _a in A k, (ENNReal.ofReal (dyadicRadius (k + 1) * |v1|)) ^ (-s) := by
          refine lintegral_mono_ae ((ae_restrict_iff' (hAmeas k)).2
            (Filter.Eventually.of_forall ?_))
          intro a ha
          exact ofReal_rpow_neg_le hs0.le (not_lt.1 ha.2)
      _ = (ENNReal.ofReal (dyadicRadius (k + 1) * |v1|)) ^ (-s) * volume (A k) := by
          rw [setLIntegral_const]
      _ ≤ (ENNReal.ofReal (dyadicRadius (k + 1) * |v1|)) ^ (-s)
            * ENNReal.ofReal (2 * dyadicRadius k) := by gcongr; exact hAvol k
      _ = ENNReal.ofReal (2 * (2 : ℝ) ^ s) * ENNReal.ofReal q ^ k * T := by
          rw [hT, ENNReal.ofReal_rpow_of_pos hdr1, ENNReal.ofReal_rpow_of_pos habs,
            ← ENNReal.ofReal_pow hq0.le,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hdr1.le _),
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have hsplit : (dyadicRadius (k + 1) * |v1|) ^ (-s)
              = dyadicRadius (k + 1) ^ (-s) * |v1| ^ (-s) :=
            Real.mul_rpow (dyadicRadius_pos _).le habs.le
          have hconst := dyadicRadius_kernel_const 2 s 1 k
          rw [Real.rpow_one] at hconst
          rw [hsplit, hqdef]
          linear_combination |v1| ^ (-s) * hconst
  calc ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v0 + a * v1|) ^ (-s)
      ≤ ∫⁻ a in (Z ∪ ⋃ k, A k) ∪ F, (ENNReal.ofReal (g a)) ^ (-s) := lintegral_mono_set hcover
    _ ≤ (∫⁻ a in Z ∪ ⋃ k, A k, (ENNReal.ofReal (g a)) ^ (-s))
          + ∫⁻ a in F, (ENNReal.ofReal (g a)) ^ (-s) := lintegral_union_le _ _ _
    _ ≤ ((∫⁻ a in Z, (ENNReal.ofReal (g a)) ^ (-s))
          + ∫⁻ a in ⋃ k, A k, (ENNReal.ofReal (g a)) ^ (-s))
          + ∫⁻ a in F, (ENNReal.ofReal (g a)) ^ (-s) := by
        gcongr; exact lintegral_union_le _ _ _
    _ ≤ ((0 : ℝ≥0∞) + ∑' k, ∫⁻ a in A k, (ENNReal.ofReal (g a)) ^ (-s)) + 2 * T := by
        gcongr
        · exact le_of_eq (setLIntegral_measure_zero _ _ hZnull)
        · exact lintegral_iUnion_le _ _
    _ ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ s) * (1 - ENNReal.ofReal q)⁻¹ * T + 2 * T := by
        gcongr
        rw [zero_add]
        calc ∑' k, ∫⁻ a in A k, (ENNReal.ofReal (g a)) ^ (-s)
            ≤ ∑' k, ENNReal.ofReal (2 * (2 : ℝ) ^ s) * ENNReal.ofReal q ^ k * T :=
              ENNReal.tsum_le_tsum hann
          _ = ENNReal.ofReal (2 * (2 : ℝ) ^ s) * (∑' k, ENNReal.ofReal q ^ k) * T := by
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
          _ = ENNReal.ofReal (2 * (2 : ℝ) ^ s) * (1 - ENNReal.ofReal q)⁻¹ * T := by
              rw [ENNReal.tsum_geometric]
    _ = (2 + ENNReal.ofReal (2 * (2 : ℝ) ^ s) * (1 - ENNReal.ofReal q)⁻¹) * T := by ring

end FalconerPacking
