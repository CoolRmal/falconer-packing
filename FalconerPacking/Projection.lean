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

/-! ### The coordinate-free estimate and the energy comparison

The chart bound degenerates when the chart's slope coefficient is small, but exactly there the
chart's affine function is bounded below on the whole chart, so the two charts together give a
bound through `‖v‖` with no preferred axis.  Integrating that pointwise estimate against
`dμ dμ` by Tonelli gives the projection-energy comparison: the `s`-energy of the projections of
`μ`, averaged over the direction, is at most a constant times the `s`-energy of `μ`.

For a measure of finite `s`-energy this says that almost every projection again has finite
`s`-energy — Marstrand's projection theorem in its energy form.
-/

theorem volume_Icc_neg_one_one : volume (Set.Icc (-1 : ℝ) 1) = 2 := by
  rw [Real.volume_Icc]; norm_num

theorem ofReal_rpow_neg_div {c N s : ℝ} (hc : 0 < c) (hN : 0 < N) :
    (ENNReal.ofReal (N / c)) ^ (-s) = ENNReal.ofReal (c ^ s) * (ENNReal.ofReal N) ^ (-s) := by
  have hreal : (N / c) ^ (-s) = c ^ s * N ^ (-s) := by
    rw [Real.div_rpow hN.le hc.le, Real.rpow_neg hc.le]
    field_simp
  rw [ENNReal.ofReal_rpow_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos hN, hreal,
    ENNReal.ofReal_mul (by positivity)]

/-- One chart of the projection-energy estimate, with the bound expressed through the norm of
the displacement rather than through one of its coordinates.  Either the chart's slope
coefficient is comparable to the norm, and the chart estimate applies, or it is small, and then
the chart's affine function is bounded below on the whole chart. -/
theorem chart_energy_le {s : ℝ} (hs0 : 0 < s) {K₀ : ℝ≥0∞}
    (hK₀ : ∀ v0 v1 : ℝ, v1 ≠ 0 →
      ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v0 + a * v1|) ^ (-s)
        ≤ K₀ * (ENNReal.ofReal |v1|) ^ (-s))
    (v0 v1 N : ℝ) (hN : 0 < N) (hN2 : N ^ 2 = v0 ^ 2 + v1 ^ 2) :
    ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v0 + a * v1|) ^ (-s)
      ≤ (K₀ * ENNReal.ofReal ((2 : ℝ) ^ s) + ENNReal.ofReal (2 * (4 : ℝ) ^ s))
          * (ENNReal.ofReal N) ^ (-s) := by
  rcases le_or_gt (N / 2) |v1| with hbig | hsmall
  · have hv1 : v1 ≠ 0 := by
      intro h; rw [h, abs_zero] at hbig; linarith
    calc ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v0 + a * v1|) ^ (-s)
        ≤ K₀ * (ENNReal.ofReal |v1|) ^ (-s) := hK₀ v0 v1 hv1
      _ ≤ K₀ * (ENNReal.ofReal (N / 2)) ^ (-s) :=
          mul_le_mul_left' (ofReal_rpow_neg_le hs0.le hbig) K₀
      _ = K₀ * ENNReal.ofReal ((2 : ℝ) ^ s) * (ENNReal.ofReal N) ^ (-s) := by
          rw [ofReal_rpow_neg_div (by norm_num) hN, mul_assoc]
      _ ≤ _ := by gcongr; exact le_self_add
  · -- the affine function is bounded below on the whole chart
    have hv0 : (5 / 6 : ℝ) * N ≤ |v0| := by
      have h1 : v1 ^ 2 < N ^ 2 / 4 := by nlinarith [abs_nonneg v1, sq_abs v1]
      nlinarith [abs_nonneg v0, sq_abs v0]
    have hlow : ∀ a ∈ Set.Icc (-1 : ℝ) 1, N / 4 ≤ |v0 + a * v1| := by
      intro a ha
      have hav : |a * v1| ≤ |v1| := by
        rw [abs_mul]
        nlinarith [abs_nonneg v1, abs_nonneg a, abs_le.2 ha, (abs_le.1 (abs_le.2 ha))]
      have h2 := abs_sub_abs_le_abs_sub v0 (-(a * v1))
      simp only [abs_neg, sub_neg_eq_add] at h2
      have hv1s : |v1| < N / 2 := hsmall
      linarith
    calc ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v0 + a * v1|) ^ (-s)
        ≤ ∫⁻ _a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal (N / 4)) ^ (-s) := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2
            (Filter.Eventually.of_forall ?_))
          intro a ha
          exact ofReal_rpow_neg_le hs0.le (hlow a ha)
      _ = (ENNReal.ofReal (N / 4)) ^ (-s) * volume (Set.Icc (-1 : ℝ) 1) := by
          rw [setLIntegral_const]
      _ = (ENNReal.ofReal (N / 4)) ^ (-s) * 2 := by rw [volume_Icc_neg_one_one]
      _ = ENNReal.ofReal (2 * (4 : ℝ) ^ s) * (ENNReal.ofReal N) ^ (-s) := by
          rw [ofReal_rpow_neg_div (by norm_num) hN,
            show (2 : ℝ) * (4 : ℝ) ^ s = (4 : ℝ) ^ s * 2 by ring,
            ENNReal.ofReal_mul (by positivity),
            show ENNReal.ofReal (2 : ℝ) = 2 from by simp]
          ring
      _ ≤ _ := by gcongr; exact le_add_self


/-- **The coordinate-free projection-energy estimate.**  Summed over the two slope charts, which
together cover the circle of directions, the `s`-Riesz kernel of the projection of a fixed
displacement is integrable with a bound proportional to the kernel of the displacement itself.

This is the pointwise input to the projection-energy comparison: integrating it against
`dμ dμ` shows that the average over directions of the `s`-energy of a projected measure is at
most a constant times the `s`-energy of the measure, for every `0 < s < 1`. -/
theorem exists_bound_lintegral_inv_rpow_norm {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ v : Plane, v ≠ 0 →
      (∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪v, normalSlope a⟫|) ^ (-s))
        + (∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪v, normalSlopeT a⟫|) ^ (-s))
        ≤ K * (ENNReal.ofReal ‖v‖) ^ (-s) := by
  obtain ⟨K₀, hK₀top, hK₀⟩ := exists_bound_lintegral_inv_rpow hs0 hs1
  refine ⟨2 * (K₀ * ENNReal.ofReal ((2 : ℝ) ^ s) + ENNReal.ofReal (2 * (4 : ℝ) ^ s)), ?_, ?_⟩
  · exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top hK₀top ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  intro v hv
  have hN : (0 : ℝ) < ‖v‖ := norm_pos_iff.2 hv
  have hN2 : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := norm_sq_plane v
  have hc1 : (∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪v, normalSlope a⟫|) ^ (-s))
      = ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v 0 + a * v 1|) ^ (-s) :=
    lintegral_congr fun a => by rw [inner_normalSlope]
  have hc2 : (∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪v, normalSlopeT a⟫|) ^ (-s))
      = ∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |v 1 + a * v 0|) ^ (-s) :=
    lintegral_congr fun a => by rw [inner_normalSlopeT]
  rw [hc1, hc2, two_mul, add_mul]
  exact add_le_add (chart_energy_le hs0 hK₀ (v 0) (v 1) ‖v‖ hN hN2)
    (chart_energy_le hs0 hK₀ (v 1) (v 0) ‖v‖ hN (by rw [hN2]; ring))


/-- The pointwise estimate extended over the diagonal, where both sides are infinite. -/
theorem exists_bound_lintegral_inv_rpow_norm' {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ K ≠ 0 ∧ ∀ v : Plane,
      (∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪v, normalSlope a⟫|) ^ (-s))
        + (∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪v, normalSlopeT a⟫|) ^ (-s))
        ≤ K * (ENNReal.ofReal ‖v‖) ^ (-s) := by
  obtain ⟨K, hKtop, hK⟩ := exists_bound_lintegral_inv_rpow_norm hs0 hs1
  refine ⟨K + 1, by simp [hKtop], by simp, fun v => ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · have htop : (K + 1) * (ENNReal.ofReal ‖(0 : Plane)‖) ^ (-s) = ⊤ := by
      rw [norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith)]
      exact ENNReal.mul_top (by simp)
    rw [htop]
    exact le_top
  · exact le_trans (hK v hv) (by gcongr; exact le_self_add)

/-- **The projection-energy comparison.**  Averaged over the two slope charts, the `s`-energy of
the projection of `μ` is at most a constant times the `s`-energy of `μ`, for every `0 < s < 1`.

For a measure of finite `s`-energy this says that almost every projection again has finite
`s`-energy, which is Marstrand's projection theorem in its energy form, and the reason the
projected densities of Section 2 of the manuscript are square integrable. -/
theorem exists_bound_lintegral_projEnergy (μ : Measure Plane) [SFinite μ] {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
      (∫⁻ a in Set.Icc (-1 : ℝ) 1, (∫⁻ p : Plane × Plane,
          (ENNReal.ofReal |⟪p.1 - p.2, normalSlope a⟫|) ^ (-s) ∂(μ.prod μ)))
        + (∫⁻ a in Set.Icc (-1 : ℝ) 1, (∫⁻ p : Plane × Plane,
          (ENNReal.ofReal |⟪p.1 - p.2, normalSlopeT a⟫|) ^ (-s) ∂(μ.prod μ)))
        ≤ K * rieszEnergy μ s := by
  obtain ⟨K, hKtop, _, hK⟩ := exists_bound_lintegral_inv_rpow_norm' hs0 hs1
  refine ⟨K, hKtop, ?_⟩
  have hmeasF : ∀ e : ℝ → Plane,
      (Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, e z.1⟫) →
      Measurable fun z : ℝ × (Plane × Plane) =>
        (ENNReal.ofReal |⟪z.2.1 - z.2.2, e z.1⟫|) ^ (-s) := by
    intro e hg
    exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hg)).pow_const _
  have hswap : ∀ e : ℝ → Plane,
      (Measurable fun z : ℝ × (Plane × Plane) => ⟪z.2.1 - z.2.2, e z.1⟫) →
      (∫⁻ a in Set.Icc (-1 : ℝ) 1, (∫⁻ p : Plane × Plane,
        (ENNReal.ofReal |⟪p.1 - p.2, e a⟫|) ^ (-s) ∂(μ.prod μ)))
      = ∫⁻ p : Plane × Plane, (∫⁻ a in Set.Icc (-1 : ℝ) 1,
        (ENNReal.ofReal |⟪p.1 - p.2, e a⟫|) ^ (-s)) ∂(μ.prod μ) := by
    intro e hg
    exact lintegral_lintegral_swap (hmeasF e hg).aemeasurable
  rw [hswap _ measurable_inner_normalSlope, hswap _ measurable_inner_normalSlopeT,
    ← lintegral_add_left _]
  · calc ∫⁻ p : Plane × Plane,
          ((∫⁻ a in Set.Icc (-1 : ℝ) 1, (ENNReal.ofReal |⟪p.1 - p.2, normalSlope a⟫|) ^ (-s))
            + ∫⁻ a in Set.Icc (-1 : ℝ) 1,
              (ENNReal.ofReal |⟪p.1 - p.2, normalSlopeT a⟫|) ^ (-s)) ∂(μ.prod μ)
        ≤ ∫⁻ p : Plane × Plane, K * (ENNReal.ofReal ‖p.1 - p.2‖) ^ (-s) ∂(μ.prod μ) :=
          lintegral_mono fun p => hK _
      _ = K * ∫⁻ p : Plane × Plane, (ENNReal.ofReal ‖p.1 - p.2‖) ^ (-s) ∂(μ.prod μ) :=
          lintegral_const_mul _ (by
            exact (ENNReal.measurable_ofReal.comp
              ((measurable_fst.sub measurable_snd).norm)).pow_const _)
      _ = K * rieszEnergy μ s := by
          rw [rieszEnergy]
          congr 1
          rw [lintegral_prod]
          · exact lintegral_congr fun x => lintegral_congr fun y => by
              rw [rieszKernel, ← dist_eq_norm]
          · exact ((ENNReal.measurable_ofReal.comp
              ((measurable_fst.sub measurable_snd).norm)).pow_const _).aemeasurable
  · exact Measurable.lintegral_prod_left' (μ := volume.restrict (Set.Icc (-1 : ℝ) 1))
      (hmeasF _ measurable_inner_normalSlope)

end FalconerPacking
