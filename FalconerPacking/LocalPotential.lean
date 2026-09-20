/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RadialProjection

/-!
# The localized Riesz potential

`Energy.lean` bounds the `a`-potential of a Frostman measure globally.  The covering arguments of
the manuscript need it localized: the potential over a ball of radius `r` is `O(r ^ (s - a))`,
with a constant independent of the centre and of the radius.

This is the estimate through which a covering hypothesis on the source enters.  Summing it over
the occupied cubes of side `r`, of which a set of upper box dimension `u` has `O(r ^ (-u))`,
gives `O(r ^ (s - a - u))` for the weighted sum of the conditional energies, and the strict
inequality `u < 2 s - 1` is exactly what leaves room for an exponent making the resulting series
converge geometrically.

The proof is the dyadic-annulus argument of `Energy.lean`, run inside the ball instead of over
the whole plane, so that the geometric series starts at scale `r` rather than at scale one.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace FalconerPacking

/-- **The localized Riesz potential.**  For `0 < a < s`, the `a`-potential of an `(s, C)`-Frostman
measure over a ball of radius `r` is `O(r ^ (s - a))`, with a constant independent of the centre
and of the radius.

This is the estimate through which a covering hypothesis enters: summing it over the occupied
cubes of side `r`, of which there are `O(r ^ (-u))`, gives `O(r ^ (s - a - u))`, and the strict
inequality `u < 2 s - 1` is exactly what makes the resulting series converge. -/
theorem exists_bound_setLIntegral_rieszKernel {μ : Measure Plane} {s C a : ℝ}
    (hC : 0 < C) (ha : 0 < a) (has : a < s) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (x : Plane) (r : ℝ), 0 < r → r ≤ 1 →
      ∫⁻ y in Metric.ball x r, rieszKernel a x y ∂μ ≤ ENNReal.ofReal (B * r ^ (s - a)) := by
  classical
  have hs : 0 < s := ha.trans has
  set q : ℝ := (2 : ℝ) ^ (a - s) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqlt : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq1
  refine ⟨C * 2 ^ a * (1 - q)⁻¹, by positivity, ?_⟩
  intro x r hr hr1
  set A : ℕ → Set Plane := fun k =>
    Metric.ball x (r * dyadicRadius k) \ Metric.ball x (r * dyadicRadius (k + 1)) with hA
  have hAmeas : ∀ k, MeasurableSet (A k) :=
    fun k => Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hcover : Metric.ball x r ⊆ {x} ∪ ⋃ k, A k := by
    intro y hy
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h | h
    · exact Or.inl (by simp [dist_eq_zero.1 h.symm])
    refine Or.inr (mem_iUnion.2 ?_)
    have hex : ∃ k : ℕ, r * dyadicRadius k ≤ dist y x := by
      have hto : Tendsto (fun k => r * dyadicRadius k) atTop (𝓝 0) := by
        simpa using tendsto_dyadicRadius.const_mul r
      obtain ⟨k, hk⟩ := (hto.eventually (gt_mem_nhds h)).exists
      exact ⟨k, hk.le⟩
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · exfalso
        have hspec := Nat.find_spec hex
        rw [h0, dyadicRadius_zero, mul_one] at hspec
        exact absurd (Metric.mem_ball.1 hy) (not_lt.2 hspec)
      · exact h0
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    refine ⟨Nat.find hex - 1, ?_, ?_⟩
    · exact Metric.mem_ball.2 (not_le.1 (Nat.find_min hex (by omega)))
    · rw [hsucc]
      exact fun hmem => absurd (Metric.mem_ball.1 hmem) (not_lt.2 (Nat.find_spec hex))
  have hx0 : μ {x} = 0 := measure_singleton_eq_zero_of_isFrostman hs hfr x
  have hann : ∀ k, ∫⁻ y in A k, rieszKernel a x y ∂μ
      ≤ ENNReal.ofReal (C * 2 ^ a * r ^ (s - a)) * ENNReal.ofReal q ^ k := by
    intro k
    have hrk : 0 < r * dyadicRadius (k + 1) := mul_pos hr (dyadicRadius_pos _)
    calc ∫⁻ y in A k, rieszKernel a x y ∂μ
        ≤ ∫⁻ _y in A k, ENNReal.ofReal (r * dyadicRadius (k + 1)) ^ (-a) ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' (hAmeas k)).2 (Eventually.of_forall ?_))
          intro y hy
          refine rieszKernel_le_of_le ha.le ?_
          rw [dist_comm]
          exact not_lt.1 fun hlt => hy.2 (Metric.mem_ball.2 hlt)
      _ = ENNReal.ofReal (r * dyadicRadius (k + 1)) ^ (-a) * μ (A k) := by rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (r * dyadicRadius (k + 1)) ^ (-a)
            * ENNReal.ofReal (C * (r * dyadicRadius k) ^ s) := by
          gcongr
          refine (measure_mono diff_subset).trans (hfr x _ (mul_pos hr (dyadicRadius_pos k)) ?_)
          nlinarith [dyadicRadius_le_one k, dyadicRadius_pos k]
      _ = ENNReal.ofReal (C * 2 ^ a * r ^ (s - a)) * ENNReal.ofReal q ^ k := by
          rw [ENNReal.ofReal_rpow_of_pos hrk,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hrk.le _),
            ← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have h2 : (0 : ℝ) < 2 := by norm_num
          have e1 : (r * dyadicRadius (k + 1)) ^ (-a)
              = r ^ (-a) * dyadicRadius (k + 1) ^ (-a) :=
            Real.mul_rpow hr.le (dyadicRadius_pos _).le
          have e2 : (r * dyadicRadius k) ^ s = r ^ s * dyadicRadius k ^ s :=
            Real.mul_rpow hr.le (dyadicRadius_pos _).le
          have e3 : r ^ (-a) * r ^ s = r ^ (s - a) := by
            rw [← Real.rpow_add hr]; ring_nf
          have hconst := dyadicRadius_kernel_const C a s k
          rw [e1, e2, hqdef]
          linear_combination (r ^ (-a) * r ^ s) * hconst
            + (C * 2 ^ a * ((2 : ℝ) ^ (a - s)) ^ k) * e3
  calc ∫⁻ y in Metric.ball x r, rieszKernel a x y ∂μ
      ≤ ∫⁻ y in {x} ∪ ⋃ k, A k, rieszKernel a x y ∂μ := lintegral_mono_set hcover
    _ ≤ (∫⁻ y in {x}, rieszKernel a x y ∂μ) + ∫⁻ y in ⋃ k, A k, rieszKernel a x y ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ (0 : ℝ≥0∞) + ∑' k, ∫⁻ y in A k, rieszKernel a x y ∂μ := by
        gcongr
        · exact le_of_eq (setLIntegral_measure_zero _ _ hx0)
        · exact lintegral_iUnion_le _ _
    _ ≤ ENNReal.ofReal (C * 2 ^ a * r ^ (s - a)) * (1 - ENNReal.ofReal q)⁻¹ := by
        rw [zero_add]
        calc ∑' k, ∫⁻ y in A k, rieszKernel a x y ∂μ
            ≤ ∑' k, ENNReal.ofReal (C * 2 ^ a * r ^ (s - a)) * ENNReal.ofReal q ^ k :=
              ENNReal.tsum_le_tsum hann
          _ = ENNReal.ofReal (C * 2 ^ a * r ^ (s - a)) * ∑' k, ENNReal.ofReal q ^ k := by
              rw [ENNReal.tsum_mul_left]
          _ = ENNReal.ofReal (C * 2 ^ a * r ^ (s - a)) * (1 - ENNReal.ofReal q)⁻¹ := by
              rw [ENNReal.tsum_geometric]
    _ ≤ ENNReal.ofReal (C * 2 ^ a * (1 - q)⁻¹ * r ^ (s - a)) := by
        rw [show (1 : ℝ≥0∞) - ENNReal.ofReal q = ENNReal.ofReal (1 - q) from by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0.le],
          ← ENNReal.ofReal_inv_of_pos (by linarith),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by rw [show C * 2 ^ a * r ^ (s - a) * (1 - q)⁻¹
          = C * 2 ^ a * (1 - q)⁻¹ * r ^ (s - a) from by ring])

end FalconerPacking
