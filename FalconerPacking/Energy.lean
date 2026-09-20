/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Dimensions
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Frostman measures and Riesz energies

Section 1.1 of the manuscript, and the first item of module 6: *an `s`-Frostman probability on a
bounded set has finite `a`-energy for `0 < a < s`, by summing the bound on dyadic spatial
annuli.*

The Riesz kernel is taken in `ℝ≥0∞`, so that it is `∞` on the diagonal instead of being silently
totalized to zero, as Lean's real `rpow` would do.  A Frostman measure has no atoms, so the
diagonal is null and contributes nothing.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- A measure is `(s, C)`-Frostman if every ball of radius at most one has mass at most
`C * r ^ s`. -/
def IsFrostman (μ : Measure Plane) (s C : ℝ) : Prop :=
  ∀ (x : Plane) (r : ℝ), 0 < r → r ≤ 1 → μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ s)

/-- The Riesz kernel `|x - y| ^ (-a)`, valued in `ℝ≥0∞` and infinite on the diagonal. -/
def rieszKernel (a : ℝ) (x y : Plane) : ℝ≥0∞ := ENNReal.ofReal (dist x y) ^ (-a)

/-- The Riesz `a`-energy of a measure. -/
def rieszEnergy (μ : Measure Plane) (a : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, rieszKernel a x y ∂μ ∂μ

section Dyadic

/-- The dyadic radii `2⁻ᵏ`. -/
def dyadicRadius (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℝ))

theorem dyadicRadius_pos (k : ℕ) : 0 < dyadicRadius k :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem dyadicRadius_le_one (k : ℕ) : dyadicRadius k ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.2 (Nat.cast_nonneg k))

/-- A dyadic radius raised to a real power is again geometric. -/
theorem dyadicRadius_rpow (k : ℕ) (s : ℝ) : dyadicRadius k ^ s = ((2 : ℝ) ^ (-s)) ^ k := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [dyadicRadius, ← Real.rpow_mul h2, ← Real.rpow_natCast ((2 : ℝ) ^ (-s)) k,
    ← Real.rpow_mul h2]
  ring_nf

theorem dyadicRadius_zero : dyadicRadius 0 = 1 := by
  simp [dyadicRadius]

theorem dyadicRadius_succ_lt (k : ℕ) : dyadicRadius (k + 1) < dyadicRadius k := by
  rw [dyadicRadius, dyadicRadius, Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
  push_cast
  linarith

theorem tendsto_dyadicRadius : Tendsto dyadicRadius atTop (𝓝 0) := by
  have h : ∀ k : ℕ, dyadicRadius k = ((1 : ℝ) / 2) ^ k := fun k ↦ two_rpow_neg_natCast k
  refine Tendsto.congr (fun k ↦ (h k).symm) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The Frostman bound on the annulus `[2⁻ᵏ⁻¹, 2⁻ᵏ)`, in closed form. -/
theorem dyadicRadius_kernel_const (C a s : ℝ) (k : ℕ) :
    (dyadicRadius (k + 1)) ^ (-a) * (C * (dyadicRadius k) ^ s)
      = C * 2 ^ a * ((2 : ℝ) ^ (a - s)) ^ k := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h2' : (0 : ℝ) < 2 := by norm_num
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [dyadicRadius, dyadicRadius, hcast]
  have e1 : ((2 : ℝ) ^ (-((k : ℝ) + 1))) ^ (-a) = (2 : ℝ) ^ (((k : ℝ) + 1) * a) := by
    rw [← Real.rpow_mul h2]; ring_nf
  have e2 : ((2 : ℝ) ^ (-(k : ℝ))) ^ s = (2 : ℝ) ^ (-((k : ℝ) * s)) := by
    rw [← Real.rpow_mul h2]; ring_nf
  have e3 : ((2 : ℝ) ^ (a - s)) ^ k = (2 : ℝ) ^ ((a - s) * (k : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (a - s)) k, ← Real.rpow_mul h2]
  rw [e1, e2, e3,
    show (2 : ℝ) ^ (((k : ℝ) + 1) * a) * (C * (2 : ℝ) ^ (-((k : ℝ) * s)))
      = C * ((2 : ℝ) ^ (((k : ℝ) + 1) * a) * (2 : ℝ) ^ (-((k : ℝ) * s))) from by ring,
    show C * (2 : ℝ) ^ a * (2 : ℝ) ^ ((a - s) * (k : ℝ))
      = C * ((2 : ℝ) ^ a * (2 : ℝ) ^ ((a - s) * (k : ℝ))) from by ring,
    ← Real.rpow_add h2', ← Real.rpow_add h2']
  ring_nf

end Dyadic

section Atoms

/-- A Frostman measure has no atoms. -/
theorem measure_singleton_eq_zero_of_isFrostman {μ : Measure Plane} {s C : ℝ} (hs : 0 < s)
    (hfr : IsFrostman μ s C) (x : Plane) : μ {x} = 0 := by
  have hbound : ∀ k : ℕ, μ {x} ≤ ENNReal.ofReal (C * dyadicRadius k ^ s) := by
    intro k
    have hmem : μ {x} ≤ μ (Metric.ball x (dyadicRadius k)) :=
      measure_mono (Set.singleton_subset_iff.2 (Metric.mem_ball_self (dyadicRadius_pos k)))
    exact hmem.trans (hfr x _ (dyadicRadius_pos k) (dyadicRadius_le_one k))
  have htend : Tendsto (fun k : ℕ ↦ ENNReal.ofReal (C * dyadicRadius k ^ s)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun k : ℕ ↦ C * dyadicRadius k ^ s) atTop (𝓝 0) := by
      have hq0 : (0 : ℝ) < (2 : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by norm_num) _
      have hq1 : ((2 : ℝ) ^ (-s)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hzero : Tendsto (fun k : ℕ ↦ dyadicRadius k ^ s) atTop (𝓝 0) := by
        refine Tendsto.congr (fun k ↦ (dyadicRadius_rpow k s).symm) ?_
        exact tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
      have := hzero.const_mul C
      rwa [mul_zero] at this
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    rwa [ENNReal.ofReal_zero] at this
  exact nonpos_iff_eq_zero.1 (ge_of_tendsto htend (Eventually.of_forall hbound))

end Atoms

section Bound

variable {μ : Measure Plane} {s C a : ℝ}

/-- Away from the diagonal the kernel is controlled by the inner radius of a dyadic annulus. -/
theorem rieszKernel_le_of_le {x y : Plane} {r : ℝ} (ha : 0 ≤ a) (h : r ≤ dist x y) :
    rieszKernel a x y ≤ ENNReal.ofReal r ^ (-a) := by
  rw [rieszKernel, ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h) ha)

/-- **Frostman measures have uniformly bounded Riesz potentials.**  For `0 < a < s` the potential
of an `(s, C)`-Frostman finite measure is bounded independently of the point: sum the Frostman
bound over the dyadic annuli. -/
theorem exists_bound_lintegral_rieszKernel [IsFiniteMeasure μ] (hC : 0 < C) (ha : 0 < a)
    (has : a < s) (hfr : IsFrostman μ s C) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x, ∫⁻ y, rieszKernel a x y ∂μ ≤ B := by
  classical
  have hs : 0 < s := ha.trans has
  set q : ℝ := (2 : ℝ) ^ (a - s) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqlt : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq1
  refine ⟨μ univ + ENNReal.ofReal (C * 2 ^ a) * (1 - ENNReal.ofReal q)⁻¹, ?_, ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hqlt).ne'
  intro x
  set A : ℕ → Set Plane := fun k ↦
    Metric.ball x (dyadicRadius k) \ Metric.ball x (dyadicRadius (k + 1)) with hA
  set F : Set Plane := (Metric.ball x 1)ᶜ with hF
  have hAmeas : ∀ k, MeasurableSet (A k) :=
    fun k ↦ Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hFmeas : MeasurableSet F := Metric.isOpen_ball.measurableSet.compl
  have hcover : (univ : Set Plane) ⊆ ({x} ∪ ⋃ k, A k) ∪ F := by
    intro y _
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with h | h
    · exact Or.inl (Or.inl (by simp [dist_eq_zero.1 h.symm]))
    rcases le_or_gt 1 (dist y x) with h1 | h1
    · exact Or.inr (by simpa [hF, Metric.mem_ball, not_lt] using h1)
    refine Or.inl (Or.inr (mem_iUnion.2 ?_))
    have hex : ∃ k : ℕ, dyadicRadius k ≤ dist y x := by
      obtain ⟨k, hk⟩ := (tendsto_dyadicRadius.eventually (gt_mem_nhds h)).exists
      exact ⟨k, hk.le⟩
    refine ⟨Nat.find hex - 1, ?_⟩
    have hspec : dyadicRadius (Nat.find hex) ≤ dist y x := Nat.find_spec hex
    have hpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
      · rw [h0, dyadicRadius_zero] at hspec
        exact absurd hspec (not_le.2 h1)
      · exact h0
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have hmin : ¬ dyadicRadius (Nat.find hex - 1) ≤ dist y x :=
      Nat.find_min hex (by omega)
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.2 (not_le.1 hmin)
    · rw [hsucc]
      exact fun hmem ↦ absurd (Metric.mem_ball.1 hmem) (not_lt.2 hspec)
  have hx0 : μ {x} = 0 := measure_singleton_eq_zero_of_isFrostman hs hfr x
  have hfar : ∫⁻ y in F, rieszKernel a x y ∂μ ≤ μ univ := by
    calc ∫⁻ y in F, rieszKernel a x y ∂μ ≤ ∫⁻ _y in F, (1 : ℝ≥0∞) ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hFmeas).2 (Eventually.of_forall ?_))
          intro y hy
          have h1 : (1 : ℝ) ≤ dist x y := by
            rw [dist_comm]
            simpa [hF, Metric.mem_ball, not_lt] using hy
          simpa using rieszKernel_le_of_le (r := 1) ha.le h1
      _ = μ F := by rw [setLIntegral_const, one_mul]
      _ ≤ μ univ := measure_mono (subset_univ _)
  have hann : ∀ k, ∫⁻ y in A k, rieszKernel a x y ∂μ
      ≤ ENNReal.ofReal (C * 2 ^ a) * ENNReal.ofReal q ^ k := by
    intro k
    calc ∫⁻ y in A k, rieszKernel a x y ∂μ
        ≤ ∫⁻ _y in A k, ENNReal.ofReal (dyadicRadius (k + 1)) ^ (-a) ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' (hAmeas k)).2 (Eventually.of_forall ?_))
          intro y hy
          refine rieszKernel_le_of_le ha.le ?_
          rw [dist_comm]
          exact not_lt.1 fun hlt ↦ hy.2 (Metric.mem_ball.2 hlt)
      _ = ENNReal.ofReal (dyadicRadius (k + 1)) ^ (-a) * μ (A k) := by rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (dyadicRadius (k + 1)) ^ (-a)
            * ENNReal.ofReal (C * dyadicRadius k ^ s) := by
          gcongr
          exact (measure_mono (diff_subset)).trans
            (hfr x _ (dyadicRadius_pos k) (dyadicRadius_le_one k))
      _ = ENNReal.ofReal (C * 2 ^ a) * ENNReal.ofReal q ^ k := by
          rw [ENNReal.ofReal_rpow_of_pos (dyadicRadius_pos (k + 1)),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicRadius_pos (k + 1)).le _),
            ← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_mul (by positivity), hqdef,
            dyadicRadius_kernel_const C a s k]
  calc ∫⁻ y, rieszKernel a x y ∂μ
      = ∫⁻ y in univ, rieszKernel a x y ∂μ := by rw [Measure.restrict_univ]
    _ ≤ ∫⁻ y in ({x} ∪ ⋃ k, A k) ∪ F, rieszKernel a x y ∂μ := lintegral_mono_set hcover
    _ ≤ (∫⁻ y in {x} ∪ ⋃ k, A k, rieszKernel a x y ∂μ) + ∫⁻ y in F, rieszKernel a x y ∂μ :=
        lintegral_union_le _ _ _
    _ ≤ ((∫⁻ y in {x}, rieszKernel a x y ∂μ) + ∫⁻ y in ⋃ k, A k, rieszKernel a x y ∂μ)
          + ∫⁻ y in F, rieszKernel a x y ∂μ := by
        gcongr
        exact lintegral_union_le _ _ _
    _ ≤ ((0 : ℝ≥0∞) + ∑' k, ∫⁻ y in A k, rieszKernel a x y ∂μ) + μ univ := by
        gcongr
        · exact le_of_eq (setLIntegral_measure_zero _ _ hx0)
        · exact lintegral_iUnion_le _ _
    _ ≤ ENNReal.ofReal (C * 2 ^ a) * (1 - ENNReal.ofReal q)⁻¹ + μ univ := by
        gcongr
        rw [zero_add]
        calc ∑' k, ∫⁻ y in A k, rieszKernel a x y ∂μ
            ≤ ∑' k, ENNReal.ofReal (C * 2 ^ a) * ENNReal.ofReal q ^ k :=
              ENNReal.tsum_le_tsum hann
          _ = ENNReal.ofReal (C * 2 ^ a) * ∑' k, ENNReal.ofReal q ^ k := by
              rw [ENNReal.tsum_mul_left]
          _ = ENNReal.ofReal (C * 2 ^ a) * (1 - ENNReal.ofReal q)⁻¹ := by
              rw [ENNReal.tsum_geometric]
    _ = μ univ + ENNReal.ofReal (C * 2 ^ a) * (1 - ENNReal.ofReal q)⁻¹ := add_comm _ _

/-- **Finite energy.**  An `(s, C)`-Frostman finite measure has finite `a`-energy for every
`0 < a < s`. -/
theorem rieszEnergy_ne_top [IsFiniteMeasure μ] (hC : 0 < C) (ha : 0 < a) (has : a < s)
    (hfr : IsFrostman μ s C) : rieszEnergy μ a ≠ ⊤ := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_lintegral_rieszKernel hC ha has hfr
  have hle : rieszEnergy μ a ≤ B * μ univ := by
    refine (lintegral_mono fun x ↦ hbound x).trans ?_
    rw [lintegral_const]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hB (measure_ne_top _ _)) hle

end Bound

section Truncated

/-- The truncated kernel at scales `a ≤ b` of §6.3: `b / a` on the diagonal, and
`min (b / a) (b / |y - z|)` off it.  The diagonal case is explicit, so that Lean's totalized
division at zero never contributes a value. -/
def truncKernel (a b : ℝ) (y z : Plane) : ℝ≥0∞ :=
  if y = z then ENNReal.ofReal (b / a) else ENNReal.ofReal (min (b / a) (b / dist y z))

variable {a b : ℝ} {y z : Plane}

theorem truncKernel_symm (a b : ℝ) (y z : Plane) : truncKernel a b y z = truncKernel a b z y := by
  rw [truncKernel, truncKernel, dist_comm]
  by_cases h : y = z
  · simp [h]
  · simp [h, Ne.symm h]

/-- The truncation makes the kernel bounded by the ratio of the scales. -/
theorem truncKernel_le (a b : ℝ) (y z : Plane) : truncKernel a b y z ≤ ENNReal.ofReal (b / a) := by
  rw [truncKernel]
  by_cases h : y = z
  · simp [h]
  · simp only [h, if_false]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-- Inside the inner scale the kernel is exactly the ratio of the scales. -/
theorem truncKernel_of_dist_le (hb : 0 ≤ b) (ha : 0 < a) (h : dist y z ≤ a) :
    truncKernel a b y z = ENNReal.ofReal (b / a) := by
  rw [truncKernel]
  by_cases hyz : y = z
  · simp [hyz]
  · have hd : 0 < dist y z := dist_pos.2 hyz
    have : b / a ≤ b / dist y z := by
      exact div_le_div_of_nonneg_left hb hd h
    simp [hyz, min_eq_left this]

/-- Outside the inner scale the kernel is the reciprocal distance, scaled by `b`. -/
theorem truncKernel_of_le_dist (hb : 0 ≤ b) (ha : 0 < a) (h : a ≤ dist y z) :
    truncKernel a b y z = ENNReal.ofReal (b / dist y z) := by
  have hd : 0 < dist y z := lt_of_lt_of_le ha h
  have hyz : y ≠ z := fun hyz ↦ by simp [hyz] at hd
  rw [truncKernel, if_neg hyz, min_eq_right (div_le_div_of_nonneg_left hb ha h)]

/-- The truncated energy of §6.3. -/
def truncEnergy (μ : Measure Plane) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ∫⁻ z, truncKernel a b y z ∂μ ∂μ

/-- The finite truncation bounds the energy by `b / a` times the squared mass. -/
theorem truncEnergy_le (μ : Measure Plane) (a b : ℝ) :
    truncEnergy μ a b ≤ ENNReal.ofReal (b / a) * μ univ * μ univ := by
  have hinner : ∀ y : Plane, ∫⁻ z, truncKernel a b y z ∂μ
      ≤ ENNReal.ofReal (b / a) * μ univ := by
    intro y
    refine (lintegral_mono fun z ↦ truncKernel_le a b y z).trans ?_
    rw [lintegral_const]
  calc truncEnergy μ a b
      ≤ ∫⁻ _y, ENNReal.ofReal (b / a) * μ univ ∂μ := lintegral_mono hinner
    _ = ENNReal.ofReal (b / a) * μ univ * μ univ := by
        rw [lintegral_const]

theorem truncEnergy_ne_top (μ : Measure Plane) [IsFiniteMeasure μ] (a b : ℝ) :
    truncEnergy μ a b ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (measure_ne_top _ _))
    (truncEnergy_le μ a b)

end Truncated

end FalconerPacking
