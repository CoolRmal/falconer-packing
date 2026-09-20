/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.Restriction

/-!
# Localized Frostman energy estimates

The global energy estimate does not record the diameter of the source.  The coherent-tree
argument needs the sharper local statement: inside a ball of radius `R`, the `a`-potential of an
`s`-Frostman measure is `O(R ^ (s - a))`.  This file proves that estimate by annular summation and
then applies it to normalized restrictions to dyadic cubes.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- The closed form for the Frostman kernel estimate after all dyadic radii are scaled by `R`. -/
theorem scaledDyadicRadius_kernel_const (C R a s : ℝ) (k : ℕ) (hR : 0 < R) :
    (R * dyadicRadius (k + 1)) ^ (-a) * (C * (R * dyadicRadius k) ^ s)
      = C * R ^ (s - a) * 2 ^ a * ((2 : ℝ) ^ (a - s)) ^ k := by
  rw [Real.mul_rpow hR.le (dyadicRadius_pos (k + 1)).le,
    Real.mul_rpow hR.le (dyadicRadius_pos k).le]
  have hRpow : R ^ (-a) * R ^ s = R ^ (s - a) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  rw [show R ^ (-a) * dyadicRadius (k + 1) ^ (-a) *
      (C * (R ^ s * dyadicRadius k ^ s)) =
      (R ^ (-a) * R ^ s) *
        (dyadicRadius (k + 1) ^ (-a) * (C * dyadicRadius k ^ s)) by ring,
    hRpow, dyadicRadius_kernel_const]
  ring

/-- The local `a`-potential of an `s`-Frostman measure inside a ball of radius `R` is bounded by
a constant times `R ^ (s - a)`. -/
theorem setLIntegral_rieszKernel_le_of_subset_ball
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C a R : ℝ}
    (hC : 0 < C) (ha : 0 < a) (has : a < s) (hfr : IsFrostman μ s C)
    (hR : 0 < R) (hR1 : R ≤ 1)
    {Q : Set (EuclideanSpace ℝ (Fin 2))} {x : EuclideanSpace ℝ (Fin 2)}
    (hQ : Q ⊆ Metric.ball x R) :
    ∫⁻ y in Q, rieszKernel a x y ∂μ ≤
      ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹ := by
  have hs : 0 < s := ha.trans has
  set q : ℝ := (2 : ℝ) ^ (a - s) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqlt : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq1
  set A : ℕ → Set (EuclideanSpace ℝ (Fin 2)) := fun k ↦
    Metric.ball x (R * dyadicRadius k) \ Metric.ball x (R * dyadicRadius (k + 1)) with hA
  have hAmeas : ∀ k, MeasurableSet (A k) :=
    fun k ↦ Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hcover : Metric.ball x R ⊆ {x} ∪ ⋃ k, A k := by
    intro y hy
    rcases eq_or_lt_of_le (dist_nonneg (x := y) (y := x)) with hzero | hpos
    · exact Or.inl (by simp [dist_eq_zero.1 hzero.symm])
    have htend : Tendsto (fun k ↦ R * dyadicRadius k) atTop (𝓝 0) := by
      have ht := tendsto_dyadicRadius.const_mul R
      rwa [mul_zero] at ht
    have hex : ∃ k : ℕ, R * dyadicRadius k ≤ dist y x := by
      obtain ⟨k, hk⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
      exact ⟨k, hk.le⟩
    have hspec : R * dyadicRadius (Nat.find hex) ≤ dist y x := Nat.find_spec hex
    have hfindpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero' | hpos'
      · rw [hzero', dyadicRadius_zero, mul_one] at hspec
        exact absurd hspec (not_le.2 (by simpa [dist_comm] using hy))
      · exact hpos'
    have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    have hmin : ¬R * dyadicRadius (Nat.find hex - 1) ≤ dist y x :=
      Nat.find_min hex (by omega)
    refine Or.inr (mem_iUnion.2 ⟨Nat.find hex - 1, ?_⟩)
    refine ⟨?_, ?_⟩
    · exact Metric.mem_ball.2 (not_le.1 hmin)
    · rw [hsucc]
      exact fun hmem ↦ absurd (Metric.mem_ball.1 hmem) (not_lt.2 (by simpa [dist_comm] using hspec))
  have hx0 : μ {x} = 0 := measure_singleton_eq_zero_of_isFrostman hs hfr x
  have hann : ∀ k, ∫⁻ y in A k, rieszKernel a x y ∂μ
      ≤ ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) * ENNReal.ofReal q ^ k := by
    intro k
    have hrpos : 0 < R * dyadicRadius k := mul_pos hR (dyadicRadius_pos k)
    have hrle : R * dyadicRadius k ≤ 1 := by
      calc
        R * dyadicRadius k ≤ 1 * 1 :=
          mul_le_mul hR1 (dyadicRadius_le_one k) (dyadicRadius_pos k).le (by norm_num)
        _ = 1 := mul_one 1
    calc
      ∫⁻ y in A k, rieszKernel a x y ∂μ
          ≤ ∫⁻ _y in A k,
              ENNReal.ofReal (R * dyadicRadius (k + 1)) ^ (-a) ∂μ := by
            refine lintegral_mono_ae ((ae_restrict_iff' (hAmeas k)).2
              (Eventually.of_forall ?_))
            intro y hy
            refine rieszKernel_le_of_le ha.le ?_
            rw [dist_comm]
            exact not_lt.1 fun hlt ↦ hy.2 (Metric.mem_ball.2 hlt)
      _ = ENNReal.ofReal (R * dyadicRadius (k + 1)) ^ (-a) * μ (A k) := by
            rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (R * dyadicRadius (k + 1)) ^ (-a) *
            ENNReal.ofReal (C * (R * dyadicRadius k) ^ s) := by
            gcongr
            exact (measure_mono sdiff_subset).trans (hfr x _ hrpos hrle)
      _ = ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) * ENNReal.ofReal q ^ k := by
            rw [ENNReal.ofReal_rpow_of_pos (mul_pos hR (dyadicRadius_pos (k + 1))),
              ← ENNReal.ofReal_mul
                (Real.rpow_nonneg (mul_pos hR (dyadicRadius_pos (k + 1))).le _),
              ← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_mul (by positivity), hqdef,
              scaledDyadicRadius_kernel_const C R a s k hR]
  calc
    ∫⁻ y in Q, rieszKernel a x y ∂μ
        ≤ ∫⁻ y in Metric.ball x R, rieszKernel a x y ∂μ := lintegral_mono_set hQ
    _ ≤ ∫⁻ y in {x} ∪ ⋃ k, A k, rieszKernel a x y ∂μ := lintegral_mono_set hcover
    _ ≤ (∫⁻ y in {x}, rieszKernel a x y ∂μ) +
          ∫⁻ y in ⋃ k, A k, rieszKernel a x y ∂μ := lintegral_union_le _ _ _
    _ ≤ (0 : ℝ≥0∞) + ∑' k, ∫⁻ y in A k, rieszKernel a x y ∂μ := by
          gcongr
          · exact le_of_eq (setLIntegral_measure_zero _ _ hx0)
          · exact lintegral_iUnion_le _ _
    _ ≤ ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
          (1 - ENNReal.ofReal q)⁻¹ := by
          rw [zero_add]
          calc
            ∑' k, ∫⁻ y in A k, rieszKernel a x y ∂μ
                ≤ ∑' k, ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
                    ENNReal.ofReal q ^ k := ENNReal.tsum_le_tsum hann
            _ = ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
                  ∑' k, ENNReal.ofReal q ^ k := by rw [ENNReal.tsum_mul_left]
            _ = ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
                  (1 - ENNReal.ofReal q)⁻¹ := by rw [ENNReal.tsum_geometric]
    _ = ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹ := by rw [hqdef]

/-- Integrating the local potential estimate over the source set gives the corresponding raw
double-energy bound. -/
theorem setLIntegral_setLIntegral_rieszKernel_le
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C a R : ℝ}
    (hC : 0 < C) (ha : 0 < a) (has : a < s) (hfr : IsFrostman μ s C)
    (hR : 0 < R) (hR1 : R ≤ 1)
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQmeas : MeasurableSet Q)
    (hQ : ∀ x ∈ Q, Q ⊆ Metric.ball x R) :
    ∫⁻ x in Q, ∫⁻ y in Q, rieszKernel a x y ∂μ ∂μ ≤
      (ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * μ Q := by
  calc
    ∫⁻ x in Q, ∫⁻ y in Q, rieszKernel a x y ∂μ ∂μ
        ≤ ∫⁻ _x in Q,
            ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
              (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹ ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hQmeas).2
            (Eventually.of_forall ?_))
          intro x hx
          exact setLIntegral_rieszKernel_le_of_subset_ball hC ha has hfr hR hR1 (hQ x hx)
    _ = (ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * μ Q := by
          rw [setLIntegral_const]

/-- Normalizing a restriction multiplies its raw double energy by the inverse square of its
mass. -/
theorem rieszEnergy_normalizedRestrict_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (a : ℝ) (hQ0 : μ Q ≠ 0) :
    rieszEnergy (normalizedRestrict μ Q) a =
      (μ Q)⁻¹ * (μ Q)⁻¹ *
        ∫⁻ x in Q, ∫⁻ y in Q, rieszKernel a x y ∂μ ∂μ := by
  have hinvtop : (μ Q)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hQ0
  rw [rieszEnergy, normalizedRestrict]
  simp_rw [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' (μ Q)⁻¹ _ hinvtop]
  ring

/-- The normalized local energy is bounded by the local potential constant divided by the mass
of the conditioning set. -/
theorem rieszEnergy_normalizedRestrict_le
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C a R : ℝ}
    (hC : 0 < C) (ha : 0 < a) (has : a < s) (hfr : IsFrostman μ s C)
    (hR : 0 < R) (hR1 : R ≤ 1)
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQmeas : MeasurableSet Q)
    (hQ0 : μ Q ≠ 0) (hQtop : μ Q ≠ ∞)
    (hQ : ∀ x ∈ Q, Q ⊆ Metric.ball x R) :
    rieszEnergy (normalizedRestrict μ Q) a ≤
      (ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * (μ Q)⁻¹ := by
  rw [rieszEnergy_normalizedRestrict_eq μ a hQ0]
  calc
    (μ Q)⁻¹ * (μ Q)⁻¹ *
        ∫⁻ x in Q, ∫⁻ y in Q, rieszKernel a x y ∂μ ∂μ
        ≤ (μ Q)⁻¹ * (μ Q)⁻¹ *
          ((ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
            (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * μ Q) := by
          gcongr
          exact setLIntegral_setLIntegral_rieszKernel_le
            hC ha has hfr hR hR1 hQmeas hQ
    _ = (ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * (μ Q)⁻¹ := by
          rw [show (μ Q)⁻¹ * (μ Q)⁻¹ *
              ((ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
                (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * μ Q) =
              (ENNReal.ofReal (C * R ^ (s - a) * 2 ^ a) *
                (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) * (μ Q)⁻¹ *
                  ((μ Q)⁻¹ * μ Q) by ac_rfl,
            ENNReal.inv_mul_cancel hQ0 hQtop, mul_one]

/-- A dyadic cube lies in a ball centered at any of its points with twice the elementary
diameter bound as radius. -/
theorem dyadicCube_subset_ball {n : ℕ} {k : Fin 2 → ℤ}
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ dyadicCube n k) :
    dyadicCube n k ⊆ Metric.ball x (2 * Real.sqrt 2 / (2 : ℝ) ^ n) := by
  intro y hy
  apply Metric.mem_ball.2
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hdiam := dist_le_of_mem_dyadicCube hx hy
  rw [dist_comm]
  exact hdiam.trans_lt (by
    rw [div_lt_div_iff_of_pos_right hpow]
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith)

/-- The enlarged dyadic-cube radius used by the local energy estimate is at most one from
generation two onward. -/
theorem two_mul_sqrt_two_div_pow_le_one {n : ℕ} (hn : 2 ≤ n) :
    2 * Real.sqrt 2 / (2 : ℝ) ^ n ≤ 1 := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hsqrt2 : Real.sqrt 2 < 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hfour : (4 : ℝ) ≤ 2 ^ n := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  rw [div_le_one hpow]
  linarith

/-- The local energy estimate specialized to a positive-mass dyadic cube. -/
theorem rieszEnergy_normalizedRestrict_dyadicCube_le
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {s C a : ℝ} (hC : 0 < C) (ha : 0 < a) (has : a < s)
    (hfr : IsFrostman μ s C) {n : ℕ} (hn : 2 ≤ n) (k : Fin 2 → ℤ)
    (hQ0 : μ (dyadicCube n k) ≠ 0) :
    rieszEnergy (normalizedRestrict μ (dyadicCube n k)) a ≤
      (ENNReal.ofReal
          (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) * 2 ^ a) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) *
          (μ (dyadicCube n k))⁻¹ := by
  apply rieszEnergy_normalizedRestrict_le hC ha has hfr
    (by positivity) (two_mul_sqrt_two_div_pow_le_one hn)
    (measurableSet_dyadicCube n k) hQ0 (measure_ne_top μ _)
  exact fun x hx ↦ dyadicCube_subset_ball hx

/-- Summing the normalized conditional energies over finitely many occupied cubes costs only the
number of cubes.  The factors `μ(Q)` cancel the normalization losses. -/
theorem sum_measure_mul_rieszEnergy_normalizedRestrict_dyadicCube_le
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {s C a : ℝ} (hC : 0 < C) (ha : 0 < a) (has : a < s)
    (hfr : IsFrostman μ s C) {n : ℕ} (hn : 2 ≤ n)
    (S : Finset (Fin 2 → ℤ))
    (hpos : ∀ k ∈ S, 0 < μ (dyadicCube n k)) :
    ∑ k ∈ S, μ (dyadicCube n k) *
        rieszEnergy (normalizedRestrict μ (dyadicCube n k)) a ≤
      (S.card : ℝ≥0∞) *
        (ENNReal.ofReal
            (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) * 2 ^ a) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) := by
  let B : ℝ≥0∞ :=
    ENNReal.ofReal
        (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) * 2 ^ a) *
      (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹
  calc
    ∑ k ∈ S, μ (dyadicCube n k) *
        rieszEnergy (normalizedRestrict μ (dyadicCube n k)) a
        ≤ ∑ _k ∈ S, B := by
          apply Finset.sum_le_sum
          intro k hk
          have h0 : μ (dyadicCube n k) ≠ 0 := ne_of_gt (hpos k hk)
          calc
            μ (dyadicCube n k) *
                rieszEnergy (normalizedRestrict μ (dyadicCube n k)) a
                ≤ μ (dyadicCube n k) * (B * (μ (dyadicCube n k))⁻¹) := by
                  gcongr
                  exact rieszEnergy_normalizedRestrict_dyadicCube_le
                    hC ha has hfr hn k h0
            _ = B := by
                  rw [show μ (dyadicCube n k) * (B * (μ (dyadicCube n k))⁻¹) =
                      B * (μ (dyadicCube n k) * (μ (dyadicCube n k))⁻¹) by ac_rfl,
                    ENNReal.mul_inv_cancel h0 (measure_ne_top μ _), mul_one]
    _ = (S.card : ℝ≥0∞) * B := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ≥0∞) *
        (ENNReal.ofReal
            (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) * 2 ^ a) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) := rfl

end FalconerPacking
