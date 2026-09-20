/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.OccupiedCubes

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

/-- The scale factor from a covering number and the localized energy is geometric in the
generation. -/
theorem covering_local_energy_scale_identity (n : ℕ) (u s a : ℝ) :
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) *
        (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) =
      ((2 : ℝ) ^ u * (2 * Real.sqrt 2) ^ (s - a)) *
        (((2 : ℝ) ^ (u + a - s)) ^ n) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h2p : (0 : ℝ) < 2 := by norm_num
  have hA : 0 ≤ 2 * Real.sqrt 2 := by positivity
  rw [Real.div_rpow hA (by positivity), ← Real.rpow_natCast (2 : ℝ) n,
    ← Real.rpow_mul h2, div_eq_mul_inv,
    ← Real.rpow_natCast ((2 : ℝ) ^ (u + a - s)) n,
    ← Real.rpow_mul h2]
  have hn : (((n + 1 : ℕ) : ℝ) * u) = u + (n : ℝ) * u := by
    push_cast
    ring
  rw [hn, Real.rpow_add h2p]
  rw [show ((2 : ℝ) ^ ((n : ℝ) * (s - a)))⁻¹ =
      (2 : ℝ) ^ (-((n : ℝ) * (s - a))) by
    rw [← Real.rpow_neg h2]]
  rw [show (2 : ℝ) ^ u * (2 : ℝ) ^ ((n : ℝ) * u) *
        ((2 * Real.sqrt 2) ^ (s - a) *
          (2 : ℝ) ^ (-((n : ℝ) * (s - a)))) =
      (2 * Real.sqrt 2) ^ (s - a) * (2 : ℝ) ^ u *
        ((2 : ℝ) ^ ((n : ℝ) * u) *
          (2 : ℝ) ^ (-((n : ℝ) * (s - a)))) by ring,
    show (2 : ℝ) ^ u * (2 * Real.sqrt 2) ^ (s - a) *
        (2 : ℝ) ^ ((u + a - s) * (n : ℝ)) =
      (2 * Real.sqrt 2) ^ (s - a) * (2 : ℝ) ^ u *
        (2 : ℝ) ^ ((u + a - s) * (n : ℝ)) by ring,
    ← Real.rpow_add h2p]
  congr 2
  ring

/-- With `a = 1 + 2γ`, the coherent comparison weight changes the geometric exponent to
`u - s - 2γ`. -/
theorem coherent_local_energy_scale_identity
    (n : ℕ) (u s γ Cbox C : ℝ) :
    (2 : ℝ) ^ (-((n : ℝ) * (1 + 4 * γ))) *
        (4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) *
        (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - (1 + 2 * γ)) *
          2 ^ (1 + 2 * γ)) =
      (4 * Cbox * C * (2 : ℝ) ^ u *
          (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) * 2 ^ (1 + 2 * γ)) *
        (((2 : ℝ) ^ (u - s - 2 * γ)) ^ n) := by
  rw [show (2 : ℝ) ^ (-((n : ℝ) * (1 + 4 * γ))) *
        (4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) *
        (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - (1 + 2 * γ)) *
          2 ^ (1 + 2 * γ)) =
      (2 : ℝ) ^ (-((n : ℝ) * (1 + 4 * γ))) *
        ((4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) *
          (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - (1 + 2 * γ)) *
            2 ^ (1 + 2 * γ))) by ring,
    show (4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) *
        (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - (1 + 2 * γ)) *
          2 ^ (1 + 2 * γ)) =
      (4 * Cbox * C * 2 ^ (1 + 2 * γ)) *
        ((2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) *
          (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - (1 + 2 * γ))) by ring,
    covering_local_energy_scale_identity n u s (1 + 2 * γ)]
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (u + (1 + 2 * γ) - s)) n,
    ← Real.rpow_mul h2.le,
    ← Real.rpow_natCast ((2 : ℝ) ^ (u - s - 2 * γ)) n,
    ← Real.rpow_mul h2.le]
  rw [show (2 : ℝ) ^ (-((n : ℝ) * (1 + 4 * γ))) *
        ((4 * Cbox * C * 2 ^ (1 + 2 * γ)) *
          (2 ^ u * (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) *
            2 ^ ((u + (1 + 2 * γ) - s) * (n : ℝ)))) =
      (4 * Cbox * C * 2 ^ u * (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) *
        2 ^ (1 + 2 * γ)) *
          (2 ^ (-((n : ℝ) * (1 + 4 * γ))) *
            2 ^ ((u + (1 + 2 * γ) - s) * (n : ℝ))) by ring,
    ← Real.rpow_add h2]
  congr 2
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

/-- Removing the zero-mass cubes from a finite cover of a carrier leaves a union of full measure. -/
theorem measure_compl_iUnion_filter_measure_ne_zero_eq_zero
    {μ : Measure (EuclideanSpace ℝ (Fin 2))}
    {K : Set (EuclideanSpace ℝ (Fin 2))} {n : ℕ}
    {S : Finset (Fin 2 → ℤ)}
    (hcover : K ⊆ ⋃ k ∈ S, dyadicCube n k) (hμK : μ Kᶜ = 0) :
    μ (⋃ k ∈ S.filter fun k ↦ μ (dyadicCube n k) ≠ 0, dyadicCube n k)ᶜ = 0 := by
  classical
  let T := S.filter fun k ↦ μ (dyadicCube n k) ≠ 0
  let Z := S.filter fun k ↦ μ (dyadicCube n k) = 0
  have hZ : μ (⋃ k ∈ Z, dyadicCube n k) = 0 := by
    apply nonpos_iff_eq_zero.1
    refine (measure_biUnion_finset_le Z fun k ↦ dyadicCube n k).trans ?_
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k hk
    exact (Finset.mem_filter.1 hk).2
  apply measure_mono_null (t := Kᶜ ∪ ⋃ k ∈ Z, dyadicCube n k) ?_
    (measure_union_null hμK hZ)
  intro x hx
  by_cases hxK : x ∈ K
  · right
    obtain ⟨k, hkS, hxk⟩ := Set.mem_iUnion₂.1 (hcover hxK)
    have hkzero : μ (dyadicCube n k) = 0 := by
      by_contra hkne
      have hkT : k ∈ T := Finset.mem_filter.2 ⟨hkS, hkne⟩
      exact hx (Set.mem_iUnion₂.2 ⟨k, hkT, hxk⟩)
    exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_filter.2 ⟨hkS, hkzero⟩, hxk⟩
  · exact Or.inl hxK

/-- A polynomial covering bound supplies, at every scale, a finite family of positive-mass
conditioning cubes whose weighted conditional energy has the expected covering-number bound. -/
theorem exists_conditioningCubeIndices_energy_bound
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u s C a : ℝ}
    (hbox : HasUpperBoxBound K u) (hμK : μ Kᶜ = 0)
    (hC : 0 < C) (ha : 0 < a) (has : a < s) (hfr : IsFrostman μ s C) :
    ∃ Cbox : ℝ, 0 < Cbox ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ S : Finset (Fin 2 → ℤ),
        μ (⋃ k ∈ S, dyadicCube n k)ᶜ = 0 ∧
        (∀ k ∈ S, 0 < μ (dyadicCube n k)) ∧
        ∑ k ∈ S, μ (dyadicCube n k) *
            rieszEnergy (normalizedRestrict μ (dyadicCube n k)) a ≤
          ENNReal.ofReal
              (4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) *
            (ENNReal.ofReal
                (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) * 2 ^ a) *
              (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹) := by
  obtain ⟨Cbox, hCbox, hcover⟩ :=
    exists_occupiedCubeIndices_card_le_of_hasUpperBoxBound hbox
  refine ⟨Cbox, hCbox, fun n hn ↦ ?_⟩
  obtain ⟨S₀, hKcover, hS₀card⟩ := hcover n
  let S := S₀.filter fun k ↦ μ (dyadicCube n k) ≠ 0
  have hpos : ∀ k ∈ S, 0 < μ (dyadicCube n k) := by
    intro k hk
    exact pos_iff_ne_zero.2 (Finset.mem_filter.1 hk).2
  refine ⟨S, measure_compl_iUnion_filter_measure_ne_zero_eq_zero hKcover hμK, hpos, ?_⟩
  let B : ℝ≥0∞ :=
    ENNReal.ofReal
        (C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^ (s - a) * 2 ^ a) *
      (1 - ENNReal.ofReal ((2 : ℝ) ^ (a - s)))⁻¹
  have henergy := sum_measure_mul_rieszEnergy_normalizedRestrict_dyadicCube_le
    hC ha has hfr hn S hpos
  have hScardReal : (S.card : ℝ) ≤
      4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) := by
    calc
      (S.card : ℝ) ≤ (S₀.card : ℝ) := by
        exact_mod_cast Finset.card_filter_le S₀ (fun k ↦ μ (dyadicCube n k) ≠ 0)
      _ ≤ 4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u) := hS₀card
  have hScard : (S.card : ℝ≥0∞) ≤
      ENNReal.ofReal (4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hScardReal
  exact henergy.trans (by
    change (S.card : ℝ≥0∞) * B ≤
      ENNReal.ofReal (4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)) * B
    gcongr)

/-- The scale-normalized conditional energy that appears in the coherent comparison argument. -/
def coherentConditionalEnergy
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    (S : Finset (Fin 2 → ℤ)) (n : ℕ) (γ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (-((n : ℝ) * (1 + 4 * γ)))) *
    ∑ k ∈ S, μ (dyadicCube n k) *
      rieszEnergy (normalizedRestrict μ (dyadicCube n k)) (1 + 2 * γ)

/-- The covering-number hypothesis gives the exact geometric bound required by the coherent
criterion.  The ratio is `2 ^ (u - s - 2γ)`. -/
theorem exists_coherentConditionalEnergy_geometric_bound
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u s C γ : ℝ}
    (hbox : HasUpperBoxBound K u) (hμK : μ Kᶜ = 0)
    (hC : 0 < C) (hγ : 0 < γ) (hγs : 1 + 2 * γ < s)
    (hfr : IsFrostman μ s C) :
    ∃ Cbox : ℝ, 0 < Cbox ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ S : Finset (Fin 2 → ℤ),
        μ (⋃ k ∈ S, dyadicCube n k)ᶜ = 0 ∧
        (∀ k ∈ S, 0 < μ (dyadicCube n k)) ∧
        coherentConditionalEnergy μ S n γ ≤
          ENNReal.ofReal
              (4 * Cbox * C * (2 : ℝ) ^ u *
                (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) * 2 ^ (1 + 2 * γ)) *
            (1 - ENNReal.ofReal ((2 : ℝ) ^ ((1 + 2 * γ) - s)))⁻¹ *
            ENNReal.ofReal ((((2 : ℝ) ^ (u - s - 2 * γ)) ^ n)) := by
  obtain ⟨Cbox, hCbox, hbound⟩ :=
    exists_conditioningCubeIndices_energy_bound hbox hμK hC
      (by linarith) hγs hfr
  refine ⟨Cbox, hCbox, fun n hn ↦ ?_⟩
  obtain ⟨S, hSfull, hSpos, hSenergy⟩ := hbound n hn
  refine ⟨S, hSfull, hSpos, ?_⟩
  let scale : ℝ := (2 : ℝ) ^ (-((n : ℝ) * (1 + 4 * γ)))
  let M : ℝ := 4 * Cbox * (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) * u)
  let N : ℝ := C * (2 * Real.sqrt 2 / (2 : ℝ) ^ n) ^
    (s - (1 + 2 * γ)) * 2 ^ (1 + 2 * γ)
  let G : ℝ≥0∞ := (1 - ENNReal.ofReal ((2 : ℝ) ^ ((1 + 2 * γ) - s)))⁻¹
  let D : ℝ := 4 * Cbox * C * (2 : ℝ) ^ u *
    (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) * 2 ^ (1 + 2 * γ)
  let q : ℝ := (2 : ℝ) ^ (u - s - 2 * γ)
  change ENNReal.ofReal scale *
      (∑ k ∈ S, μ (dyadicCube n k) *
        rieszEnergy (normalizedRestrict μ (dyadicCube n k)) (1 + 2 * γ)) ≤
    ENNReal.ofReal D * G * ENNReal.ofReal (q ^ n)
  calc
    ENNReal.ofReal scale *
        (∑ k ∈ S, μ (dyadicCube n k) *
          rieszEnergy (normalizedRestrict μ (dyadicCube n k)) (1 + 2 * γ))
        ≤ ENNReal.ofReal scale * (ENNReal.ofReal M * (ENNReal.ofReal N * G)) := by
          gcongr
    _ = (ENNReal.ofReal scale * ENNReal.ofReal M * ENNReal.ofReal N) * G := by ring
    _ = ENNReal.ofReal (scale * M * N) * G := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ scale),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ scale * M)]
    _ = ENNReal.ofReal (D * q ^ n) * G := by
          congr 2
          exact coherent_local_energy_scale_identity n u s γ Cbox C
    _ = (ENNReal.ofReal D * ENNReal.ofReal (q ^ n)) * G := by
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ D)]
    _ = ENNReal.ofReal D * G * ENNReal.ofReal (q ^ n) := by ring

/-- A positive power of a real geometric sequence remains summable in `ℝ≥0∞` when the ratio is
strictly between zero and one. -/
theorem tsum_ofReal_pow_rpow_ne_top {q η : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hη : 0 < η) :
    (∑' n : ℕ, ENNReal.ofReal (q ^ n) ^ η) ≠ ∞ := by
  have hqE : ENNReal.ofReal q < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hq1
  have hr : ENNReal.ofReal q ^ η < 1 := ENNReal.rpow_lt_one hqE hη
  rw [show (fun n : ℕ ↦ ENNReal.ofReal (q ^ n) ^ η) =
      fun n : ℕ ↦ (ENNReal.ofReal q ^ η) ^ n by
    funext n
    rw [ENNReal.ofReal_pow hq0.le, ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul, mul_comm, ENNReal.rpow_mul, ENNReal.rpow_natCast],
    ENNReal.tsum_geometric]
  exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'

/-- Any sequence bounded by a finite multiple of a decaying real geometric sequence satisfies
the powered summability condition used by the coherent criterion. -/
theorem tsum_rpow_ne_top_of_le_geometric
    {Z : ℕ → ℝ≥0∞} {K : ℝ≥0∞} {q η : ℝ}
    (hK : K ≠ ∞) (hq0 : 0 < q) (hq1 : q < 1) (hη : 0 < η)
    (hZ : ∀ n, Z n ≤ K * ENNReal.ofReal (q ^ n)) :
    (∑' n, Z n ^ η) ≠ ∞ := by
  have hgeom := tsum_ofReal_pow_rpow_ne_top hq0 hq1 hη
  have hle : (∑' n, Z n ^ η) ≤
      K ^ η * ∑' n : ℕ, ENNReal.ofReal (q ^ n) ^ η := by
    calc
      (∑' n, Z n ^ η) ≤ ∑' n, (K * ENNReal.ofReal (q ^ n)) ^ η :=
        ENNReal.tsum_le_tsum fun n ↦ ENNReal.rpow_le_rpow (hZ n) hη.le
      _ = ∑' n, K ^ η * ENNReal.ofReal (q ^ n) ^ η := by
        congr 1
        funext n
        rw [ENNReal.mul_rpow_of_nonneg _ _ hη.le]
      _ = K ^ η * ∑' n, ENNReal.ofReal (q ^ n) ^ η := ENNReal.tsum_mul_left
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hη.le hK) hgeom) hle

/-- The strict covering inequality `u < 2s - 1` leaves room for an angular exponent `γ` with all
four inequalities needed by the coherent comparison. -/
theorem exists_coherent_gamma {s u : ℝ} (hs : 1 < s) (hs2 : s < 2)
    (hu : u < 2 * s - 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ < 1 / 2 ∧ 1 + 2 * γ < s ∧ u < s + 2 * γ := by
  have hupper0 : 0 < (s - 1) / 2 := by linarith
  have hlower : (u - s) / 2 < (s - 1) / 2 := by linarith
  have hmax : max 0 ((u - s) / 2) < (s - 1) / 2 :=
    max_lt hupper0 hlower
  obtain ⟨γ, hγlow, hγhigh⟩ := exists_between hmax
  refine ⟨γ, lt_of_le_of_lt (le_max_left _ _) hγlow, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · have := lt_of_le_of_lt (le_max_right 0 ((u - s) / 2)) hγlow
    linarith

/-- Under `u < s + 2γ`, one can choose full-measure conditioning families at every sufficiently
fine scale whose coherent conditional energies satisfy the powered summability hypothesis. -/
theorem exists_conditioningCubeIndices_coherentEnergy_tsum_ne_top
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u s C γ η : ℝ}
    (hbox : HasUpperBoxBound K u) (hμK : μ Kᶜ = 0)
    (hC : 0 < C) (hγ : 0 < γ) (hγs : 1 + 2 * γ < s)
    (hu : u < s + 2 * γ) (hη : 0 < η)
    (hfr : IsFrostman μ s C) :
    ∃ S : ℕ → Finset (Fin 2 → ℤ),
      (∀ n, μ (⋃ k ∈ S n, dyadicCube (n + 2) k)ᶜ = 0) ∧
      (∀ n k, k ∈ S n → 0 < μ (dyadicCube (n + 2) k)) ∧
      (∑' n, coherentConditionalEnergy μ (S n) (n + 2) γ ^ η) ≠ ∞ := by
  obtain ⟨Cbox, hCbox, hbound⟩ :=
    exists_coherentConditionalEnergy_geometric_bound hbox hμK hC hγ hγs hfr
  have hex : ∀ n : ℕ, ∃ S : Finset (Fin 2 → ℤ),
      μ (⋃ k ∈ S, dyadicCube (n + 2) k)ᶜ = 0 ∧
      (∀ k ∈ S, 0 < μ (dyadicCube (n + 2) k)) ∧
      coherentConditionalEnergy μ S (n + 2) γ ≤
        ENNReal.ofReal
            (4 * Cbox * C * (2 : ℝ) ^ u *
              (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) * 2 ^ (1 + 2 * γ)) *
          (1 - ENNReal.ofReal ((2 : ℝ) ^ ((1 + 2 * γ) - s)))⁻¹ *
          ENNReal.ofReal ((((2 : ℝ) ^ (u - s - 2 * γ)) ^ (n + 2))) := by
    intro n
    exact hbound (n + 2) (by omega)
  choose S hSfull hSpos hSenergy using hex
  refine ⟨S, hSfull, fun n k hk ↦ hSpos n k hk, ?_⟩
  let q : ℝ := (2 : ℝ) ^ (u - s - 2 * γ)
  let D : ℝ := 4 * Cbox * C * (2 : ℝ) ^ u *
    (2 * Real.sqrt 2) ^ (s - (1 + 2 * γ)) * 2 ^ (1 + 2 * γ)
  let G : ℝ≥0∞ := (1 - ENNReal.ofReal ((2 : ℝ) ^ ((1 + 2 * γ) - s)))⁻¹
  let Kconst : ℝ≥0∞ := ENNReal.ofReal D * G
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    change (2 : ℝ) ^ (u - s - 2 * γ) < 1
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hratio : ENNReal.ofReal ((2 : ℝ) ^ ((1 + 2 * γ) - s)) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hG : G ≠ ∞ := by
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hratio).ne'
  have hKconst : Kconst ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  apply tsum_rpow_ne_top_of_le_geometric hKconst hq0 hq1 hη
  intro n
  have henergy : coherentConditionalEnergy μ (S n) (n + 2) γ ≤
      Kconst * ENNReal.ofReal (q ^ (n + 2)) := by
    simpa only [Kconst, D, G, q] using hSenergy n
  refine henergy.trans ?_
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_of_le_one hq0.le hq1.le (by omega)

/-- The packing-dimension inequality `u < 2s - 1` supplies a coherent comparison parameter
and full-measure conditioning families whose powered coherent energies are summable. -/
theorem exists_gamma_conditioningCubeIndices_coherentEnergy_tsum_ne_top
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ]
    {K : Set (EuclideanSpace ℝ (Fin 2))} {u s C η : ℝ}
    (hbox : HasUpperBoxBound K u) (hμK : μ Kᶜ = 0)
    (hC : 0 < C) (hs : 1 < s) (hs2 : s < 2)
    (hu : u < 2 * s - 1) (hη : 0 < η)
    (hfr : IsFrostman μ s C) :
    ∃ (γ : ℝ) (S : ℕ → Finset (Fin 2 → ℤ)),
      0 < γ ∧ γ < 1 / 2 ∧ 1 + 2 * γ < s ∧
      (∀ n, μ (⋃ k ∈ S n, dyadicCube (n + 2) k)ᶜ = 0) ∧
      (∀ n k, k ∈ S n → 0 < μ (dyadicCube (n + 2) k)) ∧
      (∑' n, coherentConditionalEnergy μ (S n) (n + 2) γ ^ η) ≠ ∞ := by
  obtain ⟨γ, hγ0, hγhalf, hγs, hγu⟩ := exists_coherent_gamma hs hs2 hu
  obtain ⟨S, hSfull, hSpos, hSsum⟩ :=
    exists_conditioningCubeIndices_coherentEnergy_tsum_ne_top
      hbox hμK hC hγ0 hγs hγu hη hfr
  exact ⟨γ, S, hγ0, hγhalf, hγs, hSfull, hSpos, hSsum⟩

end FalconerPacking
