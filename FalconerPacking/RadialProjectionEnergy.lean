/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.Energy
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Energy exponents and angular singularities for radial projections

The strict inequalities below are the two independent integrability requirements in
Orponen's averaged radial-projection argument. The angular estimate uses the integrable
singularity of `|sin θ| ^ (-β)` for `β < 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Explicit exponents satisfying both strict inequalities in the radial trace argument. -/
theorem radialProjection_exponents {s : ℝ} (hs : 1 < s) (hs₂ : s < 2) :
    let t := (3 - s) / 2
    let p := 1 + (s - 1) / 8
    0 < t ∧ t < 1 ∧ 1 < p ∧ p < 2 ∧ p * (2 - s) < t ∧ t < 2 - p := by
  dsimp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith [sq_nonneg (s - 1)]
  · linarith

/-- Frostman exponents greater than one supply all energy exponents needed for radial projection. -/
theorem exists_radialProjection_energy_exponents
    {μ ν : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {α β Cμ Cν : ℝ} (hα : 1 < α) (hβ : 1 < β) (hCμ : 0 < Cμ) (hCν : 0 < Cν)
    (hμ : IsFrostman μ α Cμ) (hν : IsFrostman ν β Cν) :
    ∃ s t p : ℝ, 1 < s ∧ s < 2 ∧ 0 < t ∧ t < 1 ∧ 1 < p ∧ p < 2 ∧
      p * (2 - s) < t ∧ t < 2 - p ∧ rieszEnergy μ s ≠ ⊤ ∧ rieszEnergy ν t ≠ ⊤ := by
  obtain ⟨s, hs, hs'⟩ := exists_between (lt_min hα (by norm_num : (1 : ℝ) < 2))
  have hsα := hs'.trans_le (min_le_left α 2)
  have hs₂ := hs'.trans_le (min_le_right α 2)
  obtain ⟨ht₀, ht₁, hp₁, hp₂, hpt, htp⟩ := radialProjection_exponents hs hs₂
  refine ⟨s, (3 - s) / 2, 1 + (s - 1) / 8, hs, hs₂, ht₀, ht₁, hp₁, hp₂,
    hpt, htp, ?_, ?_⟩
  · exact rieszEnergy_ne_top hCμ (by linarith) hsα hμ
  · exact rieszEnergy_ne_top hCν ht₀ (ht₁.trans hβ) hν

/-- The real-valued negative sine power is integrable over a central half-turn. -/
theorem integrableOn_abs_sin_neg_rpow {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    IntegrableOn (fun θ : ℝ ↦ |Real.sin θ| ^ (-β))
      (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hmeas : AEStronglyMeasurable (fun θ : ℝ ↦ |Real.sin θ| ^ (-β)) volume := by
    exact (by fun_prop : Measurable (fun θ : ℝ ↦ |Real.sin θ| ^ (-β))).aestronglyMeasurable
  have hbound : ∀ θ ∈ Metric.ball (0 : ℝ) (Real.pi / 2),
      ‖|Real.sin θ| ^ (-β)‖ ≤ (2 / Real.pi) ^ (-β) * ‖θ‖ ^ (-β) := by
    intro θ hθ
    by_cases hzero : θ = 0
    · simp [hzero, Real.zero_rpow (neg_ne_zero.mpr hβ₀.ne')]
    have hθabs : |θ| < Real.pi / 2 := by simpa [Real.dist_eq] using hθ
    have hlow := Real.mul_abs_le_abs_sin hθabs.le
    have hpos : 0 < 2 / Real.pi * |θ| := mul_pos (by positivity) (abs_pos.mpr hzero)
    have hpow := Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith : -β ≤ 0)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      Real.mul_rpow (by positivity : 0 ≤ 2 / Real.pi) (abs_nonneg θ)] using hpow
  have h := integrableOn_ball_of_norm_le_rpow (E := ℝ) (μ := volume)
    (α := β) (C := (2 / Real.pi) ^ (-β)) (r := Real.pi / 2)
    (by simp) (by simpa using hβ₁)
    ((ae_restrict_mem Metric.isOpen_ball.measurableSet).mono hbound)
    hmeas
  simpa only [Metric.ball, Real.dist_eq, sub_zero, abs_lt, Ioo] using h

/-- Sine singularities remain integrable on every bounded interval. -/
theorem intervalIntegrable_abs_sin_neg_rpow {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (a b : ℝ) : IntervalIntegrable (fun θ : ℝ ↦ |Real.sin θ| ^ (-β)) volume a b := by
  have hper : Function.Periodic (fun θ : ℝ ↦ |Real.sin θ| ^ (-β)) Real.pi := by
    intro θ
    simp [Real.sin_add_pi]
  have hbase : IntervalIntegrable (fun θ : ℝ ↦ |Real.sin θ| ^ (-β)) volume
      (-(Real.pi / 2)) (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith [Real.pi_pos])).mpr
      (integrableOn_abs_sin_neg_rpow hβ₀ hβ₁)
  apply hper.intervalIntegrable Real.pi_ne_zero (t := -(Real.pi / 2)) ?_ a b
  convert hbase using 1
  ring

/-- The exceptional angles where a shifted sine vanishes form a null set. -/
theorem ae_sin_sub_ne_zero (φ : ℝ) : ∀ᵐ θ : ℝ, Real.sin (θ - φ) ≠ 0 := by
  rw [ae_iff]
  have hsub : {θ : ℝ | ¬Real.sin (θ - φ) ≠ 0} ⊆
      Set.range (fun n : ℤ ↦ n * Real.pi + φ) := by
    intro θ hθ
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp (not_ne_iff.mp hθ)
    exact ⟨n, by linarith⟩
  exact measure_mono_null hsub (Set.countable_range _ |>.measure_zero volume)

/-- The angular singularity has a finite integral, uniformly in its direction. -/
theorem lintegral_abs_sin_sub_neg_rpow {β : ℝ} (hβ₀ : 0 < β) (hβ₁ : β < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : ℝ,
      (∫⁻ θ in Ioc (-Real.pi) Real.pi,
        ENNReal.ofReal |Real.sin (θ - φ)| ^ (-β)) = C := by
  let f : ℝ → ℝ := fun θ ↦ |Real.sin θ| ^ (-β)
  let C := ENNReal.ofReal (∫ θ in (-Real.pi)..Real.pi, f θ)
  refine ⟨C, ENNReal.ofReal_ne_top, fun φ ↦ ?_⟩
  have hint : IntervalIntegrable f volume (-Real.pi - φ) (Real.pi - φ) :=
    intervalIntegrable_abs_sin_neg_rpow hβ₀ hβ₁ _ _
  have hshift : IntervalIntegrable (fun θ ↦ f (θ - φ)) volume (-Real.pi) Real.pi := by
    convert hint.comp_sub_right φ using 1 <;> simp
  have hset : IntegrableOn (fun θ ↦ f (θ - φ)) (Ioc (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])).mp hshift
  have heq : (∫⁻ θ in Ioc (-Real.pi) Real.pi,
      ENNReal.ofReal |Real.sin (θ - φ)| ^ (-β)) =
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, ENNReal.ofReal (f (θ - φ)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae (ae_sin_sub_ne_zero φ)] with θ hθ
    exact ENNReal.ofReal_rpow_of_pos (abs_pos.mpr hθ)
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal hset]
  · congr 1
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      intervalIntegral.integral_comp_sub_right]
    have hper : Function.Periodic f (2 * Real.pi) := by
      intro θ
      simp [f, Real.sin_add_two_pi]
    convert hper.intervalIntegral_add_eq (-Real.pi - φ) (-Real.pi) using 1 <;> ring_nf
  · exact Filter.Eventually.of_forall fun θ ↦ Real.rpow_nonneg (abs_nonneg _) _

/-- Hölder gives the weighted angular estimate in Orponen's argument directly.
The constant is independent of the direction and of the normalized angular weight. -/
theorem exists_uniform_weighted_sin_riesz_bound {p t : ℝ}
    (hp₁ : 1 < p) (hp₂ : p < 2) (ht₀ : 0 < t) (ht : t < 2 - p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ w : ℝ → ℝ≥0∞, Measurable w →
      (∫⁻ θ in Ioc (-Real.pi) Real.pi, w θ ^ (1 / (p - 1))) ≤ 1 →
      ∀ φ : ℝ, (∫⁻ θ in Ioc (-Real.pi) Real.pi,
        w θ * ENNReal.ofReal |Real.sin (θ - φ)| ^ (-t)) ≤ C := by
  have hp₀ : 0 < p - 1 := by linarith
  have htwo : 0 < 2 - p := sub_pos.mpr hp₂
  obtain ⟨C, hC, hCeq⟩ := lintegral_abs_sin_sub_neg_rpow
    (div_pos ht₀ htwo) ((div_lt_one htwo).mpr ht)
  refine ⟨C ^ (2 - p), ENNReal.rpow_ne_top_of_nonneg htwo.le hC, ?_⟩
  intro w hw hnorm φ
  have hpq : (1 / (p - 1)).HolderConjugate (1 / (2 - p)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [one_div, one_lt_inv₀ hp₀]
      linarith
    · simp only [one_div, inv_inv]
      ring
  have hk : Measurable (fun θ ↦ ENNReal.ofReal |Real.sin (θ - φ)| ^ (-t)) := by
    fun_prop
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict (Ioc (-Real.pi) Real.pi)) hpq hw.aemeasurable hk.aemeasurable
  have hkernel : (∫⁻ θ in Ioc (-Real.pi) Real.pi,
      (ENNReal.ofReal |Real.sin (θ - φ)| ^ (-t)) ^ (1 / (2 - p))) = C := by
    simpa only [← ENNReal.rpow_mul, mul_one_div, neg_div] using hCeq φ
  simp only [Pi.mul_apply] at hh
  rw [hkernel] at hh
  simp only [one_div, inv_inv] at hh hnorm
  exact hh.trans (mul_le_of_le_one_left' (ENNReal.rpow_le_one hnorm hp₀.le))

end FalconerPacking
