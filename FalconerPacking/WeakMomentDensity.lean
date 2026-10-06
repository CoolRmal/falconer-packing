/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.WeakDensityLimit
public import FalconerPacking.RadialProjectionWeakMoment

/-!
# Actual density moments from open-set power bounds

Outer regularity extends an open-set mass bound to every set. Applying that bound to
superlevel sets of the actual Radon–Nikodym derivative gives a weak power estimate and
all strictly smaller positive moments. In particular a weak limit retains some moment
strictly greater than one whenever its open-set power exponent lies strictly between
zero and one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace FalconerPacking

/-- For a finite outer regular reference measure, an open power bound holds on every set. -/
theorem measure_power_bound_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) (A : Set α) :
    μ A ≤ K * ν A ^ θ := by
  haveI : (𝓝[>] (ν A)).NeBot :=
    nhdsGT_neBot_of_exists_gt ⟨∞, measure_lt_top ν A⟩
  have hlim : Tendsto (fun t : ℝ≥0∞ ↦ K * t ^ θ) (𝓝[>] (ν A))
      (𝓝 (K * ν A ^ θ)) :=
    ((ENNReal.continuous_const_mul hK).comp ENNReal.continuous_rpow_const).continuousAt
      |>.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  obtain ⟨U, hAU, hU, hUt⟩ := A.exists_isOpen_lt_of_lt (μ := ν) t ht
  exact (measure_mono hAU).trans ((hbound U hU).trans
    (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hUt.le hθ)))

/-- The elementary weak-exponent rearrangement used for density level sets. -/
theorem ennreal_power_mass_bound_implies_tail
    {T m K : ℝ≥0∞} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hm : m ≠ ∞)
    (h : T * m ≤ K * m ^ θ) :
    T ^ (1 / (1 - θ) : ℝ) * m ≤ K ^ (1 / (1 - θ) : ℝ) := by
  by_cases hm₀ : m = 0
  · simp [hm₀]
  have hp : 0 < (1 - θ)⁻¹ := inv_pos.2 (sub_pos.2 hθ₁)
  have hmθ₀ : m ^ θ ≠ 0 :=
    fun hz ↦ hm₀ ((ENNReal.rpow_eq_zero_iff_of_pos hθ₀).1 hz)
  have hmθ : m ^ θ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hθ₀.le hm
  have hdiv : T * m ^ (1 - θ) ≤ K := by
    rw [ENNReal.rpow_sub _ _ hm₀ hm, ENNReal.rpow_one, ← mul_div_assoc]
    exact (ENNReal.div_le_iff hmθ₀ hmθ).2 h
  have hh := ENNReal.rpow_le_rpow hdiv hp.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul,
    mul_inv_cancel₀ (sub_pos.2 hθ₁).ne', ENNReal.rpow_one] at hh
  simpa only [one_div] using hh

/-- Open-set power control gives a sharp weak exponent for the actual density. -/
theorem rnDeriv_dyadic_tail_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) (n : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ n) ^ (1 / (1 - θ) : ℝ) *
      ν {x | (2 : ℝ) ^ n ≤ (μ.rnDeriv ν x).toReal} ≤ K ^ (1 / (1 - θ) : ℝ) := by
  let A := {x | (2 : ℝ) ^ n ≤ (μ.rnDeriv ν x).toReal}
  have hlevel : ENNReal.ofReal ((2 : ℝ) ^ n) * ν A ≤ μ A := by
    calc
      _ = ∫⁻ _ in A, ENNReal.ofReal ((2 : ℝ) ^ n) ∂ν := by simp
      _ ≤ ∫⁻ x in A, μ.rnDeriv ν x ∂ν := by
        apply setLIntegral_mono (Measure.measurable_rnDeriv μ ν)
        intro x hx
        exact (ENNReal.ofReal_le_ofReal hx).trans ENNReal.ofReal_toReal_le
      _ ≤ μ A := Measure.setLIntegral_rnDeriv_le A
  exact ennreal_power_mass_bound_implies_tail hθ₀ hθ₁ (measure_ne_top ν A)
    (hlevel.trans (measure_power_bound_of_open_power_bound hK hθ₀.le hbound A))

/-- A quantitative smaller-moment bound for the real-valued actual density. -/
theorem lintegral_rnDeriv_toReal_rpow_le_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ q : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hq : 0 ≤ q) (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) :
    (∫⁻ x, ENNReal.ofReal (μ.rnDeriv ν x).toReal ^ q ∂ν) ≤
      ν univ + (2 : ℝ≥0∞) ^ q * K ^ (1 / (1 - θ) : ℝ) *
        (1 - (2 : ℝ≥0∞) ^ (q - 1 / (1 - θ)))⁻¹ :=
  lintegral_rpow_le_of_dyadic_tail ν (Measure.measurable_rnDeriv μ ν).ennreal_toReal hq
    (rnDeriv_dyadic_tail_of_open_power_bound hK hθ₀ hθ₁ hbound)

/-- Every nonnegative exponent strictly below the weak exponent gives a finite density moment. -/
theorem lintegral_rnDeriv_toReal_rpow_lt_top_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ q : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hq : 0 ≤ q) (hqp : q < 1 / (1 - θ))
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) :
    (∫⁻ x, ENNReal.ofReal (μ.rnDeriv ν x).toReal ^ q ∂ν) < ∞ := by
  apply lintegral_rpow_lt_top_of_dyadic_tail ν
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal hq hqp
    (ENNReal.rpow_lt_top_of_nonneg
      (show 0 ≤ 1 / (1 - θ) by positivity) hK)
  exact rnDeriv_dyadic_tail_of_open_power_bound hK hθ₀ hθ₁ hbound

/-- Open power bounds yield absolute continuity and a finite moment of the actual derivative. -/
theorem absolutelyContinuous_and_rnDeriv_moment_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ q : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hq : 0 ≤ q) (hqp : q < 1 / (1 - θ))
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) :
    μ ≪ ν ∧ (∫⁻ x, μ.rnDeriv ν x ^ q ∂ν) < ∞ := by
  refine ⟨absolutelyContinuous_of_open_power_bound hK hθ₀ hbound, ?_⟩
  have heq : (∫⁻ x, μ.rnDeriv ν x ^ q ∂ν) =
      ∫⁻ x, ENNReal.ofReal (μ.rnDeriv ν x).toReal ^ q ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
    rw [ENNReal.ofReal_toReal hx.ne]
  rw [heq]
  exact lintegral_rnDeriv_toReal_rpow_lt_top_of_open_power_bound
    hK hθ₀ hθ₁ hq hqp hbound

/-- The actual derivative gives a nonnegative measurable density with a finite smaller moment. -/
theorem exists_density_moment_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ q : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hq : 0 ≤ q) (hqp : q < 1 / (1 - θ))
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) :
    ∃ f : α → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      μ = ν.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂ν) < ∞ := by
  refine ⟨fun x ↦ (μ.rnDeriv ν x).toReal, (Measure.measurable_rnDeriv μ ν).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, ?_,
    lintegral_rnDeriv_toReal_rpow_lt_top_of_open_power_bound hK hθ₀ hθ₁ hq hqp hbound⟩
  calc
    μ = ν.withDensity (μ.rnDeriv ν) :=
      (Measure.withDensity_rnDeriv_eq μ ν
        (absolutelyContinuous_of_open_power_bound hK hθ₀ hbound)).symm
    _ = ν.withDensity (fun x ↦ ENNReal.ofReal (μ.rnDeriv ν x).toReal) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm

/-- A strict open-set power bound always retains a density moment greater than one. -/
theorem exists_gt_one_density_moment_of_open_power_bound
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [ν.OuterRegular]
    {K : ℝ≥0∞} (hK : K ≠ ∞) {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hbound : ∀ U : Set α, IsOpen U → μ U ≤ K * ν U ^ θ) :
    ∃ q : ℝ, 1 < q ∧ q < 1 / (1 - θ) ∧
      ∃ f : α → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
        μ = ν.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
        (∫⁻ x, ENNReal.ofReal (f x) ^ q ∂ν) < ∞ := by
  have hp : 1 < 1 / (1 - θ) := (lt_div_iff₀ (sub_pos.2 hθ₁)).2 (by linarith)
  obtain ⟨q, hq, hqp⟩ := exists_between hp
  exact ⟨q, hq, hqp, exists_density_moment_of_open_power_bound hK hθ₀ hθ₁
    (by linarith) hqp hbound⟩

end FalconerPacking
