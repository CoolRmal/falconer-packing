/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.LocalEnergy
import FalconerPacking.PinnedMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Positive density limits

This file formalizes the measure-theoretic limit step in the coherent positive-linearization
argument.  An integrable real function determines the finite measure whose density is its
positive part.  The main goal is to show that this construction is compatible with convergence
in `L¹`, so that a weak limit of the positive affine laws remains absolutely continuous.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- The finite measure represented by the positive part of an `L¹` function. -/
def finiteMeasureOfL1Density
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α →₁[μ] ℝ) :
    FiniteMeasure α :=
  ⟨μ.withDensity (fun x ↦ ENNReal.ofReal (f x)),
    isFiniteMeasure_withDensity_ofReal (L1.integrable_coeFn f).hasFiniteIntegral⟩

@[simp]
theorem finiteMeasureOfL1Density_toMeasure
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α →₁[μ] ℝ) :
    (finiteMeasureOfL1Density μ f : Measure α) =
      μ.withDensity (fun x ↦ ENNReal.ofReal (f x)) := rfl

/-- Integration against `finiteMeasureOfL1Density` is integration against the positive part of
the `L¹` function. -/
theorem integral_finiteMeasureOfL1Density
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α →₁[μ] ℝ) (g : α → ℝ) :
    ∫ x, g x ∂(finiteMeasureOfL1Density μ f : Measure α) =
      ∫ x, Lp.posPart f x * g x ∂μ := by
  rw [finiteMeasureOfL1Density_toMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (L1.integrable_coeFn f).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (ae_of_all μ fun _ ↦ ENNReal.ofReal_lt_top) g]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart f] with x hx
  rw [hx]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

/-- Testing the density measures against a bounded continuous function is Lipschitz in the
`L¹` distance of the densities. -/
theorem dist_integral_finiteMeasureOfL1Density_le
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) (f g : α →₁[μ] ℝ) (h : BoundedContinuousFunction α ℝ) :
    dist (∫ x, h x ∂(finiteMeasureOfL1Density μ f : Measure α))
        (∫ x, h x ∂(finiteMeasureOfL1Density μ g : Measure α)) ≤
      ‖h‖ * dist f g := by
  rw [integral_finiteMeasureOfL1Density, integral_finiteMeasureOfL1Density]
  have hh_meas : AEStronglyMeasurable (fun x ↦ h x) μ :=
    h.continuous.aestronglyMeasurable
  have hh_bound : ∀ᵐ x ∂μ, ‖h x‖ ≤ ‖h‖ :=
    ae_of_all μ fun x ↦ h.norm_coe_le_norm x
  have hfint : Integrable (fun x ↦ Lp.posPart f x * h x) μ :=
    (L1.integrable_coeFn (Lp.posPart f)).mul_bdd hh_meas hh_bound
  have hgint : Integrable (fun x ↦ Lp.posPart g x * h x) μ :=
    (L1.integrable_coeFn (Lp.posPart g)).mul_bdd hh_meas hh_bound
  rw [dist_eq_norm, ← integral_sub hfint hgint]
  calc
    ‖∫ x, Lp.posPart f x * h x - Lp.posPart g x * h x ∂μ‖
        ≤ ∫ x, ‖Lp.posPart f x * h x - Lp.posPart g x * h x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖h‖ * ‖Lp.posPart f x - Lp.posPart g x‖ ∂μ := by
      apply integral_mono_ae
      · exact (hfint.sub hgint).norm
      · refine ((L1.integrable_coeFn
          (Lp.posPart f - Lp.posPart g)).norm.const_mul ‖h‖).congr ?_
        filter_upwards [Lp.coeFn_sub (Lp.posPart f) (Lp.posPart g)] with x hx
        rw [hx, Pi.sub_apply]
      · filter_upwards with x
        rw [← sub_mul]
        calc
          ‖(Lp.posPart f x - Lp.posPart g x) * h x‖
              ≤ ‖Lp.posPart f x - Lp.posPart g x‖ * ‖h x‖ := norm_mul_le _ _
          _ ≤ ‖Lp.posPart f x - Lp.posPart g x‖ * ‖h‖ :=
            mul_le_mul_of_nonneg_left (h.norm_coe_le_norm x) (norm_nonneg _)
          _ = ‖h‖ * ‖Lp.posPart f x - Lp.posPart g x‖ := mul_comm _ _
    _ = ‖h‖ * ‖Lp.posPart f - Lp.posPart g‖ := by
      rw [integral_const_mul, L1.norm_eq_integral_norm]
      apply congrArg (‖h‖ * ·)
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Lp.posPart f) (Lp.posPart g)] with x hx
      rw [hx, Pi.sub_apply]
    _ = ‖h‖ * dist (Lp.posPart f) (Lp.posPart g) := by rw [dist_eq_norm]
    _ ≤ ‖h‖ * dist f g := by
      gcongr
      change dist
        (Lp.lipschitzWith_pos_part.compLp (max_eq_right le_rfl) f)
        (Lp.lipschitzWith_pos_part.compLp (max_eq_right le_rfl) g) ≤ dist f g
      simpa only [NNReal.coe_one, one_mul] using
        (Lp.lipschitzWith_pos_part.lipschitzWith_compLp
          (max_eq_right le_rfl)).dist_le_mul f g

/-- Convergence in `L¹` implies weak convergence of the finite measures represented by the
positive parts. -/
theorem tendsto_finiteMeasureOfL1Density
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) {l : Filter ι} {f : ι → α →₁[μ] ℝ} {g : α →₁[μ] ℝ}
    (hfg : Tendsto f l (𝓝 g)) :
    Tendsto (fun i ↦ finiteMeasureOfL1Density μ (f i)) l
      (𝓝 (finiteMeasureOfL1Density μ g)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro h
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero
  · exact fun _ ↦ dist_nonneg
  · exact fun i ↦ dist_integral_finiteMeasureOfL1Density_le μ (f i) g h
  · have hdist : Tendsto (fun i ↦ dist (f i) g) l (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.1 hfg
    simpa using hdist.const_mul ‖h‖

/-- A finite-measure weak limit of positive `L¹` densities is the measure represented by their
`L¹` limit. -/
theorem finiteMeasure_eq_of_tendsto_L1Density
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [T2Space (FiniteMeasure α)]
    (μ : Measure α) {l : Filter ι} [NeBot l]
    {f : ι → α →₁[μ] ℝ} {g : α →₁[μ] ℝ} {ν : FiniteMeasure α}
    (hfg : Tendsto f l (𝓝 g))
    (hν : Tendsto (fun i ↦ finiteMeasureOfL1Density μ (f i)) l (𝓝 ν)) :
    ν = finiteMeasureOfL1Density μ g :=
  tendsto_nhds_unique hν (tendsto_finiteMeasureOfL1Density μ hfg)

/-- Consequently, a weak limit identified through positive `L¹` densities is absolutely
continuous with respect to the reference measure. -/
theorem absolutelyContinuous_of_tendsto_L1Density
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [T2Space (FiniteMeasure α)]
    (μ : Measure α) {l : Filter ι} [NeBot l]
    {f : ι → α →₁[μ] ℝ} {g : α →₁[μ] ℝ} {ν : FiniteMeasure α}
    (hfg : Tendsto f l (𝓝 g))
    (hν : Tendsto (fun i ↦ finiteMeasureOfL1Density μ (f i)) l (𝓝 ν)) :
    (ν : Measure α) ≪ μ := by
  rw [finiteMeasure_eq_of_tendsto_L1Density μ hfg hν,
    finiteMeasureOfL1Density_toMeasure]
  exact withDensity_absolutelyContinuous _ _

/-- The abstract coherent criterion: a summable first-norm comparison for positive density laws,
together with weak identification of those laws, forces the weak limit to be absolutely
continuous. -/
theorem absolutelyContinuous_of_coherentDensityComparison
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [T2Space (FiniteMeasure α)]
    (μ : Measure α) {f : ℕ → α →₁[μ] ℝ} {ν : FiniteMeasure α}
    {Z : ℕ → ℝ≥0∞} {K : ℝ≥0∞} {eta : ℝ}
    (hK : K ≠ ∞) (hZ : (∑' n, Z n ^ eta) ≠ ∞)
    (hstep : ∀ n, edist (f n) (f n.succ) ≤ K * Z n ^ eta)
    (hweak : Tendsto (fun n ↦ finiteMeasureOfL1Density μ (f n)) atTop (𝓝 ν)) :
    (ν : Measure α) ≪ μ := by
  obtain ⟨g, hg⟩ :=
    exists_tendsto_of_edist_le_coherentEnergy hK hZ hstep
  exact absolutelyContinuous_of_tendsto_L1Density μ hg hweak

/-- Almost-everywhere convergence of measurable random variables gives weak convergence of their
pushforward laws, stated in the finite-measure space used by the positive-density argument. -/
theorem tendsto_map_toFiniteMeasure_of_ae_tendsto
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α]
    (μ : ProbabilityMeasure Ω) {F : ℕ → Ω → α} {G : Ω → α}
    (hF : ∀ n, AEMeasurable (F n) (μ : Measure Ω))
    (hG : AEMeasurable G (μ : Measure Ω))
    (hlim : ∀ᵐ ω ∂(μ : Measure Ω), Tendsto (fun n ↦ F n ω) atTop (𝓝 (G ω))) :
    Tendsto
      (fun n ↦ ProbabilityMeasure.toFiniteMeasure
        (⟨(μ : Measure Ω).map (F n),
          Measure.isProbabilityMeasure_map (hF n)⟩ : ProbabilityMeasure α))
      atTop
      (𝓝 (ProbabilityMeasure.toFiniteMeasure
        (⟨(μ : Measure Ω).map G,
          Measure.isProbabilityMeasure_map hG⟩ : ProbabilityMeasure α))) := by
  have hdist := tendstoInDistribution_of_ae_tendsto hF hG hlim
  exact (ProbabilityMeasure.toFiniteMeasure_continuous.tendsto _).comp hdist.tendsto

/-- A uniform pointwise error tending to zero identifies the weak limit of the pushforward
laws.  This is the form used for the quadratic affine approximation to distance. -/
theorem tendsto_map_toFiniteMeasure_of_dist_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [PseudoMetricSpace α] [BorelSpace α]
    (μ : ProbabilityMeasure Ω) {F : ℕ → Ω → α} {G : Ω → α} {ε : ℕ → ℝ}
    (hF : ∀ n, AEMeasurable (F n) (μ : Measure Ω))
    (hG : AEMeasurable G (μ : Measure Ω))
    (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ n ω, dist (F n ω) (G ω) ≤ ε n) :
    Tendsto
      (fun n ↦ ProbabilityMeasure.toFiniteMeasure
        (⟨(μ : Measure Ω).map (F n),
          Measure.isProbabilityMeasure_map (hF n)⟩ : ProbabilityMeasure α))
      atTop
      (𝓝 (ProbabilityMeasure.toFiniteMeasure
        (⟨(μ : Measure Ω).map G,
          Measure.isProbabilityMeasure_map hG⟩ : ProbabilityMeasure α))) := by
  apply tendsto_map_toFiniteMeasure_of_ae_tendsto μ hF hG
  filter_upwards with ω
  apply tendsto_iff_dist_tendsto_zero.2
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ hclose n ω) hε

/-- The preceding weak-limit identification only needs the uniform error bound almost
everywhere at each scale.  Countability of the scales produces one full-measure set on which
all bounds hold. -/
theorem tendsto_map_toFiniteMeasure_of_ae_dist_le
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [PseudoMetricSpace α] [BorelSpace α]
    (μ : ProbabilityMeasure Ω) {F : ℕ → Ω → α} {G : Ω → α} {ε : ℕ → ℝ}
    (hF : ∀ n, AEMeasurable (F n) (μ : Measure Ω))
    (hG : AEMeasurable G (μ : Measure Ω))
    (hε : Tendsto ε atTop (𝓝 0))
    (hclose : ∀ n, ∀ᵐ ω ∂(μ : Measure Ω), dist (F n ω) (G ω) ≤ ε n) :
    Tendsto
      (fun n ↦ ProbabilityMeasure.toFiniteMeasure
        (⟨(μ : Measure Ω).map (F n),
          Measure.isProbabilityMeasure_map (hF n)⟩ : ProbabilityMeasure α))
      atTop
      (𝓝 (ProbabilityMeasure.toFiniteMeasure
        (⟨(μ : Measure Ω).map G,
          Measure.isProbabilityMeasure_map hG⟩ : ProbabilityMeasure α))) := by
  apply tendsto_map_toFiniteMeasure_of_ae_tendsto μ hF hG
  filter_upwards [ae_all_iff.2 hclose] with ω hω
  apply tendsto_iff_dist_tendsto_zero.2
  exact squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ hω n) hε

end FalconerPacking
