/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SchwartzMeasureReconstruction
import FalconerPacking.CompactSourceSchwartz

/-!
# Compact smooth annular reconstruction

A fixed explicitly constructed smooth cutoff equals one near the bounded source. Applying it
to the low-frequency term and the dyadic annular source convolutions gives actual compactly
supported Schwartz functions. Their finite sums telescope and reconstruct the source against
all bounded continuous complex tests.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal Topology

namespace FalconerPacking

/-- The fixed spatial bump has a unit region strictly larger than the source norm bound. -/
def sourceCutoffBump (M : ℝ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
  ⟨max M 0 + 1, max M 0 + 2, by positivity, by linarith⟩

/-- The spatial cutoff, bundled as a compactly supported Schwartz function. -/
def sourceSchwartzCutoff (M : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ((sourceCutoffBump M).hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (sourceCutoffBump M).contDiff)

theorem hasCompactSupport_sourceSchwartzCutoff (M : ℝ) :
    HasCompactSupport (sourceSchwartzCutoff M : EuclideanSpace ℝ (Fin 2) → ℂ) :=
  (sourceCutoffBump M).hasCompactSupport.comp_left Complex.ofReal_zero

/-- The cutoff is one on an open neighborhood of the closed source ball. -/
theorem sourceSchwartzCutoff_eq_one {M : ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ < max M 0 + 1) : sourceSchwartzCutoff M x = 1 := by
  change ((sourceCutoffBump M) x : ℂ) = 1
  rw [(sourceCutoffBump M).one_of_mem_closedBall]
  · norm_num
  · simpa only [Metric.mem_closedBall, dist_zero_right, sourceCutoffBump] using hx.le

theorem norm_sourceSchwartzCutoff_le_one (M : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    ‖sourceSchwartzCutoff M x‖ ≤ 1 := by
  change ‖((sourceCutoffBump M) x : ℂ)‖ ≤ 1
  rw [Complex.norm_of_nonneg (sourceCutoffBump M).nonneg]
  exact (sourceCutoffBump M).le_one

/-- Actual source pieces: the zeroth piece is low frequency, subsequent pieces are annular. -/
def compactAnnularSource (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ)) (T : ℕ) :
    ℕ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ
  | 0 => cutoffSchwartzMeasureConvolution μ hμ (lowpassSchwartzKernel 1 (by norm_num))
      (χ.smooth ⊤) hχ
  | n + 1 => cutoffSchwartzMeasureConvolution μ hμ (dyadicAnnularKernel T n)
      (χ.smooth ⊤) hχ

/-- All pieces have the same compact source support cutoff. -/
theorem support_compactAnnularSource_subset
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ)) (T n : ℕ) :
    Function.support (compactAnnularSource μ hμ χ hχ T n) ⊆ Function.support χ := by
  intro x hx
  cases n with
  | zero => exact fun h ↦ hx (by simp [compactAnnularSource, h])
  | succ n => exact fun h ↦ hx (by simp [compactAnnularSource, h])

/-- Finite reconstruction is a pointwise identity, before taking any limit or pushforward. -/
theorem sum_compactAnnularSource
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ)) (T N : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    (∑ n ∈ Finset.range (N + 1), compactAnnularSource μ hμ χ hχ T n x) =
      χ x *
        schwartzMeasureDensity μ (lowpassSchwartzKernel (2 ^ (T * N)) (by positivity)) x := by
  have hstep (n : ℕ) : compactAnnularSource μ hμ χ hχ T (n + 1) x =
      χ x *
          schwartzMeasureDensity μ (lowpassSchwartzKernel (2 ^ (T * (n + 1))) (by positivity)) x -
        χ x *
          schwartzMeasureDensity μ (lowpassSchwartzKernel (2 ^ (T * n)) (by positivity)) x := by
    simp only [compactAnnularSource, cutoffSchwartzMeasureConvolution_apply,
      dyadicAnnularKernel, sub_apply, schwartzMeasureDensity]
    rw [integral_sub (integrable_schwartzMeasureDensity_integrand μ _ x)
      (integrable_schwartzMeasureDensity_integrand μ _ x), mul_sub]
  rw [Finset.sum_range_succ']
  simp_rw [hstep]
  rw [Finset.sum_range_sub (fun n ↦ χ x *
    schwartzMeasureDensity μ (lowpassSchwartzKernel (2 ^ (T * n)) (by positivity)) x)]
  simp [compactAnnularSource, schwartzMeasureDensity]

/-- No first-norm growth is hidden in the full source annuli. -/
theorem integral_norm_compactAnnularSource_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχnorm : ∀ x, ‖χ x‖ ≤ 1) (T n : ℕ) :
    (∫ x, ‖compactAnnularSource μ hμ χ hχ T n x‖) ≤
      2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖ := by
  have hcut (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) :
      (∫ x, ‖cutoffSchwartzMeasureConvolution μ hμ K (χ.smooth ⊤) hχ x‖) ≤
        μ.real univ * ∫ x, ‖K x‖ := by
    refine le_trans (integral_mono
      (cutoffSchwartzMeasureConvolution μ hμ K (χ.smooth ⊤) hχ).integrable.norm
      (integrable_schwartzMeasureDensity μ K).norm ?_) (integral_norm_schwartzMeasureDensity_le μ K)
    intro x
    change ‖χ x * schwartzMeasureDensity μ K x‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχnorm x)
  cases n with
  | zero =>
      refine (hcut (lowpassSchwartzKernel 1 (by norm_num))).trans ?_
      rw [integral_norm_lowpassSchwartzKernel]
      have hm : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
      have hi : 0 ≤ ∫ x, ‖unitReproducingKernel x‖ := integral_nonneg (fun _ ↦ norm_nonneg _)
      nlinarith
  | succ n =>
      refine (hcut (dyadicAnnularKernel T n)).trans ?_
      have h := mul_le_mul_of_nonneg_left (integral_norm_dyadicAnnularKernel_le T n)
        (show 0 ≤ μ.real univ from ENNReal.toReal_nonneg)
      simpa only [mul_left_comm, mul_assoc] using h

/-- The constructed smooth source expansion reconstructs every finite bounded source measure. -/
theorem tendsto_integral_compactAnnularSource
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hχ : HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ))
    (hχone : ∀ᵐ x ∂μ, χ x = 1) {T : ℕ} (hT : 0 < T)
    (g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℂ) :
    Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range N, compactAnnularSource μ hμ χ hχ T n x) * g x)
      atTop (𝓝 (∫ x, g x ∂μ)) := by
  let ψ := χ.toBoundedContinuousFunction * g
  have h := tendsto_integral_lowpassMeasureDensity μ
    (fun n ↦ by positivity : ∀ n : ℕ, 0 < (2 : ℝ) ^ (T * n))
    (tendsto_dyadic_blockScale hT) ψ
  have heq : (∫ x, ψ x ∂μ) = ∫ x, g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hχone] with x hx
    simp [ψ, hx]
  rw [heq] at h
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert h using 1
  funext N
  apply integral_congr_ae
  filter_upwards with x
  rw [sum_compactAnnularSource]
  change χ x * _ * g x = _ * (χ x * g x)
  ring

/-- Compactness alone supplies the cutoff and the actual smooth annular expansion. The formulas
for the zeroth and successor pieces identify the expansion without a reconstruction hypothesis. -/
theorem exists_compact_annular_reconstruction
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsCompact S) (hμS : μ Sᶜ = 0)
    {T : ℕ} (hT : 0 < T) :
    ∃ χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ,
      HasCompactSupport (χ : EuclideanSpace ℝ (Fin 2) → ℂ) ∧
      (∀ x, ‖χ x‖ ≤ 1) ∧
      (∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ S ⊆ U ∧ ∀ x ∈ U, χ x = 1) ∧
      ∃ f : ℕ → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ,
        (∀ x, f 0 x = χ x * schwartzMeasureDensity μ (lowpassSchwartzKernel 1 (by norm_num)) x) ∧
        (∀ n x, f (n + 1) x = χ x * schwartzMeasureDensity μ (dyadicAnnularKernel T n) x) ∧
        (∀ n, Function.support (f n) ⊆ Function.support χ) ∧
        (∀ n, (∫ x, ‖f n x‖) ≤ 2 * μ.real univ * ∫ x, ‖unitReproducingKernel x‖) ∧
        ∀ g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℂ,
          Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range N, f n x) * g x)
            atTop (𝓝 (∫ x, g x ∂μ)) := by
  obtain ⟨M, _, hM⟩ := hS.isBounded.exists_pos_norm_le
  have hmem : ∀ᵐ x ∂μ, x ∈ S := ae_iff.mpr hμS
  have hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ M := hmem.mono (fun x hx ↦ hM x hx)
  let χ := sourceSchwartzCutoff M
  have hχ := hasCompactSupport_sourceSchwartzCutoff M
  have hone : ∀ᵐ x ∂μ, χ x = 1 := hμ.mono fun x hx ↦
    sourceSchwartzCutoff_eq_one (by linarith [le_max_left M 0])
  refine ⟨χ, hχ, norm_sourceSchwartzCutoff_le_one M, ?_,
    compactAnnularSource μ hμ χ hχ T, (fun _ ↦ rfl), (fun _ _ ↦ rfl),
    support_compactAnnularSource_subset μ hμ χ hχ T,
    integral_norm_compactAnnularSource_le μ hμ χ hχ (norm_sourceSchwartzCutoff_le_one M) T,
    tendsto_integral_compactAnnularSource μ hμ χ hχ hone hT⟩
  refine ⟨Metric.ball 0 (max M 0 + 1), Metric.isOpen_ball, ?_, ?_⟩
  · intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hM x hx, le_max_left M 0]
  · intro x hx
    exact sourceSchwartzCutoff_eq_one (by simpa only [Metric.mem_ball, dist_zero_right] using hx)

end FalconerPacking
