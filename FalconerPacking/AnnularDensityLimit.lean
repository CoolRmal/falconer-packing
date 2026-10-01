/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PositiveLimit
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Summation and identification of annular distance densities

On a finite reference measure, summable second norms of good terms and summable first norms
of bad terms give an actual first-norm limit. The terms may be complex and need not be positive.
Reconstruction against bounded continuous tests identifies the limit with a positive measure.
The finite reference measure can be the pin measure times Lebesgue measure on a bounded distance
interval; no probability normalization is required.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace FalconerPacking

/-- The finite-measure second-norm estimate, in the real norm used for summing shell errors. -/
theorem norm_toL1_le_secondNorm
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [IsFiniteMeasure κ]
    {f : α → ℂ} (hf : MemLp f 2 κ) :
    ‖(hf.integrable (by norm_num)).toL1 f‖ ≤
      (eLpNorm f 2 κ).toReal * (κ univ ^ (1 / 2 : ℝ)).toReal := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hf.aestronglyMeasurable
  norm_num at h
  have hfin : eLpNorm f 2 κ * κ univ ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (measure_ne_top κ univ))
  have hreal := ENNReal.toReal_mono hfin h
  simpa only [Integrable.norm_toL1_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    ENNReal.toReal_mul] using hreal

/-- Summable good second norms and bad first norms give an absolutely convergent series in
the actual first-norm function space. -/
theorem summable_annularDensity_toL1_norm
    {α : Type*} [MeasurableSpace α] (κ : Measure α) [IsFiniteMeasure κ]
    (good bad : ℕ → α → ℂ) (hg : ∀ n, MemLp (good n) 2 κ)
    (hb : ∀ n, Integrable (bad n) κ)
    (hgs : Summable (fun n ↦ (eLpNorm (good n) 2 κ).toReal))
    (hbs : Summable (fun n ↦ ∫ x, ‖bad n x‖ ∂κ)) :
    Summable (fun n ↦
      ‖((hg n).integrable (by norm_num) |>.add (hb n)).toL1 (good n + bad n)‖) := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    ((hgs.mul_right (κ univ ^ (1 / 2 : ℝ)).toReal).add hbs)
  intro n
  rw [Integrable.toL1_add _ _ ((hg n).integrable (by norm_num)) (hb n)]
  refine (norm_add_le _ _).trans (add_le_add (norm_toL1_le_secondNorm κ (hg n)) ?_)
  exact le_of_eq (by
    rw [Integrable.norm_toL1_eq_lintegral_enorm,
      integral_norm_eq_lintegral_enorm (hb n).aestronglyMeasurable])

/-- Complex integration against a bounded continuous real test is Lipschitz in the first norm. -/
theorem dist_integral_L1_mul_boundedContinuous_le
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (κ : Measure α) (f g : α →₁[κ] ℂ) (φ : BoundedContinuousFunction α ℝ) :
    dist (∫ x, f x * (φ x : ℂ) ∂κ) (∫ x, g x * (φ x : ℂ) ∂κ) ≤
      ‖φ‖ * dist f g := by
  have hφm : AEStronglyMeasurable (fun x ↦ (φ x : ℂ)) κ :=
    (Complex.continuous_ofReal.comp φ.continuous).aestronglyMeasurable
  have hφb : ∀ᵐ x ∂κ, ‖(φ x : ℂ)‖ ≤ ‖φ‖ :=
    ae_of_all κ fun x ↦ by simpa using φ.norm_coe_le_norm x
  have hf := (L1.integrable_coeFn f).mul_bdd hφm hφb
  have hg := (L1.integrable_coeFn g).mul_bdd hφm hφb
  rw [dist_eq_norm, ← integral_sub hf hg]
  calc
    ‖∫ x, f x * (φ x : ℂ) - g x * (φ x : ℂ) ∂κ‖
        ≤ ∫ x, ‖f x * (φ x : ℂ) - g x * (φ x : ℂ)‖ ∂κ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖φ‖ * ‖f x - g x‖ ∂κ := by
      apply integral_mono_ae (hf.sub hg).norm
      · refine ((L1.integrable_coeFn (f - g)).norm.const_mul ‖φ‖).congr ?_
        filter_upwards [Lp.coeFn_sub f g] with x hx
        rw [hx, Pi.sub_apply]
      · filter_upwards [hφb] with x hx
        dsimp only [Pi.sub_apply]
        rw [← sub_mul, norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = ‖φ‖ * dist f g := by
      rw [integral_const_mul, dist_eq_norm, L1.norm_eq_integral_norm]
      congr 1
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub f g] with x hx
      rw [hx, Pi.sub_apply]

/-- The actual complex test integrals converge whenever the densities converge in first norm. -/
theorem tendsto_integral_L1_mul_boundedContinuous
    {α ι : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    (κ : Measure α) {l : Filter ι} {f : ι → α →₁[κ] ℂ} {g : α →₁[κ] ℂ}
    (hfg : Tendsto f l (𝓝 g)) (φ : BoundedContinuousFunction α ℝ) :
    Tendsto (fun i ↦ ∫ x, f i x * (φ x : ℂ) ∂κ) l
      (𝓝 (∫ x, g x * (φ x : ℂ) ∂κ)) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _ ↦ dist_nonneg)
    (fun i ↦ dist_integral_L1_mul_boundedContinuous_le κ (f i) g φ)
  simpa using (tendsto_iff_dist_tendsto_zero.1 hfg).const_mul ‖φ‖

/-- A signed integrable density that reconstructs a finite positive measure on continuous
tests forces absolute continuity. Positivity of the density is not an assumption. -/
theorem absolutelyContinuous_of_real_density_tests
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [HasOuterApproxClosed α]
    [BorelSpace α] (κ μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Integrable f κ)
    (htest : ∀ φ : BoundedContinuousFunction α ℝ,
      ∫ x, f x * φ x ∂κ = ∫ x, φ x ∂μ) : μ ≪ κ := by
  let μp := κ.withDensity (fun x ↦ ENNReal.ofReal (f x))
  let μn := κ.withDensity (fun x ↦ ENNReal.ofReal (-f x))
  haveI : IsFiniteMeasure μp := isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  haveI : IsFiniteMeasure μn := isFiniteMeasure_withDensity_ofReal hf.neg.hasFiniteIntegral
  have heq : μp = μ + μn := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro φ
    have hφm : AEStronglyMeasurable (fun x ↦ φ x) κ :=
      φ.continuous.aestronglyMeasurable
    have hφb : ∀ᵐ x ∂κ, ‖φ x‖ ≤ ‖φ‖ := ae_of_all κ φ.norm_coe_le_norm
    have hfi := hf.mul_bdd hφm hφb
    have hni := hf.neg.pos_part.mul_bdd hφm hφb
    change Integrable (fun x ↦ max (-f x) 0 * φ x) κ at hni
    rw [integral_add_measure (φ.integrable μ) (φ.integrable μn)]
    change (∫ x, φ x ∂κ.withDensity (fun x ↦ ENNReal.ofReal (f x))) =
      (∫ x, φ x ∂μ) + ∫ x, φ x ∂κ.withDensity (fun x ↦ ENNReal.ofReal (-f x))
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (ae_of_all κ fun _ ↦ ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀
      (show AEMeasurable (fun x ↦ ENNReal.ofReal (-f x)) κ from
        hf.aestronglyMeasurable.aemeasurable.neg.ennreal_ofReal)
      (ae_of_all κ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
    rw [← htest φ, ← integral_add hfi hni]
    apply integral_congr_ae
    filter_upwards with x
    have h : max (f x) 0 = f x + max (-f x) 0 := by
      by_cases hx : 0 ≤ f x
      · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero]
      · rw [max_eq_right (le_of_not_ge hx), max_eq_left (by linarith)]
        ring
    rw [h, add_mul]
  have hle : μ ≤ μp := heq ▸ Measure.le_add_right le_rfl
  exact (Measure.absolutelyContinuous_of_le hle).trans (withDensity_absolutelyContinuous _ _)

/-- Continuous test reconstruction identifies a complex integrable function with the actual
Radon--Nikodym density, and hence proves that its imaginary part vanishes and its real part is
nonnegative almost everywhere. -/
theorem complex_density_eq_rnDeriv_of_tests
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (κ μ : Measure E)
    [IsFiniteMeasure κ] [IsFiniteMeasure μ] {f : E → ℂ} (hf : Integrable f κ)
    (htest : ∀ φ : BoundedContinuousFunction E ℝ,
      ∫ x, f x * (φ x : ℂ) ∂κ = ((∫ x, φ x ∂μ : ℝ) : ℂ)) :
    μ ≪ κ ∧ f =ᵐ[κ] fun x ↦ ((μ.rnDeriv κ x).toReal : ℂ) := by
  have hac : μ ≪ κ := by
    apply absolutelyContinuous_of_real_density_tests κ μ hf.re
    intro φ
    have hi := hf.mul_bdd
      (Complex.continuous_ofReal.comp φ.continuous).aestronglyMeasurable
      (ae_of_all κ fun x ↦ by simpa using φ.norm_coe_le_norm x)
    have h := congrArg Complex.re (htest φ)
    change RCLike.re (∫ x, f x * (φ x : ℂ) ∂κ) = ∫ x, φ x ∂μ at h
    change Integrable (fun x ↦ f x * (φ x : ℂ)) κ at hi
    rw [← integral_re hi] at h
    simpa using h
  refine ⟨hac, ?_⟩
  have hri : Integrable (fun x ↦ (μ.rnDeriv κ x).toReal) κ :=
    integrableOn_univ.mp (Measure.integrableOn_toReal_rnDeriv (measure_ne_top μ univ))
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hri.ofReal.locallyIntegrable
  intro φ hφ hc
  let ψ : BoundedContinuousFunction E ℝ :=
    (⟨⟨φ, hφ.continuous⟩, hc⟩ : CompactlySupportedContinuousMap E ℝ).toBoundedContinuousFunction
  calc
    (∫ x, φ x • f x ∂κ) = ∫ x, f x * (ψ x : ℂ) ∂κ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [ψ, Complex.real_smul, mul_comm]
    _ = ((∫ x, ψ x ∂μ : ℝ) : ℂ) := htest ψ
    _ = ∫ x, (μ.rnDeriv κ x).toReal • (φ x : ℂ) ∂κ := by
      rw [integral_rnDeriv_smul hac, integral_complex_ofReal]
      rfl
    _ = ∫ x, φ x • ((μ.rnDeriv κ x).toReal : ℂ) ∂κ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Complex.real_smul, mul_comm]

/-- An absolutely summable complex density expansion reconstructing a finite positive measure
converges in the actual integral first norm to its nonnegative real density. -/
theorem exists_density_of_summable_L1_tests
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (κ μ : Measure E)
    [IsFiniteMeasure κ] [IsFiniteMeasure μ] (f : ℕ → E → ℂ)
    (hi : ∀ n, Integrable (f n) κ)
    (hs : Summable (fun n ↦ ‖(hi n).toL1 (f n)‖))
    (htest : ∀ φ : BoundedContinuousFunction E ℝ,
      Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range N, f n x) * (φ x : ℂ) ∂κ)
        atTop (𝓝 ((∫ x, φ x ∂μ : ℝ) : ℂ))) :
    ∃ F : E → ℂ, Integrable F κ ∧
      Tendsto (fun N ↦ ∫ x, ‖(∑ n ∈ Finset.range N, f n x) - F x‖ ∂κ)
        atTop (𝓝 0) ∧
      μ = κ.withDensity (fun x ↦ ENNReal.ofReal (F x).re) ∧
      (∀ᵐ x ∂κ, (F x).im = 0 ∧ 0 ≤ (F x).re) ∧ μ ≪ κ := by
  let u (n : ℕ) : E →₁[κ] ℂ := (hi n).toL1 (f n)
  have hu : Summable u := hs.of_norm
  let F : E →₁[κ] ℂ := ∑' n, u n
  have hlim : Tendsto (fun N ↦ ∑ n ∈ Finset.range N, u n) atTop (𝓝 F) :=
    hu.hasSum.tendsto_sum_nat
  have hcoe (N : ℕ) :
      (fun x ↦ (∑ n ∈ Finset.range N, u n) x) =ᵐ[κ]
        fun x ↦ ∑ n ∈ Finset.range N, f n x := by
    refine (Lp.coeFn_fun_finsetSum _ u).trans ?_
    filter_upwards [ae_all_iff.mpr (fun n ↦ (hi n).coeFn_toL1)] with x hx
    exact Finset.sum_congr rfl (fun n _ ↦ hx n)
  have htests : ∀ φ : BoundedContinuousFunction E ℝ,
      ∫ x, F x * (φ x : ℂ) ∂κ = ((∫ x, φ x ∂μ : ℝ) : ℂ) := by
    intro φ
    apply tendsto_nhds_unique (tendsto_integral_L1_mul_boundedContinuous κ hlim φ)
    refine (htest φ).congr' (Eventually.of_forall fun N ↦ ?_)
    apply integral_congr_ae
    filter_upwards [hcoe N] with x hx
    rw [hx]
  obtain ⟨hac, hrn⟩ := complex_density_eq_rnDeriv_of_tests κ μ
    (L1.integrable_coeFn F) htests
  refine ⟨F, L1.integrable_coeFn F, ?_, ?_, ?_, hac⟩
  · have hd := tendsto_iff_dist_tendsto_zero.1 hlim
    refine hd.congr' (Eventually.of_forall fun N ↦ ?_)
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (∑ n ∈ Finset.range N, u n) F, hcoe N] with x hx hx'
    rw [hx, Pi.sub_apply, hx']
  · rw [← Measure.withDensity_rnDeriv_eq μ κ hac]
    apply withDensity_congr_ae
    filter_upwards [hrn, Measure.rnDeriv_lt_top μ κ] with x hx hfin
    rw [hx, Complex.ofReal_re, ENNReal.ofReal_toReal hfin.ne]
  · filter_upwards [hrn] with x hx
    rw [hx]
    exact ⟨Complex.ofReal_im _, ENNReal.toReal_nonneg⟩

/-- The annular good/bad summation step. Only the total expansion reconstructs the positive
measure; no sign condition on any good term, bad term, or finite partial sum is needed. -/
theorem exists_density_of_annular_L2_L1_tests
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (κ μ : Measure E)
    [IsFiniteMeasure κ] [IsFiniteMeasure μ] (good bad : ℕ → E → ℂ)
    (hg : ∀ n, MemLp (good n) 2 κ) (hb : ∀ n, Integrable (bad n) κ)
    (hgs : Summable (fun n ↦ (eLpNorm (good n) 2 κ).toReal))
    (hbs : Summable (fun n ↦ ∫ x, ‖bad n x‖ ∂κ))
    (htest : ∀ φ : BoundedContinuousFunction E ℝ,
      Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range N, (good n x + bad n x)) *
        (φ x : ℂ) ∂κ) atTop (𝓝 ((∫ x, φ x ∂μ : ℝ) : ℂ))) :
    ∃ F : E → ℂ, Integrable F κ ∧
      Tendsto (fun N ↦ ∫ x, ‖(∑ n ∈ Finset.range N, (good n x + bad n x)) - F x‖ ∂κ)
        atTop (𝓝 0) ∧
      μ = κ.withDensity (fun x ↦ ENNReal.ofReal (F x).re) ∧
      (∀ᵐ x ∂κ, (F x).im = 0 ∧ 0 ≤ (F x).re) ∧ μ ≪ κ :=
  exists_density_of_summable_L1_tests κ μ (fun n ↦ good n + bad n)
    (fun n ↦ ((hg n).integrable (by norm_num)).add (hb n))
    (summable_annularDensity_toL1_norm κ good bad hg hb hgs hbs) htest

/-- The version for an infinite ambient reference measure: the reconstructed shell sums are
supported in a fixed region of finite reference measure. This applies directly to a finite pin
measure times full Lebesgue measure, with a bounded distance interval as the finite region. -/
theorem absolutelyContinuous_of_annular_tests_finite_region
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (κ μ : Measure E) [IsFiniteMeasure μ]
    {S : Set E} (hS : κ S ≠ ∞) (good bad : ℕ → E → ℂ)
    (hg : ∀ n, MemLp (good n) 2 κ) (hb : ∀ n, Integrable (bad n) κ)
    (hgs : Summable (fun n ↦ (eLpNorm (good n) 2 κ).toReal))
    (hbs : Summable (fun n ↦ ∫ x, ‖bad n x‖ ∂κ))
    (hsupp : ∀ n, ∀ᵐ x ∂κ, x ∉ S → good n x + bad n x = 0)
    (htest : ∀ φ : BoundedContinuousFunction E ℝ,
      Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range N, (good n x + bad n x)) *
        (φ x : ℂ) ∂κ) atTop (𝓝 ((∫ x, φ x ∂μ : ℝ) : ℂ))) : μ ≪ κ := by
  haveI : IsFiniteMeasure (κ.restrict S) := ⟨by simpa using hS.lt_top⟩
  have hgs' : Summable (fun n ↦ (eLpNorm (good n) 2 (κ.restrict S)).toReal) :=
    Summable.of_nonneg_of_le (fun _ ↦ ENNReal.toReal_nonneg)
      (fun n ↦ ENNReal.toReal_mono (hg n).eLpNorm_ne_top
        (eLpNorm_mono_measure _ Measure.restrict_le_self)) hgs
  have hbs' : Summable (fun n ↦ ∫ x, ‖bad n x‖ ∂κ.restrict S) :=
    Summable.of_nonneg_of_le (fun _ ↦ integral_nonneg (fun _ ↦ norm_nonneg _))
      (fun n ↦ integral_mono_measure Measure.restrict_le_self
        (ae_of_all κ fun _ ↦ norm_nonneg _) (hb n).norm) hbs
  have htest' : ∀ φ : BoundedContinuousFunction E ℝ,
      Tendsto (fun N ↦ ∫ x, (∑ n ∈ Finset.range N, (good n x + bad n x)) *
        (φ x : ℂ) ∂κ.restrict S) atTop (𝓝 ((∫ x, φ x ∂μ : ℝ) : ℂ)) := by
    intro φ
    refine (htest φ).congr' (Eventually.of_forall fun N ↦ ?_)
    symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [ae_all_iff.mpr hsupp] with x hx
    intro hxS
    simp [Finset.sum_eq_zero (fun n _ ↦ hx n hxS)]
  obtain ⟨_, _, _, _, _, hac⟩ := exists_density_of_annular_L2_L1_tests (κ.restrict S) μ
    good bad (fun n ↦ (hg n).restrict S) (fun n ↦ (hb n).restrict) hgs' hbs' htest'
  exact hac.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

end FalconerPacking
