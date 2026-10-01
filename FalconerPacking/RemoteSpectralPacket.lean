/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SpectralPacketFubini
import FalconerPacking.AngularSpectralWindowBounds
import FalconerPacking.SchwartzMeasureReconstruction

/-!
# Remote spectral circle averages of actual spatial packets

The smooth enlarged-cone contribution is controlled through the physical source integral.
The complementary contribution is controlled pointwise by the proved Fourier leakage bound.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ContDiff FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- A remote physical strip gives nonstationarity on the enlarged angular window. -/
theorem remote_strip_transverse_margin
    (x y : EuclideanSpace ℝ (Fin 2)) (α b w γ ε L : ℝ)
    (hx : |⟪angularDirection (α + Real.pi / 2), x⟫ - b| ≤ w)
    (hy : γ + w + L * ε ≤ |⟪angularDirection (α + Real.pi / 2), y⟫ - b|) :
    γ + L * ε ≤ |⟪y - x, angularDirection (α + Real.pi / 2)⟫| := by
  have h := abs_add_le
    (⟪angularDirection (α + Real.pi / 2), y⟫ -
      ⟪angularDirection (α + Real.pi / 2), x⟫)
    (⟪angularDirection (α + Real.pi / 2), x⟫ - b)
  rw [sub_add_sub_cancel] at h
  rw [real_inner_comm, inner_sub_right]
  linarith

/-- The actual smooth angular selector satisfies the remote first-norm estimate. -/
theorem exists_remote_window_spectral_bound (N : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S γ α b w : ℝ), 1 ≤ S → S⁻¹ ≤ γ → γ ≤ 1 →
      ∀ {f : EuclideanSpace ℝ (Fin 2) → ℂ}, Integrable f volume →
      ∀ y : EuclideanSpace ℝ (Fin 2),
        (∀ x ∈ support f, ‖y - x‖ ≤ L) →
        (∀ x ∈ support f, |⟪angularDirection (α + Real.pi / 2), x⟫ - b| ≤ w) →
        γ + w + L * (16 * Real.pi / S) ≤
          |⟪angularDirection (α + Real.pi / 2), y⟫ - b| →
        ∀ r : ℝ, 0 < r →
          ‖selectedSpectralCircleAverage
            (fun θ ↦ (angularSpectralWindow S (angularDirection α) θ : ℂ)) f y r‖ ≤
            C * (r * S⁻¹ * γ)⁻¹ ^ N * ∫ x, ‖f x‖ := by
  obtain ⟨B, hB, hb⟩ := angularSpectralWindow_finite_derivative_bound N
  obtain ⟨C, hC, hc⟩ := exists_remote_probability_circle_kernel_bound N L
  refine ⟨C * B, by positivity, ?_⟩
  intro S γ α b w hS hSγ hγ₁ f hf y hy hx hmargin r hr
  have hS₀ : 0 < S := lt_of_lt_of_le zero_lt_one hS
  apply norm_selectedSpectralCircleAverage_le
    (integrable_angularSpectralWindow S (angularDirection α)).2 hf
  intro x hxf
  have hd : ∀ k ≤ N, ∀ θ,
      ‖iteratedDeriv k (fun θ ↦ (angularSpectralWindow S (angularDirection α) θ : ℂ)) θ‖ ≤
        B * (S⁻¹)⁻¹ ^ k := by
    intro k hk θ
    rw [iteratedDeriv_ofReal (contDiff_angularSpectralWindow _ _) k, Complex.norm_real,
      inv_inv]
    exact hb S hS (angularDirection α) k hk θ
  exact hc
    (Complex.ofRealCLM.contDiff.comp (contDiff_angularSpectralWindow _ _))
    (fun θ ↦ congrArg Complex.ofReal (periodic_angularSpectralWindow S _ θ))
    S⁻¹ γ B (16 * Real.pi / S) α (by positivity) hSγ hγ₁ hB.le hd
    (tsupport_complex_angularSpectralWindow_subset hS₀ _)
    (y - x) (hy x hxf) (remote_strip_transverse_margin x y α b w γ _ L
      (hx x hxf) hmargin) r hr

/-- Pointwise spectral leakage controls the omitted circle average, uniformly in the pin. -/
theorem norm_pinnedSpectralCircleAverage_sub_selected_le
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    {a : ℝ → ℂ} (ha : Continuous a) (ha₁ : ∀ θ, ‖a θ‖ ≤ 1)
    (y : EuclideanSpace ℝ (Fin 2)) (r : ℝ) {E : ℝ}
    (htail : ∀ θ, ‖(1 - a θ) * (𝓕 f) (r • angularDirection θ)‖ ≤ E) :
    ‖pinnedSpectralCircleAverage f y r - selectedSpectralCircleAverage a f y r‖ ≤ E := by
  have hb (θ : ℝ) : ‖(𝓕 f) (r • angularDirection θ)‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (𝓕 f) := by
    simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ (𝓕 f) 0
      (r • angularDirection θ)
  have hF : Integrable (fun θ ↦
      (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) * (𝓕 f) (r • angularDirection θ))
        radialAngularProbability := by
    apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 (𝓕 f))).mono' (by fun_prop)
    exact ae_of_all _ fun θ ↦ by simpa only [norm_mul, Circle.norm_coe, one_mul] using hb θ
  have hA : Integrable (fun θ ↦ a θ *
      (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) * (𝓕 f) (r • angularDirection θ))
        radialAngularProbability := by
    apply hF.norm.mono' (by fun_prop)
    refine ae_of_all _ fun θ ↦ ?_
    simp only [norm_mul, Circle.norm_coe, mul_one, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (ha₁ θ)
  rw [pinnedSpectralCircleAverage_eq_probability, selectedSpectralCircleAverage]
  simp only [Circle.smul_def, smul_eq_mul]
  change ‖(∫ θ, (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) *
    (𝓕 f) (r • angularDirection θ) ∂radialAngularProbability) -
    ∫ θ, a θ * (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) *
      (𝓕 f) (r • angularDirection θ) ∂radialAngularProbability‖ ≤ E
  rw [← integral_sub hF hA]
  refine (norm_integral_le_of_norm_le_const (C := E) ?_).trans (by simp)
  refine ae_of_all _ fun θ ↦ ?_
  have he : (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) * (𝓕 f) (r • angularDirection θ) -
      a θ * (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) * (𝓕 f) (r • angularDirection θ) =
      (𝐞 (⟪y, r • angularDirection θ⟫) : ℂ) *
        ((1 - a θ) * (𝓕 f) (r • angularDirection θ)) := by ring
  rw [he, norm_mul, Circle.norm_coe, one_mul]
  exact htail θ

/-- Remote spectral decay for the constructed packet, with its actual first norm and an
explicit pointwise Fourier-leakage error. Both terms have arbitrary polynomial decay. -/
theorem exists_remote_sourceWavePacket_spectral_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (m : ℕ) (L : ℝ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (j : ℕ) (w γ : ℝ),
        0 < w → w ≤ 1 → (N : ℝ)⁻¹ ≤ γ → γ ≤ 1 →
        ∀ (k : ℤ) (y : EuclideanSpace ℝ (Fin 2)),
          sourceCutoffRadius χ hχ + ‖y‖ ≤ L →
          γ + w + L * (16 * Real.pi / N) ≤
            |⟪sourceWavePacketNormal N j, y⟫ - w * k| →
          ∀ r : ℝ, 0 < r →
            ‖pinnedSpectralCircleAverage
              (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y r‖ ≤
              C₁ * (r * (N : ℝ)⁻¹ * γ)⁻¹ ^ m *
                (∫ x, ‖sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x‖) +
              (w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m) * μ.real univ *
                ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
  obtain ⟨C₁, hC₁, hc₁⟩ := exists_remote_window_spectral_bound m L
  obtain ⟨C₂, hC₂, hc₂⟩ := exists_sourcePacketTailData_bound χ hχ m
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN j w γ hw hw₁ hNγ hγ₁ k y hy hremote r hr
  let f := sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k
  let a (θ : ℝ) : ℂ := angularSpectralWindow N (angularDirection (angularGridPoint N j)) θ
  have hN₀ : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN₁ : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hsupport (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ support f) :
      ‖y - x‖ ≤ L := by
    have hχx := (support_sourceWavePacket_subset μ hμ ψ hψ hzero χ hχ N hN hw j k hx).1
    have hxnorm := support_subset_sourceCutoffRadius χ hχ hχx
    rw [Metric.mem_closedBall, dist_zero_right] at hxnorm
    have htriangle := norm_sub_le y x
    linarith
  have hstrip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ support f) :
      |⟪angularDirection (angularGridPoint N j + Real.pi / 2), x⟫ - w * k| ≤ w :=
    (support_sourceWavePacket_subset μ hμ ψ hψ hzero χ hχ N hN hw j k hx).2.le
  have hmain := hc₁ N γ (angularGridPoint N j) (w * k) w hN₁ hNγ hγ₁ f.integrable
    y hsupport hstrip hremote r hr
  have hρone (ξ : EuclideanSpace ℝ (Fin 2)) (hξ : ξ ∈ sourcePacketCoreCone N j) :
      (angularSpectralSelector N (angularDirection (angularGridPoint N j)) ξ : ℂ) = 1 := by
    rw [angularSpectralSelector_eq_one hN₀ (show _ ≤ _ from hξ.le), Complex.ofReal_one]
  have hρbound (ξ : EuclideanSpace ℝ (Fin 2)) :
      ‖1 - (angularSpectralSelector N (angularDirection (angularGridPoint N j)) ξ : ℂ)‖ ≤
        1 := by
    have hs := angularSpectralSelector_mem_Icc (N : ℝ)
      (angularDirection (angularGridPoint N j)) ξ
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hs.2)]
    linarith [hs.1]
  have htail (θ : ℝ) : ‖(1 - a θ) * (𝓕 f) (r • angularDirection θ)‖ ≤
      (w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m) * μ.real univ *
        ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
    have h := norm_selected_sourcePacketTail_le N j
      (𝓕 f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
      (fun ξ ↦ (angularSpectralSelector N (angularDirection (angularGridPoint N j)) ξ : ℂ))
      hρone hρbound (r • angularDirection θ)
    rw [angularSpectralSelector_circle _ _ hr] at h
    apply h.trans
    simpa only [norm_smul, Real.norm_eq_abs, norm_angularDirection, mul_one, abs_of_pos hr]
      using hc₂ μ M hμ ψ hψ hzero N hN j w hw hw₁ k (r • angularDirection θ)
  have herr := norm_pinnedSpectralCircleAverage_sub_selected_le f
    (Complex.continuous_ofReal.comp (contDiff_angularSpectralWindow _ _).continuous)
    (norm_complex_angularSpectralWindow_le_one _ _) y r htail
  have htri := norm_add_le
    (selectedSpectralCircleAverage a f y r)
    (pinnedSpectralCircleAverage f y r - selectedSpectralCircleAverage a f y r)
  rw [add_sub_cancel] at htri
  exact htri.trans (add_le_add hmain herr)

/-- A bounded actual spatial packet cutoff contracts the full cap convolution's first norm. -/
theorem integral_norm_sourceWavePacket_le_kernel
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχnorm : ∀ x, |χ x| ≤ 1) (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ) :
    (∫ x, ‖sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x‖) ≤
      μ.real univ * ∫ x, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) x‖ := by
  let K := 𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)
  apply le_trans _ (integral_norm_schwartzMeasureDensity_le μ K)
  apply integral_mono
    (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k).integrable.norm
    (integrable_schwartzMeasureDensity μ K).norm
  intro x
  change ‖(smoothStripPacket χ w (sourceWavePacketNormal N j) k x : ℂ) *
    schwartzMeasureDensity μ K x‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [smoothStripPacket, abs_mul, abs_of_nonneg (smoothStripWeight_nonneg _ _ _)]
  exact mul_le_one₀ (hχnorm x) (smoothStripWeight_nonneg _ _ _)
    (smoothStripWeight_le_one _ _ _)

/-- Complete remote spectral packet bound in terms of the actual cap and inverse-cap norms.
No kernel localization or spectral support assumption on the spatially cut off packet occurs. -/
theorem exists_remote_sourceWavePacket_spectral_kernel_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχnorm : ∀ x, |χ x| ≤ 1) (m : ℕ) (L : ℝ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (j : ℕ) (w γ : ℝ),
        0 < w → w ≤ 1 → (N : ℝ)⁻¹ ≤ γ → γ ≤ 1 →
        ∀ (k : ℤ) (y : EuclideanSpace ℝ (Fin 2)),
          sourceCutoffRadius χ hχ + ‖y‖ ≤ L →
          γ + w + L * (16 * Real.pi / N) ≤
            |⟪sourceWavePacketNormal N j, y⟫ - w * k| →
          ∀ r : ℝ, 0 < r →
            ‖pinnedSpectralCircleAverage
              (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y r‖ ≤
              C₁ * (r * (N : ℝ)⁻¹ * γ)⁻¹ ^ m *
                (μ.real univ * ∫ x, ‖(𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) x‖) +
              (w * C₂ / (1 + w * r * (2 * Real.pi / N)) ^ m) * μ.real univ *
                ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hc⟩ :=
    exists_remote_sourceWavePacket_spectral_bound χ hχ m L
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN j w γ hw hw₁ hNγ hγ₁ k y hy hremote r hr
  apply (hc μ M hμ ψ hψ hzero N hN j w γ hw hw₁ hNγ hγ₁ k y hy hremote r hr).trans
  apply add_le_add_left
  have hγ : 0 < γ := lt_of_lt_of_le (by positivity : 0 < (N : ℝ)⁻¹) hNγ
  exact mul_le_mul_of_nonneg_left
    (integral_norm_sourceWavePacket_le_kernel μ hμ ψ hψ hzero χ hχ hχnorm N hN w j k)
    (by positivity)

end FalconerPacking
