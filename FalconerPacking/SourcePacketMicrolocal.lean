/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SourcePacketFourierConvolution
import FalconerPacking.RadialAngleGeometry
import FalconerPacking.CircleCapScaledGeometry
import FalconerPacking.CircleSpectralSchwartz

/-!
# Exact angular cores and frequency-circle tails of source packets

The core is the actual packet Fourier transform restricted to a doubled angular cap.
The complementary tail is pointwise rapidly small on every frequency circle. Angular
restriction is measurable; the subsequent fixed circle convolution supplies smoothness.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- The anisotropic frequency norm dominates width times the Euclidean norm. -/
theorem mul_norm_le_anisotropic_strip_norm
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {w : ℝ} (hw : 0 ≤ w) (hw₁ : w ≤ 1) (x : EuclideanSpace ℝ (Fin 2)) :
    w * ‖x‖ ≤ ‖(WithLp.toLp 2 ![w * (O x) 0, (O x) 1] :
      EuclideanSpace ℝ (Fin 2))‖ := by
  have hx : ‖x‖ ^ 2 = (O x 0) ^ 2 + (O x 1) ^ 2 := by
    simpa only [O.norm_map, Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq (O x)
  have hy : ‖(WithLp.toLp 2 ![w * (O x) 0, (O x) 1] :
      EuclideanSpace ℝ (Fin 2))‖ ^ 2 = (w * O x 0) ^ 2 + (O x 1) ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have hw₂ : w ^ 2 ≤ 1 := by nlinarith
  have hsq := mul_le_mul_of_nonneg_right hw₂ (sq_nonneg (O x 1))
  nlinarith [norm_nonneg x, norm_nonneg
    (WithLp.toLp 2 ![w * (O x) 0, (O x) 1] : EuclideanSpace ℝ (Fin 2))]

/-- The doubled actual cap, defined without choosing a branch of the angle. -/
def sourcePacketCoreCone (N j : ℕ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {ξ | ‖NormedSpace.normalize ξ - angularDirection (angularGridPoint N j)‖ <
    8 * Real.pi / N}

theorem measurableSet_sourcePacketCoreCone (N j : ℕ) :
    MeasurableSet (sourcePacketCoreCone N j) := by
  unfold sourcePacketCoreCone NormedSpace.normalize
  exact measurableSet_lt (by fun_prop) measurable_const

/-- The exact spectral core of arbitrary actual packet data. -/
def sourcePacketCoreData (N j : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ := (sourcePacketCoreCone N j).indicator g

/-- The exact complementary spectral tail. -/
def sourcePacketTailData (N j : ℕ) (g : EuclideanSpace ℝ (Fin 2) → ℂ) :
    EuclideanSpace ℝ (Fin 2) → ℂ := (sourcePacketCoreCone N j)ᶜ.indicator g

theorem sourcePacketCoreData_add_tailData (N j : ℕ)
    (g : EuclideanSpace ℝ (Fin 2) → ℂ) (ξ : EuclideanSpace ℝ (Fin 2)) :
    sourcePacketCoreData N j g ξ + sourcePacketTailData N j g ξ = g ξ := by
  by_cases hξ : ξ ∈ sourcePacketCoreCone N j <;>
    simp [sourcePacketCoreData, sourcePacketTailData, hξ]

/-- Geometric separation of the discarded frequencies from every original cap frequency. -/
theorem sourcePacketCoreCone_compl_separation
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (N : ℕ) (hN : 0 < N) (j : ℕ)
    (O : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {w : ℝ} (hw : 0 ≤ w) (hw₁ : w ≤ 1)
    {ζ : EuclideanSpace ℝ (Fin 2)} (hζ : ζ ∉ sourcePacketCoreCone N j)
    {ξ : EuclideanSpace ℝ (Fin 2)}
    (hξ : ξ ∈ Function.support (smoothAngularCap ψ hψ hzero N hN j)) :
    w * ‖ζ‖ * (2 * Real.pi / N) ≤
      ‖(WithLp.toLp 2 ![w * (O (ζ - ξ)) 0, (O (ζ - ξ)) 1] :
        EuclideanSpace ℝ (Fin 2))‖ := by
  have hnear := smoothAngularCap_direction_support ψ hψ hzero N hN j hξ
  rw [mem_ball, dist_eq_norm] at hnear
  change ‖NormedSpace.normalize ξ - angularDirection (angularGridPoint N j)‖ <
    4 * Real.pi / N at hnear
  have hfar : 8 * Real.pi / N ≤
      ‖NormedSpace.normalize ζ - angularDirection (angularGridPoint N j)‖ :=
    le_of_not_gt hζ
  have htriangle := dist_triangle (NormedSpace.normalize ζ) (NormedSpace.normalize ξ)
    (angularDirection (angularGridPoint N j))
  simp only [dist_eq_norm] at htriangle
  have hgap : 4 * Real.pi / N ≤ ‖NormedSpace.normalize ζ - NormedSpace.normalize ξ‖ := by
    rw [show 8 * Real.pi / N = 2 * (4 * Real.pi / N) by ring] at hfar
    linarith
  have hξne : ξ ≠ 0 := by
    intro he
    have hψzero : ψ 0 = 0 := hzero.self_of_nhds
    have hψξ := support_smoothAngularCap_subset ψ hψ hzero N hN j hξ
    exact hψξ (he ▸ hψzero)
  have hnormalize := norm_normalize_sub_le hξne (v := ζ)
  have hdist : ‖ζ‖ * (2 * Real.pi / N) ≤ ‖ζ - ξ‖ := by
    have hm := mul_le_mul_of_nonneg_left hgap (norm_nonneg ζ)
    rw [show ‖ζ‖ * (4 * Real.pi / N) = 2 * (‖ζ‖ * (2 * Real.pi / N)) by ring] at hm
    nlinarith
  calc
    _ = w * (‖ζ‖ * (2 * Real.pi / N)) := by ring
    _ ≤ w * ‖ζ - ξ‖ := mul_le_mul_of_nonneg_left hdist hw
    _ ≤ _ := mul_norm_le_anisotropic_strip_norm O hw hw₁ (ζ - ξ)

/-- An explicit frame realizes the source packet's given normal; no frame choice is assumed. -/
theorem sourceWavePacketNormal_eq_frame_zero (N j : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    ⟪sourceWavePacketNormal N j, x⟫ = circleCapFrame (angularGridPoint N j + Real.pi) x 0 := by
  rw [circleCapFrame_zero_eq_inner, sourceWavePacketNormal]
  congr 2
  ring

/-- The discarded angular part of each actual packet has a uniform pointwise bound at
every frequency. Its decay parameter is the proved product `w * |ζ| / N`. -/
theorem exists_sourcePacketTailData_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (j : ℕ) (w : ℝ),
        0 < w → w ≤ 1 → ∀ (k : ℤ) (ζ : EuclideanSpace ℝ (Fin 2)),
          ‖sourcePacketTailData N j
            (𝓕 (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) :
              SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ζ‖ ≤
            (w * C / (1 + w * ‖ζ‖ * (2 * Real.pi / N)) ^ m) * μ.real univ *
              ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
  obtain ⟨C, hC, hc⟩ := exists_sourceWavePacket_fourier_tail_bound χ hχ m
  refine ⟨C, hC, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN j w hw hw₁ k ζ
  by_cases hζ : ζ ∈ sourcePacketCoreCone N j
  · simp only [sourcePacketTailData, indicator_of_notMem (notMem_compl_iff.mpr hζ), norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
      (integral_nonneg fun _ ↦ norm_nonneg _)
  · rw [sourcePacketTailData, indicator_of_mem hζ]
    exact hc μ M hμ ψ hψ hzero N hN j (circleCapFrame (angularGridPoint N j + Real.pi))
      (sourceWavePacketNormal_eq_frame_zero N j) w hw hw₁ k ζ _ (by positivity)
      (fun ξ hξ ↦ sourcePacketCoreCone_compl_separation ψ hψ hzero N hN j _ hw.le hw₁ hζ hξ)

/-- Every smooth selector which equals one on the proved core has tail dominated by the
hard complementary tail. This permits smooth core integration by parts without losing
the actual pointwise error bound. -/
theorem norm_selected_sourcePacketTail_le
    (N j : ℕ) (g ρ : EuclideanSpace ℝ (Fin 2) → ℂ)
    (hρ : ∀ ξ ∈ sourcePacketCoreCone N j, ρ ξ = 1)
    (hρbound : ∀ ξ, ‖1 - ρ ξ‖ ≤ 1) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ‖(1 - ρ ξ) * g ξ‖ ≤ ‖sourcePacketTailData N j g ξ‖ := by
  by_cases hξ : ξ ∈ sourcePacketCoreCone N j
  · simp [hρ ξ hξ, sourcePacketTailData, hξ]
  · rw [sourcePacketTailData, indicator_of_mem hξ, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hρbound ξ)

end FalconerPacking
