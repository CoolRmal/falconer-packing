/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SmoothAngularCaps
public import FalconerPacking.CompactSourceSchwartz
public import FalconerPacking.PlanarStripPackets
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Constructed source wave packets and exact reconstruction

The angular caps, spatial strip weights, and finite index sets are actual constructions.
For any compact smooth source cutoff, their finite sum reconstructs its product with
the annular convolution exactly. Each individual packet is a genuine Schwartz function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Filter
open scoped ContDiff FourierTransform RealInnerProductSpace Topology

namespace FalconerPacking

/-- A support radius chosen from the compact support of the actual source cutoff. -/
def sourceCutoffRadius (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (hχ : HasCompactSupport χ) : ℝ :=
  hχ.isCompact.isBounded.exists_pos_norm_le.choose

theorem sourceCutoffRadius_pos (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (hχ : HasCompactSupport χ) : 0 < sourceCutoffRadius χ hχ :=
  hχ.isCompact.isBounded.exists_pos_norm_le.choose_spec.1

theorem support_subset_sourceCutoffRadius
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) :
    Function.support χ ⊆ closedBall 0 (sourceCutoffRadius χ hχ) := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  exact hχ.isCompact.isBounded.exists_pos_norm_le.choose_spec.2 x (subset_tsupport χ hx)

/-- The complete finite strip grid is determined by the cutoff and the width. -/
def sourceWavePacketIndices (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (hχ : HasCompactSupport χ) (w : ℝ) : Finset ℤ :=
  slopeNet ⌈sourceCutoffRadius χ hχ / w⌉₊

/-- The actual packet count is polynomial in inverse width. -/
theorem card_sourceWavePacketIndices_le
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {w : ℝ} (hw : 0 < w) :
    ((sourceWavePacketIndices χ hχ w).card : ℝ) ≤
      2 * sourceCutoffRadius χ hχ / w + 3 := by
  rw [sourceWavePacketIndices, card_slopeNet, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  have h := Nat.ceil_lt_add_one
    (div_nonneg (sourceCutoffRadius_pos χ hχ).le hw.le)
  rw [show 2 * sourceCutoffRadius χ hχ / w =
    2 * (sourceCutoffRadius χ hχ / w) by ring]
  linarith

/-- The canonical normal is perpendicular to the central direction of the angular cap. -/
def sourceWavePacketNormal (N j : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  angularDirection (angularGridPoint N j + Real.pi / 2)

@[simp]
theorem norm_sourceWavePacketNormal (N j : ℕ) : ‖sourceWavePacketNormal N j‖ = 1 :=
  norm_angularDirection _

theorem contDiff_complexStripPacket
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (k : ℤ) :
    ContDiff ℝ ∞ (fun x ↦ (smoothStripPacket χ w e k x : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_smoothStripPacket χ w e k)

theorem hasCompactSupport_complexStripPacket
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (w : ℝ) (e : EuclideanSpace ℝ (Fin 2)) (k : ℤ) :
    HasCompactSupport (fun x ↦ (smoothStripPacket χ w e k x : ℂ)) :=
  (hasCompactSupport_smoothStripPacket χ hχ w e k).comp_left
    (g := Complex.ofReal) (by simp)

/-- An actual source packet: a spatial strip cutoff times convolution with the inverse
Fourier transform of the explicitly constructed angular cap. -/
def sourceWavePacket
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  cutoffSchwartzMeasureConvolution μ hμ (𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j))
    (contDiff_complexStripPacket χ w (sourceWavePacketNormal N j) k)
    (hasCompactSupport_complexStripPacket χ hχ w (sourceWavePacketNormal N j) k)

@[simp]
theorem sourceWavePacket_apply
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x =
      (smoothStripPacket χ w (sourceWavePacketNormal N j) k x : ℂ) *
        ∫ y, (𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) (x - y) ∂μ := rfl

/-- Every translated Schwartz kernel is integrable against the finite source measure. -/
theorem integrable_schwartz_sub_finite_measure
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun y ↦ K (x - y)) μ := by
  apply Integrable.of_bound (K.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (SchwartzMap.seminorm ℝ 0 0 K)
  exact ae_of_all _ fun y ↦ SchwartzMap.norm_le_seminorm ℝ K (x - y)

/-- The automatically chosen strip family reconstructs the cutoff for every cap direction. -/
theorem sum_sourceWavePacket_spatial_cutoff
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {w : ℝ} (hw : 0 < w) (N j : ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    ∑ k ∈ sourceWavePacketIndices χ hχ w,
      smoothStripPacket χ w (sourceWavePacketNormal N j) k x = χ x := by
  apply sum_smoothStripPacket_eq χ (support_subset_sourceCutoffRadius χ hχ) hw
    (norm_sourceWavePacketNormal N j).le
  have h := Nat.le_ceil (sourceCutoffRadius χ hχ / w)
  exact (div_le_iff₀ hw).mp h |>.trans_eq (mul_comm _ _)

/-- Summation over physical strips exactly recovers the corresponding angular convolution. -/
theorem sum_sourceWavePacket_strips
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∑ k ∈ sourceWavePacketIndices χ hχ w,
      sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x =
      (χ x : ℂ) * ∫ y, (𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j)) (x - y) ∂μ := by
  simp only [sourceWavePacket_apply, ← Finset.sum_mul, ← Complex.ofReal_sum]
  rw [sum_sourceWavePacket_spatial_cutoff χ hχ hw]

/-- The inverse Fourier kernels form an exact finite partition of the original kernel. -/
theorem sum_inverseFourier_smoothAngularCap
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (N : ℕ) (hN : 0 < N) :
    ∑ j ∈ Finset.range N, 𝓕⁻ (smoothAngularCap ψ hψ hzero N hN j) = 𝓕⁻ ψ := by
  rw [← fourierInv_sum, sum_smoothAngularCap]

/-- Exact reconstruction of the localized annular source, with no assumed packet partition. -/
theorem sum_sourceWavePacket_eq
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ∑ j ∈ Finset.range N, ∑ k ∈ sourceWavePacketIndices χ hχ w,
      sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x =
      (χ x : ℂ) * ∫ y, (𝓕⁻ ψ) (x - y) ∂μ := by
  simp only [sum_sourceWavePacket_strips μ hμ ψ hψ hzero χ hχ N hN hw,
    ← Finset.mul_sum]
  congr 1
  rw [← integral_finsetSum _ (fun j _ ↦ integrable_schwartz_sub_finite_measure μ _ x)]
  apply integral_congr_ae
  exact ae_of_all _ fun y ↦ by
    simpa only [sum_apply] using congrArg
      (fun K : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ ↦ K (x - y))
      (sum_inverseFourier_smoothAngularCap ψ hψ hzero N hN)

/-- The actual source packet has the specified source and strip support. -/
theorem support_sourceWavePacket_subset
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w) (j : ℕ) (k : ℤ) :
    Function.support (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) ⊆
      Function.support χ ∩ {x | |⟪sourceWavePacketNormal N j, x⟫ - w * k| < w} := by
  intro x hx
  apply support_smoothStripPacket χ hw (sourceWavePacketNormal N j) k
  intro he
  exact hx (by simp only [sourceWavePacket_apply, he, Complex.ofReal_zero, zero_mul])

/-- Every actual packet is compactly supported within the original source cutoff. -/
theorem hasCompactSupport_sourceWavePacket
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ) :
    HasCompactSupport (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) := by
  apply hχ.mono
  intro x hx he
  exact hx (by simp only [sourceWavePacket_apply, smoothStripPacket, he, zero_mul,
    Complex.ofReal_zero])

/-- The constructed packets are integrable functions, not merely distributional pieces. -/
theorem integrable_sourceWavePacket
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ y ∂μ, ‖y‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (j : ℕ) (k : ℤ) :
    Integrable (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) :=
  (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k).integrable

end FalconerPacking
