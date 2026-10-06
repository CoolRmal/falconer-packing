/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SourcePacketMicrolocal
public import FalconerPacking.InitialSpectralReconstruction

/-!
# Radial Fourier leakage of actual retained source packets

Spatial cutoff destroys exact annular Fourier support. The convolution formula instead
gives an explicit rapidly decreasing envelope outside an enlarged original annulus.
The estimate is uniform in every choice of retained spatial packets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- An annulus with fixed radial margins separates every omitted frequency from every
original frequency, also at the two endpoints of the open enlarged annulus. -/
theorem norm_sub_ge_of_omitted_annulus {R U : ℝ} (hR : 0 < R)
    {ξ ζ : EuclideanSpace ℝ (Fin 2)} (hξ : 2 * R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ U)
    (hζ : ‖ζ‖ ∉ Ioo R (2 * U)) :
    (R + ‖ζ‖) / 4 ≤ ‖ζ - ξ‖ := by
  have hreverse₁ : ‖ξ‖ - ‖ζ‖ ≤ ‖ζ - ξ‖ := by
    simpa only [norm_sub_rev] using norm_sub_norm_le ξ ζ
  have hreverse₂ := norm_sub_norm_le ζ ξ
  by_cases hz : ‖ζ‖ ≤ R
  · linarith
  · have hz' : 2 * U ≤ ‖ζ‖ := le_of_not_gt fun h ↦ hζ ⟨lt_of_not_ge hz, h⟩
    linarith

/-- Each actual packet has rapid radial decay. All frame and spectral separation
hypotheses of the anisotropic convolution estimate are discharged here. -/
theorem exists_sourceWavePacket_radial_tail_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (j : ℕ) (w : ℝ),
        0 < w → w ≤ 1 → ∀ (k : ℤ) (R U : ℝ), 0 < R → R ≤ U →
        (∀ ξ ∈ Function.support ψ, 2 * R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ U) →
        ∀ ζ : EuclideanSpace ℝ (Fin 2), ‖ζ‖ ∉ Ioo R (2 * U) →
          ‖(𝓕 (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k)) ζ‖ ≤
            C * w * w⁻¹ ^ m * μ.real univ *
              (∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖) /
              (R + ‖ζ‖) ^ m := by
  obtain ⟨C, hC, hc⟩ := exists_sourceWavePacket_fourier_tail_bound χ hχ m
  refine ⟨C * 4 ^ m, by positivity, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN j w hw hw₁ k R U hR hRU hsupp ζ hζ
  let O := circleCapFrame (angularGridPoint N j + Real.pi)
  have hgeom : ∀ ξ ∈ Function.support (smoothAngularCap ψ hψ hzero N hN j),
      w * ((R + ‖ζ‖) / 4) ≤ ‖(WithLp.toLp 2 ![w * (O (ζ - ξ)) 0,
        (O (ζ - ξ)) 1] : EuclideanSpace ℝ (Fin 2))‖ := by
    intro ξ hξ
    exact (mul_le_mul_of_nonneg_left
      (norm_sub_ge_of_omitted_annulus hR
        (hsupp ξ (support_smoothAngularCap_subset ψ hψ hzero N hN j hξ)) hζ) hw.le).trans
      (mul_norm_le_anisotropic_strip_norm O hw.le hw₁ (ζ - ξ))
  have h := hc μ M hμ ψ hψ hzero N hN j O
    (sourceWavePacketNormal_eq_frame_zero N j) w hw hw₁ k ζ
      (w * ((R + ‖ζ‖) / 4)) (by positivity) hgeom
  have hp : 0 < R + ‖ζ‖ := by positivity
  have hden : w * C / (1 + w * ((R + ‖ζ‖) / 4)) ^ m ≤
      w * C / (w * ((R + ‖ζ‖) / 4)) ^ m := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) m
  apply h.trans
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hden ENNReal.toReal_nonneg)
    (integral_nonneg fun _ ↦ norm_nonneg _)).trans_eq
  rw [mul_pow, div_pow, inv_pow]
  simp only [Measure.real]
  field_simp

/-- Fourier linearity gives a uniform bound for any actual retained subset. A whole good
standard label and its complementary remote label never need to be counted together. -/
theorem norm_fourier_initialRetainedSource_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) (w : ℝ) (G : Finset ℕ) (remote : ℕ → Finset ℤ)
    (hG : G ⊆ Finset.range N)
    (hremote : ∀ j ∈ Finset.range N \ G, remote j ⊆ sourceWavePacketIndices χ hχ w)
    (ζ : EuclideanSpace ℝ (Fin 2)) {B : ℝ} (hB : 0 ≤ B)
    (hpacket : ∀ j ∈ Finset.range N, ∀ k ∈ sourceWavePacketIndices χ hχ w,
      ‖(𝓕 (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k)) ζ‖ ≤ B) :
    ‖(𝓕 (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote)) ζ‖ ≤
      N * ((sourceWavePacketIndices χ hχ w).card : ℝ) * B := by
  let I := sourceWavePacketIndices χ hχ w
  have hall (J : Finset ℕ) (hJ : J ⊆ Finset.range N) (I' : ℕ → Finset ℤ)
      (hI' : ∀ j ∈ J, I' j ⊆ I) :
      ‖(𝓕 (∑ j ∈ J, ∑ k ∈ I' j,
        sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k :
          SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)) ζ‖ ≤ J.card * I.card * B := by
    simp only [fourier_sum, sum_apply]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j ∈ J, ∑ k ∈ I' j, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦
          hpacket j (hJ hj) k (hI' j hj hk))
      _ ≤ ∑ j ∈ J, ∑ k ∈ I, B := by
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.sum_le_sum_of_subset_of_nonneg (hI' j hj) (fun _ _ _ ↦ hB)
      _ = _ := by simp; ring
  rw [initialRetainedSource, FourierTransform.fourier_add, add_apply]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hall G hG (fun _ ↦ I) (fun _ _ ↦ Finset.Subset.refl _))
    (hall (Finset.range N \ G) Finset.sdiff_subset remote hremote)).trans_eq
  have hcard := Finset.card_sdiff_add_card_eq_card hG
  simp only [Finset.card_range] at hcard
  have hcast : ((Finset.range N \ G).card : ℝ) + G.card = N := by exact_mod_cast hcard
  change (G.card : ℝ) * I.card * B + _ = N * I.card * B
  rw [← hcast]
  ring

/-- Arbitrary retained spatial subsets share one radial envelope. The spatial-grid count
cancels the width prefactor in the single-packet Fourier estimate. -/
theorem exists_initialRetainedSource_radial_tail_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (w : ℝ),
        0 < w → w ≤ 1 → ∀ (G : Finset ℕ) (remote : ℕ → Finset ℤ),
        G ⊆ Finset.range N →
        (∀ j ∈ Finset.range N \ G, remote j ⊆ sourceWavePacketIndices χ hχ w) →
        ∀ R U : ℝ, 0 < R → R ≤ U →
        (∀ ξ ∈ Function.support ψ, 2 * R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ U) →
        ∀ ζ : EuclideanSpace ℝ (Fin 2), ‖ζ‖ ∉ Ioo R (2 * U) →
          ‖(𝓕 (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote)) ζ‖ ≤
            C * N * w⁻¹ ^ m * μ.real univ * (∫ ξ, ‖ψ ξ‖) / (R + ‖ζ‖) ^ m := by
  obtain ⟨C, hC, hc⟩ := exists_sourceWavePacket_radial_tail_bound χ hχ m
  refine ⟨C * (2 * sourceCutoffRadius χ hχ + 3),
    mul_pos hC (by linarith [sourceCutoffRadius_pos χ hχ]), ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN w hw hw₁ G remote hG hremote R U hR hRU hsupp ζ hζ
  have hnorm : ∀ j ∈ Finset.range N,
      (∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖) ≤ ∫ ξ, ‖ψ ξ‖ := by
    intro j hj
    exact integral_mono (smoothAngularCap ψ hψ hzero N hN j).integrable.norm
      ψ.integrable.norm (norm_smoothAngularCap_le ψ hψ hzero N hN (Finset.mem_range.mp hj))
  have hp : 0 < R + ‖ζ‖ := by positivity
  let B := C * w * w⁻¹ ^ m * μ.real univ * (∫ ξ, ‖ψ ξ‖) / (R + ‖ζ‖) ^ m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs := norm_fourier_initialRetainedSource_le μ hμ ψ hψ hzero χ hχ N hN w
    G remote hG hremote ζ hB (fun j hj k _ ↦
      (hc μ M hμ ψ hψ hzero N hN j w hw hw₁ k R U hR hRU hsupp ζ hζ).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hnorm j hj) (by positivity)) (by positivity)))
  have hcount : ((sourceWavePacketIndices χ hχ w).card : ℝ) * w ≤
      2 * sourceCutoffRadius χ hχ + 3 := by
    have h := mul_le_mul_of_nonneg_right (card_sourceWavePacketIndices_le χ hχ hw) hw.le
    have he : (2 * sourceCutoffRadius χ hχ / w + 3) * w =
        2 * sourceCutoffRadius χ hχ + 3 * w := by field_simp
    rw [he] at h
    linarith
  apply hs.trans
  dsimp [B]
  calc
    _ = (((sourceWavePacketIndices χ hχ w).card : ℝ) * w) *
        (C * N * w⁻¹ ^ m * μ.real univ * (∫ ξ, ‖ψ ξ‖) / (R + ‖ζ‖) ^ m) := by ring
    _ ≤ (2 * sourceCutoffRadius χ hχ + 3) *
        (C * N * w⁻¹ ^ m * μ.real univ * (∫ ξ, ‖ψ ξ‖) / (R + ‖ζ‖) ^ m) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by ring

end FalconerPacking
