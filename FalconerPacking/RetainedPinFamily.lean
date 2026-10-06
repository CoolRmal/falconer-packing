/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.DyadicSchwartzFamily
public import FalconerPacking.JointPinnedCircleEnergy

/-!
# The measurable retained source and its actual pinned distance density

The pin's initial dyadic cell selects a finite sum of the constructed source packets.
The resulting family is jointly measurable, retains the fixed source support, and has
exactly the cellwise spectral energy already bounded by the Fourier chain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

variable (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
  {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
  (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
  (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
  (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
  (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (s t K : ℕ)
  (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (w : ℝ)

/-- The actual retained source assigned by the initial pin cube. -/
def retainedPinSource (y : EuclideanSpace ℝ (Fin 2)) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  dyadicSchwartzFamily (n 0) I (fun Q ↦
    initialRetainedSource μ hμ ψ hψ hzero χ hχ (2 ^ s) (by positivity) w
      ((Finset.range (2 ^ s)).filter (standardPacketSurvives σ n e s t K L H 0 Q))
      (fun j ↦ initialCellRemoteIndices χ hχ w (2 ^ s) j (dyadicCube (n 0) Q))) y

theorem measurable_retainedPinSource :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
      retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w p.1 p.2) :=
  measurable_dyadicSchwartzFamily _ _ _

theorem measurable_retainedPinDistanceDensity :
    Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ ↦
      complexDistanceDensity
        (retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w p.1) p.1 p.2) :=
  measurable_family_complexDistanceDensity
    (f := fun y x ↦ retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y x)
    (measurable_retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w)

/-- The literal source support is unchanged by arbitrary whole-packet retention. -/
theorem support_initialRetainedSource_subset (N : ℕ) (hN : 0 < N)
    (G : Finset ℕ) (remote : ℕ → Finset ℤ) :
    Function.support (initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w G remote) ⊆
      Function.support χ := by
  intro x hx
  by_contra hχx
  have hc : χ x = 0 := by simpa only [Function.mem_support, not_not] using hχx
  have hz (j : ℕ) (k : ℤ) : sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k x = 0 := by
    simp only [sourceWavePacket_apply, smoothStripPacket, hc, zero_mul, Complex.ofReal_zero]
  exact hx (by simp only [initialRetainedSource, add_apply, sum_apply, hz,
    Finset.sum_const_zero, add_zero])

theorem support_retainedPinSource_subset (y : EuclideanSpace ℝ (Fin 2)) :
    Function.support (retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y) ⊆
      Function.support χ := by
  apply support_dyadicSchwartzFamily_subset
  intro Q _
  exact support_initialRetainedSource_subset μ hμ ψ hψ hzero χ hχ w _ _ _ _

/-- The actual global retained spectral energy is exactly the sum over initial pin cubes. -/
theorem lintegral_retainedPinSource_spectral (ν : Measure (EuclideanSpace ℝ (Fin 2))) (r : ℝ) :
    (∫⁻ y, ‖pinnedSpectralCircleAverage
      (retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y) y r‖ₑ ^ 2 ∂ν) =
      ∑ Q ∈ I, ∫⁻ y in dyadicCube (n 0) Q,
        ‖pinnedSpectralCircleAverage
          (initialRetainedSource μ hμ ψ hψ hzero χ hχ (2 ^ s) (by positivity) w
            ((Finset.range (2 ^ s)).filter (standardPacketSurvives σ n e s t K L H 0 Q))
            (fun j ↦ initialCellRemoteIndices χ hχ w (2 ^ s) j (dyadicCube (n 0) Q)))
          y r‖ₑ ^ 2 ∂ν := by
  unfold retainedPinSource
  apply lintegral_dyadicSchwartzFamily ν (n 0) I _
    (fun f y ↦ ‖pinnedSpectralCircleAverage f y r‖ₑ ^ 2)
  · intro y
    change ‖pinnedSpectralCircleAverage (0 : EuclideanSpace ℝ (Fin 2) → ℂ) y r‖ₑ ^ 2 = 0
    simp [pinnedSpectralCircleAverage, Real.fourier_eq]
  · intro Q _
    let F := initialRetainedSource μ hμ ψ hψ hzero χ hχ (2 ^ s) (by positivity) w
        ((Finset.range (2 ^ s)).filter (standardPacketSurvives σ n e s t K L H 0 Q))
        (fun j ↦ initialCellRemoteIndices χ hχ w (2 ^ s) j (dyadicCube (n 0) Q))
    have hf : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) ↦
        F p.2) := F.continuous.measurable.comp measurable_snd
    have hh := measurable_family_pinnedSpectralCircleAverage (f := fun _ x ↦ F x) hf
    exact ((hh.comp (measurable_id.prodMk measurable_const)).enorm.pow_const 2)

end FalconerPacking
