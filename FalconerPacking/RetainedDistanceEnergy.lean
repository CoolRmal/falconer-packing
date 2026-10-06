/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RetainedPinFamily
public import FalconerPacking.RetainedOmittedCircleEnergy
public import FalconerPacking.RetainedCircleIntegration

/-!
# Full distance energy of the actual retained source

The actual finite choice in each pin cube has a rapidly decaying omitted spectrum.
Combining this with a circle estimate on the main annulus gives the full joint distance
energy, without assuming compact Fourier support or discarding a range of distances.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

theorem retainedPinSource_eq_zero_or_packet_family
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (s t K : ℕ)
    (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (w : ℝ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y = 0 ∨
      ∃ (G : Finset ℕ) (remote : ℕ → Finset ℤ), G ⊆ Finset.range (2 ^ s) ∧
        (∀ j ∈ Finset.range (2 ^ s) \ G, remote j ⊆ sourceWavePacketIndices χ hχ w) ∧
        retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y =
          initialRetainedSource μ hμ ψ hψ hzero χ hχ (2 ^ s) (by positivity) w G remote := by
  by_cases hy : ∃ Q ∈ I, y ∈ dyadicCube (n 0) Q
  · obtain ⟨Q, hQ, hyQ⟩ := hy
    right
    refine ⟨(Finset.range (2 ^ s)).filter (standardPacketSurvives σ n e s t K L H 0 Q),
      fun j ↦ initialCellRemoteIndices χ hχ w (2 ^ s) j (dyadicCube (n 0) Q),
      Finset.filter_subset _ _, ?_, ?_⟩
    · intro j _
      exact initialCellRemoteIndices_subset χ hχ w (2 ^ s) j _
    · exact dyadicSchwartzFamily_of_mem _ hQ hyQ
  · left
    exact dyadicSchwartzFamily_of_notMem _ (by simpa only [not_exists, not_and] using hy)

/-- Every nonzero retained source point lies in the fixed cutoff support. -/
theorem retainedPinSource_distance_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (s t K : ℕ)
    (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (w : ℝ)
    (y x : EuclideanSpace ℝ (Fin 2))
    (hx : retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y x ≠ 0) :
    dist x y ≤ sourceCutoffRadius χ hχ + ‖y‖ := by
  have hc := support_retainedPinSource_subset μ hμ ψ hψ hzero χ hχ σ n e s t K L H I w y hx
  have hb := support_subset_sourceCutoffRadius χ hχ hc
  rw [Metric.mem_closedBall, dist_zero_right] at hb
  exact (dist_le_norm_add_norm x y).trans (add_le_add_left hb _)

/-- An actual retained family has arbitrarily rapid omitted radial energy, uniformly in
its finite pin partition and its inherited marks. -/
theorem exists_retainedPinSource_omitted_energy_rapid
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {J : ℕ} (hJ : 0 < J) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M) (k : ℕ),
        let ψ := 𝓕 (dyadicAnnularKernel (4 * J) k)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) k
        let w := (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * J)
        let R := (2 : ℝ) ^ (4 * J * k)
        let U := (2 : ℝ) ^ (4 * J + 2) * R
        ∀ (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
          (n e : ℕ → ℕ) (t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)),
          let f := retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e (6 + 2 * J * k) t K L H I w
          (∫⁻ r in Ioi (0 : ℝ) \ Ioo R (2 * U), ENNReal.ofReal r *
            ∫⁻ y, ENNReal.ofReal (‖pinnedSpectralCircleAverage (f y) y r‖ ^ 2) ∂ν) ≤
              ν univ * ENNReal.ofReal (C * (μ.real univ) ^ 2 / ((2 : ℝ) ^ k) ^ q) := by
  obtain ⟨C, hC, hc⟩ := exists_retained_omitted_circle_energy_rapid χ hχ hJ q
  refine ⟨C, hC, ?_⟩
  intro μ _ M hμ k
  dsimp only
  intro σ ν _ n e t K L H I
  apply hc μ M hμ k ν
  filter_upwards [] with y
  have hN : 64 * 2 ^ (2 * J * k) = 2 ^ (6 + 2 * J * k) := by
    rw [pow_add]
    norm_num
  simpa only [hN] using retainedPinSource_eq_zero_or_packet_family μ hμ _ _ _ χ hχ
    σ n e (6 + 2 * J * k) t K L H I _ y

/-- Main-annulus control of the actual retained circle family implies a full joint
distance bound. The omitted term is proved from the source packets, not postulated. -/
theorem exists_retainedPinDistance_energy_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    {J : ℕ} (hJ : 0 < J) (q : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {s C₀ : ℝ} (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C₀) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M) (k : ℕ),
        let ψ := 𝓕 (dyadicAnnularKernel (4 * J) k)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) k
        let w := (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * J)
        let R := (2 : ℝ) ^ (4 * J * k)
        let U := (2 : ℝ) ^ (4 * J + 2) * R
        ∀ (σ ν : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure ν]
          (n e : ℕ → ℕ) (t K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ))
          (B : ℝ), 0 ≤ B → (∀ᵐ y ∂ν, ‖y‖ ≤ B) →
          let f := retainedPinSource μ hμ ψ hψ hzero χ hχ σ n e (6 + 2 * J * k) t K L H I w
          ∀ A E : ℝ≥0∞,
            (∀ᵐ r ∂volume.restrict (Ioo R (2 * U)),
              (∫⁻ y, ‖pinnedSpectralCircleAverage (f y) y r‖ₑ ^ 2 ∂ν) ≤
                A * ENNReal.ofReal (1 / r) *
                  (∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
                    ∂radialAngularProbability) + E) →
            (∫⁻ p, ENNReal.ofReal (‖complexDistanceDensity (f p.1) p.1 p.2‖ ^ 2)
              ∂ν.prod volume) ≤
              ENNReal.ofReal ((sourceCutoffRadius χ hχ + B) * (2 * Real.pi) ^ 2) *
                (A * ENNReal.ofReal (1 / R) * (ENNReal.ofReal (2 * Real.pi))⁻¹ *
                  ENNReal.ofReal (C₁ * (2 * U) ^ (2 - s)) +
                  E * ENNReal.ofReal ((2 * U) ^ 2) +
                  ν univ * ENNReal.ofReal (C₂ / ((2 : ℝ) ^ k) ^ q)) := by
  obtain ⟨C₁, hC₁, hband⟩ := exists_circle_chain_band_frostman_bound μ hs hs₂ hfr
  obtain ⟨C₂, hC₂, htail⟩ := exists_retainedPinSource_omitted_energy_rapid χ hχ hJ q
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M hμ k
  dsimp only
  intro σ ν _ n e t K L H I B hB hball A E hcircle
  let f := retainedPinSource μ hμ (𝓕 (dyadicAnnularKernel (4 * J) k))
    (hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k)
    (fourier_dyadicAnnularKernel_eventually_zero (4 * J) k) χ hχ
    σ n e (6 + 2 * J * k) t K L H I
    ((2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * J))
  let R : ℝ := 2 ^ (4 * J * k)
  let U : ℝ := 2 ^ (4 * J + 2) * R
  have hR : 0 < R := by dsimp [R]; positivity
  have hRU : R ≤ 2 * U := by
    have hp : (1 : ℝ) ≤ 2 ^ (4 * J + 2) := one_le_pow₀ (by norm_num)
    dsimp only [U]
    nlinarith
  have hmain := hband (fun r ↦ ∫⁻ y, ‖pinnedSpectralCircleAverage (f y) y r‖ₑ ^ 2 ∂ν)
    hR hRU A E hcircle
  have ht := htail μ M hμ k σ ν n e t K L H I
  have hf := measurable_retainedPinSource μ hμ (𝓕 (dyadicAnnularKernel (4 * J) k))
    (hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k)
    (fourier_dyadicAnnularKernel_eventually_zero (4 * J) k) χ hχ
    σ n e (6 + 2 * J * k) t K L H I ((2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * J))
  apply lintegral_joint_distance_sq_le_of_annular_energy ν f hf
    (add_nonneg (sourceCutoffRadius_pos χ hχ).le hB) hR.le
  · filter_upwards [hball] with y hy
    intro x hx
    exact (retainedPinSource_distance_le μ hμ _ _ _ χ hχ σ n e _ t K L H I _ y x hx).trans
      (add_le_add_right hy _)
  · simpa only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using hmain
  · simpa only [Measure.real, measure_univ, ENNReal.toReal_one, one_pow, mul_one] using ht

end FalconerPacking
