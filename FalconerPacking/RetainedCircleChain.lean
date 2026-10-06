/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.InitialRetainedEnergy
public import FalconerPacking.BroadMarkedCircleFourierChain

/-!
# The actual retained packet energy after the complete spatial chain

The retained source is reconstructed from the original common spectrum, localized in
the pin cubes, and passed through the proved finite Fourier chain. The marks are the
actual physical rectangle tests, so their analytic tube hypothesis is discharged.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap FourierTransform
open scoped ENNReal Topology

namespace FalconerPacking

/-- Actual good-packet pin energy, with only the geometric chain inequalities remaining.
The three constants depend on the fixed parameters, never the scale, measures, or marks. -/
theorem exists_retainedCircle_chain_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) {J : ℕ} (hJ : 0 < J) (B : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (q m pwr K : ℕ) (Bann : ℝ) (hBann : 0 < Bann) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ ∃ k₀ : ℕ,
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M),
        (∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1) →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ],
        (∀ᵐ y ∂σ, ‖y‖ ≤ B) → ∀ k ≥ k₀,
        let s := 6 + 2 * J * k
        let N := 2 ^ s
        let hN : 0 < N := by dsimp only [N]; positivity
        let w := (2 : ℝ) ^ k / ((2 : ℝ) ^ k) ^ (2 * J)
        let ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ := 𝓕 (dyadicAnnularKernel (4 * J) k)
        let hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k
        let hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) k
        ∀ (n e : ℕ → ℕ), Antitone n → Monotone e → e 0 = 0 →
        ∀ t : ℕ, e K ≤ t → ∀ L : ℝ, 346 ≤ L →
        ∀ (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (R r : ℝ),
          1 ≤ R → (2 : ℝ) ^ (4 * J * k) ≤ r → R ≤ Bann * r → r ≤ 2 * R →
        let a := fun j ↦ ((2 : ℝ) ^ n j)⁻¹
        (∀ j < K, a (j + 1) ≤ R * (a j) ^ 2) →
        (∀ j < K, R * a j ≤ (2 : ℝ) ^ e (j + 1)) →
        (∀ j < K, (2 : ℝ) ^ e (j + 1) ≤ 2 * (R * a j)) →
        (∀ j < K, s < e (j + 1) → ((2 : ℝ) ^ s)⁻¹ ≤ a j / a (j + 1)) →
        let G := fun Q ↦ (Finset.range N).filter (standardPacketSurvives σ n e s t K L H 0 Q)
        let f := fun Q ↦ initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w (G Q)
          (fun j ↦ initialCellRemoteIndices χ hχ w N j (dyadicCube (n 0) Q))
        let E := ENNReal.ofReal (1 / r) * (∫⁻ x, ‖initialCircleMultiplierRadius B x‖ₑ ^ 2) *
          ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
          ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
            ∂radialAngularProbability
        let A := fun j ↦ ENNReal.ofReal C₃ * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
        let err := fun j ↦ ENNReal.ofReal C₃ *
          ENNReal.ofReal (((a j) ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
          ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2)
        let D := ENNReal.ofReal ((4 * R) ^ 2) * 81 *
          ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
            SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
          ENNReal.ofReal (L ^ 2 * a 0) ^ 2
        let T := ENNReal.ofReal ((4 * R) ^ 2 * C₂ /
          (1 + 4 * R * (L ^ 2 * a 0 / 2 - a 0)) ^ m)
        (∑ Q ∈ I, ∫⁻ y in dyadicCube (n 0) Q,
          ‖pinnedSpectralCircleAverage (f Q) y r‖ₑ ^ 2 ∂σ) ≤
          2 * (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
            (D * (((∏ j ∈ Finset.range K, A j) *
                ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
              ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * err j) * σ univ * E) +
              T * σ univ * E) +
          2 * ENNReal.ofReal (C₁ * μ.real univ / ((2 : ℝ) ^ k) ^ q) ^ 2 * σ univ := by
  obtain ⟨C₁, hC₁, k₀, hretain⟩ :=
    exists_dyadic_initial_retained_pin_energy χ hχ hχone hJ B hδ q
  obtain ⟨C₂, hC₂, hloc⟩ := markedCircle_initial_pin_energy m
  obtain ⟨C₃, hC₃, hchain⟩ :=
    markedCircle_finite_chain_source_energy_ratio Bann hBann pwr K
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, k₀, ?_⟩
  intro μ hμfin M hμ hnear σ hσfin hball k hk
  dsimp only
  intro n e hn he he₀ t het L hL H I R r hR hr₀ hr₁ hr₂ hcurv hscale₀ hscale₁ hframe
  have hr : 0 < r := (by positivity : 0 < (2 : ℝ) ^ (4 * J * k)).trans_le hr₀
  let ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ := 𝓕 (dyadicAnnularKernel (4 * J) k)
  have hψ := hasCompactSupport_fourier_dyadicAnnularKernel (4 * J) k
  have hzero := fourier_dyadicAnnularKernel_eventually_zero (4 * J) k
  let s := 6 + 2 * J * k
  have hret := hretain μ M hμ hnear σ hball k hk n e he₀ t K L H I r hr₀
  have hinit := hloc ψ hψ hzero s t R r hR hr hr₂ μ
    (initialCircleMultiplierRadius B) (hasCompactSupport_initialCircleMultiplierRadius B)
    (support_initialCircleMultiplierRadius B) n e (physicalDyadicGood σ n e s K L H)
    K σ I L (by linarith)
  have hseq := hchain ψ hψ hzero s t n e hn he het (physicalDyadicGood σ n e s K L H)
    R r L (by linarith) hr₁ hr₂ hL μ
    (initialCircleMultiplierRadius B) (hasCompactSupport_initialCircleMultiplierRadius B)
    (support_initialCircleMultiplierRadius B) σ I H hcurv hscale₀ hscale₁ hframe
    (by
      intro j _ Q _ β _ hgood
      exact hgood)
  apply hret.trans
  have hh := add_le_add_left (mul_le_mul_right hinit 2)
    (2 * ENNReal.ofReal (C₁ * μ.real univ / ((2 : ℝ) ^ k) ^ q) ^ 2 * σ univ)
  apply hh.trans
  dsimp only [ψ, s] at hseq ⊢
  simp only [mul_assoc] at hseq ⊢
  gcongr

end FalconerPacking
