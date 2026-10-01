/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.MarkedStandardReconstruction
import FalconerPacking.InitialCircleMultiplierRadius
import FalconerPacking.MarkedCircleInitialSum

/-!
# From actual retained packets to the initial marked pin energy

The fixed multiplier is bounded below on the pin ball. The actual reconstruction error
can therefore be added in square norm before applying the initial circle localization.
At angular depth zero there is exactly one label, so no angular cardinality is lost.
-/

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap FourierTransform
open scoped ENNReal Topology

namespace FalconerPacking

private theorem enorm_sq_le_cutoff_sq_add_error {B : ℝ} {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ ≤ B) (z v : ℂ) {ε : ℝ} (hε : 0 ≤ ε) (herr : ‖z - v‖ ≤ ε) :
    ‖z‖ₑ ^ 2 ≤ 2 * ‖(𝓕⁻ (initialCircleMultiplierRadius B)) x * v‖ₑ ^ 2 +
      2 * ENNReal.ofReal ε ^ 2 := by
  have hm : ‖v‖ ≤ ‖(𝓕⁻ (initialCircleMultiplierRadius B)) x * v‖ := by
    rw [norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg v)
      (one_le_norm_fourierInv_initialCircleMultiplierRadius hx)
  have hz : ‖z‖ ≤ ‖(𝓕⁻ (initialCircleMultiplierRadius B)) x * v‖ + ε := by
    have ht := norm_add_le (z - v) v
    rw [sub_add_cancel] at ht
    linarith
  have hs : ‖z‖ ^ 2 ≤ 2 * ‖(𝓕⁻ (initialCircleMultiplierRadius B)) x * v‖ ^ 2 + 2 * ε ^ 2 := by
    have hn := norm_nonneg z
    have hv := norm_nonneg ((𝓕⁻ (initialCircleMultiplierRadius B)) x * v)
    nlinarith [sq_nonneg (‖(𝓕⁻ (initialCircleMultiplierRadius B)) x * v‖ - ε)]
  have he := ENNReal.ofReal_le_ofReal hs
  rw [ENNReal.ofReal_add (by positivity) (by positivity)] at he
  simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_pow hε] using he

/-- Exact transfer of a cellwise reconstruction error to the actual initial marked energy.
The error will be supplied by the proved remote-packet estimate. -/
theorem initialRetainedSource_pin_energy_le_marked
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
    (B : ℝ) (hball : ∀ᵐ y ∂σ, ‖y‖ ≤ B)
    (n e : ℕ → ℕ) (he : e 0 = 0) (s t K : ℕ) (L : ℝ)
    (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (w r : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    let N := 2 ^ s
    let hN : 0 < N := by dsimp only [N]; positivity
    let G := fun Q ↦ (Finset.range N).filter (standardPacketSurvives σ n e s t K L H 0 Q)
    let f := fun Q ↦ initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w (G Q)
      (fun j ↦ initialCellRemoteIndices χ hχ w N j (dyadicCube (n 0) Q))
    (∀ Q ∈ I, ∀ y ∈ dyadicCube (n 0) Q, ‖y‖ ≤ B →
      ‖pinnedSpectralCircleAverage (f Q) y r -
        circleSpectralExtension r (initialCommonSourceSpectrum μ ψ hψ hzero N hN (G Q)) y‖
          ≤ ε) →
    (∑ Q ∈ I, ∫⁻ y in dyadicCube (n 0) Q, ‖pinnedSpectralCircleAverage (f Q) y r‖ₑ ^ 2 ∂σ) ≤
      2 * (∑ Q ∈ I, ∑ α ∈ dyadicCapLabels s (e 0), ∫⁻ y in dyadicCube (n 0) Q,
        ‖markedDyadicCircle ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
          (initialCircleMultiplierRadius B) (hasCompactSupport_initialCircleMultiplierRadius B) n e
          (physicalDyadicGood σ n e s K L H) 0 K Q α y‖ₑ ^ 2 ∂σ) +
      2 * ENNReal.ofReal ε ^ 2 * σ univ := by
  dsimp only
  intro herr
  let F := fun Q ↦ markedDyadicCircle ψ hψ hzero s t r
    (integrable_circle_planarMeasureFourier μ r) (initialCircleMultiplierRadius B)
    (hasCompactSupport_initialCircleMultiplierRadius B) n e (physicalDyadicGood σ n e s K L H)
    0 K Q (Sum.inl 0)
  have hcell (Q : Fin 2 → ℤ) (hQ : Q ∈ I) :
      (∫⁻ y in dyadicCube (n 0) Q,
        ‖pinnedSpectralCircleAverage
          (initialRetainedSource μ hμ ψ hψ hzero χ hχ (2 ^ s) (by positivity) w
            ((Finset.range (2 ^ s)).filter (standardPacketSurvives σ n e s t K L H 0 Q))
            (fun j ↦ initialCellRemoteIndices χ hχ w (2 ^ s) j (dyadicCube (n 0) Q)))
          y r‖ₑ ^ 2 ∂σ) ≤
      2 * (∫⁻ y in dyadicCube (n 0) Q, ‖F Q y‖ₑ ^ 2 ∂σ) +
        2 * ENNReal.ofReal ε ^ 2 * σ (dyadicCube (n 0) Q) := by
    calc
      _ ≤ ∫⁻ y in dyadicCube (n 0) Q, 2 * ‖F Q y‖ₑ ^ 2 +
          2 * ENNReal.ofReal ε ^ 2 ∂σ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_of_ae hball,
          ae_restrict_mem (measurableSet_dyadicCube (n 0) Q)] with y hy hyQ
        have hh := enorm_sq_le_cutoff_sq_add_error hy _ _ hε (herr Q hQ y hyQ hy)
        simpa only [F, markedDyadicCircle_initial_common_spectrum ψ hψ hzero μ
          s t r (initialCircleMultiplierRadius B) (hasCompactSupport_initialCircleMultiplierRadius B)
          σ n e he K L H Q y] using hh
      _ = _ := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul _ ((F Q).continuous.measurable.enorm.pow_const 2)]
        simp only [lintegral_const, Measure.restrict_apply_univ]
  have hs := Finset.sum_le_sum (fun Q hQ ↦ hcell Q hQ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hs
  have hm := sum_measure_dyadicCube_le_univ σ (n 0) I
  apply hs.trans
  have hlabels (Q : Fin 2 → ℤ) :
      (∑ α ∈ dyadicCapLabels s (e 0), ∫⁻ y in dyadicCube (n 0) Q,
        ‖markedDyadicCircle ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
          (initialCircleMultiplierRadius B) (hasCompactSupport_initialCircleMultiplierRadius B) n e
          (physicalDyadicGood σ n e s K L H) 0 K Q α y‖ₑ ^ 2 ∂σ) =
      ∫⁻ y in dyadicCube (n 0) Q, ‖F Q y‖ₑ ^ 2 ∂σ := by
    rw [he, sum_dyadicCapLabels_coarse (Nat.zero_le s)]
    simp only [pow_zero, Finset.sum_range_one, F]
  simp_rw [hlabels]
  rw [mul_assoc]
  exact add_le_add_right (mul_le_mul_right (mul_le_mul_right hm _) _) _

/-- The actual dyadic retained packets have initial marked energy plus an arbitrarily rapid
square error. Every reconstruction hypothesis is discharged by the constructed packets. -/
theorem exists_dyadic_initial_retained_pin_energy
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1) {J : ℕ} (hJ : 0 < J) (B : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ,
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
        ∀ (n e : ℕ → ℕ), e 0 = 0 → ∀ (t K : ℕ) (L : ℝ)
          (H : ℕ → ℝ≥0∞) (I : Finset (Fin 2 → ℤ)) (r : ℝ), (2 : ℝ) ^ (4 * J * k) ≤ r →
        let G := fun Q ↦ (Finset.range N).filter (standardPacketSurvives σ n e s t K L H 0 Q)
        let f := fun Q ↦ initialRetainedSource μ hμ ψ hψ hzero χ hχ N hN w (G Q)
          (fun j ↦ initialCellRemoteIndices χ hχ w N j (dyadicCube (n 0) Q))
        (∑ Q ∈ I, ∫⁻ y in dyadicCube (n 0) Q,
          ‖pinnedSpectralCircleAverage (f Q) y r‖ₑ ^ 2 ∂σ) ≤
          2 * (∑ Q ∈ I, ∑ α ∈ dyadicCapLabels s (e 0), ∫⁻ y in dyadicCube (n 0) Q,
            ‖markedDyadicCircle ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
              (initialCircleMultiplierRadius B) (hasCompactSupport_initialCircleMultiplierRadius B)
              n e (physicalDyadicGood σ n e s K L H) 0 K Q α y‖ₑ ^ 2 ∂σ) +
          2 * ENNReal.ofReal (C * μ.real univ / ((2 : ℝ) ^ k) ^ q) ^ 2 * σ univ := by
  obtain ⟨C, hC, k₀, hrapid⟩ := exists_initial_cell_reconstruction_rapid χ hχ hχone hJ
    (sourceCutoffRadius χ hχ + B) hδ q
  refine ⟨C, hC, k₀, ?_⟩
  intro μ hμfin M hμ hnear σ hσfin hball k hk
  dsimp only
  intro n e he t K L H I r hr
  apply initialRetainedSource_pin_energy_le_marked μ hμ _ _ _ χ hχ σ B hball n e he
    (6 + 2 * J * k) t K L H I _ r (by positivity)
  intro Q _ y hy hyB
  have hN : 2 ^ (6 + 2 * J * k) = 64 * 2 ^ (2 * J * k) := by
    rw [pow_add]
    norm_num
  have hh := hrapid μ M hμ hnear k hk
    ((Finset.range (2 ^ (6 + 2 * J * k))).filter
      (standardPacketSurvives σ n e (6 + 2 * J * k) t K L H 0 Q))
    (by simpa only [← hN] using (Finset.filter_subset
      (standardPacketSurvives σ n e (6 + 2 * J * k) t K L H 0 Q)
      (Finset.range (2 ^ (6 + 2 * J * k)))))
    (dyadicCube (n 0) Q) y hy (by linarith) r hr
  unfold initialCommonSourceSpectrum at hh ⊢
  simpa only [← hN] using hh

end FalconerPacking
