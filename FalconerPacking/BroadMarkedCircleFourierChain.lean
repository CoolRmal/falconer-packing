/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.MarkedCircleEnergyBounds
import FalconerPacking.BroadMarkedCircleChain

/-!
# The complete marked chain bounded by the actual source circle energy

Every terminal and global error energy is eliminated using the constructed cap
multipliers and actual enlarged-grid overlap. The remaining factors are explicit.
-/

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap
open scoped ENNReal Topology

namespace FalconerPacking

/-- Full finite inflation with all analytic energies bounded by the original source spectrum. -/
theorem markedCircle_finite_chain_source_energy_ratio (Bann : ℝ) (hBann : 0 < Bann) (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (s t : ℕ) (n e : ℕ → ℕ), Antitone n → Monotone e → e K ≤ t →
      ∀ (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
        (R r L : ℝ), 0 < R → R ≤ Bann * r → r ≤ 2 * R → 346 ≤ L →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k),
        Function.support k ⊆ closedBall 0 1 →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (I : Finset (Fin 2 → ℤ)) (H : ℕ → ℝ≥0∞),
        let a := fun j ↦ ((2 : ℝ) ^ n j)⁻¹
        let U := fun j ↦ enlargedGridSquare (a j) (L ^ (2 * j + 2))
        (∀ j < K, a (j + 1) ≤ R * (a j) ^ 2) →
        (∀ j < K, R * a j ≤ (2 : ℝ) ^ e (j + 1)) →
        (∀ j < K, (2 : ℝ) ^ e (j + 1) ≤ 2 * (R * a j)) →
        (∀ j < K, s < e (j + 1) → ((2 : ℝ) ^ s)⁻¹ ≤ a j / a (j + 1)) →
        (∀ j < K, ∀ Q ∈ dyadicChainCubes n I j,
          ∀ β ∈ dyadicCapLabels s (e (j + 1)), good j Q β →
          let P := ancestor (n j - n (j + 1)) Q
          σ (frameRectangle (dyadicCapPhysicalFrame s (e (j + 1)) β)
            (gridSquareCenter (a j) Q) (L ^ (4 * K + 20) * a j / 2)
            (L ^ (4 * K + 20) * a (j + 1) / 2) ∩ U (j + 1) P) ≤
            H j * ENNReal.ofReal (a j / a (j + 1)) * σ (U (j + 1) P)) →
        let E := markedCircleLocalEnergy ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r) k hk n e good K σ I L
        let B := ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
          ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
          ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
            ∂radialAngularProbability
        let A := fun j ↦ ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
        let ε := fun j ↦ ENNReal.ofReal C *
          ENNReal.ofReal (((a j) ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
          ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2)
        E 0 ≤ ((∏ j ∈ Finset.range K, A j) *
            ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) +
          ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * ε j) * σ univ * B := by
  obtain ⟨C, hC, hchain⟩ := markedCircle_finite_chain_ratio Bann hBann pwr K
  refine ⟨C, hC, ?_⟩
  intro ψ hψ hzero s t n e hn he het good R r L hR hrR hr₂ hL
    μ hμ k hk hkball σ hσ I H
  dsimp only
  intro hcurv hscale₀ hscale₁ hframe htest
  have hh := hchain ψ hψ hzero s t n e hn he het good R r L hR hrR hr₂ hL
    (planarMeasureFourier μ) (integrable_circle_planarMeasureFourier μ r) k hk hkball
    σ I H hcurv hscale₀ hscale₁ hframe htest
  have hr : 0 < r := circle_radius_pos_of_ratio hBann hR hrR
  have hL₁ : 1 ≤ L := by linarith
  have hterminal := markedCircleLocalEnergy_le_source ψ hψ hzero μ hr k hk hkball
    s t n e good K σ I hL₁ K
  have herror := markedCircleErrorEnergy_le_source ψ hψ hzero μ hr k hk hkball
    s t n e good K σ I hL₁
  apply hh.trans
  calc
    _ ≤ (∏ j ∈ Finset.range K, ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j) *
        (ENNReal.ofReal (49 * ((2 : ℝ) ^ n K) ^ 2) * σ univ *
          (ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
            ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
            ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
              ∂radialAngularProbability)) +
        ∑ j ∈ Finset.range K,
          (∏ i ∈ Finset.range j, ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * i + 14)) * H i) *
          (ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ n j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            (ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2) * σ univ *
              (ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
                ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
                ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
                  ∂radialAngularProbability))) := by
      apply add_le_add
      · exact mul_le_mul_right hterminal _
      · apply Finset.sum_le_sum
        intro j _
        gcongr
        exact mul_le_mul_right (herror (j + 1)) _
    _ = _ := by simp only [add_mul, Finset.sum_mul, mul_assoc]

end FalconerPacking
