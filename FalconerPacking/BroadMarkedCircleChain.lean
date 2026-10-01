/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.BroadMarkedCircleEdge
import FalconerPacking.MarkedCircleChain
import FalconerPacking.DyadicChainCubes
import FalconerPacking.FiniteEnergyIterationENNReal

/-!
# Finite inflation over a fixed broad frequency annulus

The complete finite chain is derived from the proved marked spatial edge. Angular
crossings and spatial fibers are exact; the error retains every preceding threshold
factor. The physical tube tests and numerical scale conditions are explicit hypotheses.
-/

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap
open scoped ENNReal Topology

namespace FalconerPacking

/-- The actual finite-chain estimate, with no assumed spectral or reconstruction identities. -/
theorem markedCircle_finite_chain_ratio (Bann : ℝ) (hBann : 0 < Bann) (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (s t : ℕ) (n e : ℕ → ℕ), Antitone n → Monotone e → e K ≤ t →
      ∀ (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
        (R r L : ℝ), 0 < R → R ≤ Bann * r → r ≤ 2 * R → 346 ≤ L →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → ℂ)
        (hg : Integrable g (normalizedCircleMeasure r))
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
        let E := markedCircleLocalEnergy ψ hψ hzero s t r hg k hk n e good K σ I L
        let G := markedCircleErrorEnergy ψ hψ hzero s t r hg k hk n e good K σ I L
        let A := fun j ↦ ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
        let ε := fun j ↦ ENNReal.ofReal C *
          ENNReal.ofReal (((a j) ^ 2)⁻¹ * (L ^ pwr)⁻¹) * G (j + 1)
        E 0 ≤ (∏ j ∈ Finset.range K, A j) * E K +
          ∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) * ε j := by
  obtain ⟨C, hC, hedge⟩ := selected_markedDyadicCircle_parent_embedding_ratio Bann hBann pwr K
  refine ⟨C, hC, ?_⟩
  intro ψ hψ hzero s t n e hn he het good R r L hR hrR hr₂ hL
    g hg k hk hkball σ hσ I H
  dsimp only
  intro hcurv hscale₀ hscale₁ hframe htest
  apply finite_energy_iteration_ennreal
  intro j hj
  let a := fun j ↦ ((2 : ℝ) ^ n j)⁻¹
  let U := fun j ↦ enlargedGridSquare (a j) (L ^ (2 * j + 2))
  let f := markedDyadicCircle ψ hψ hzero s t r hg k hk n e good
  let child := fun P ↦ (dyadicChainCubes n I j).filter
    (fun Q ↦ ancestor (n j - n (j + 1)) Q = P)
  have hp (P : Fin 2 → ℤ) := hedge ψ hψ hzero s t n e hn he good j hj
    ((he (Nat.succ_le_of_lt hj)).trans het) R r L hR hrR hr₂ hL g hg k hk hkball σ
    (child P) P (fun Q hQ ↦ (Finset.mem_filter.mp hQ).2)
    (hcurv j hj) (hscale₀ j hj) (hscale₁ j hj) (hframe j hj) (H j)
    (fun Q hQ β hβ hgood ↦ by
      have h := htest j hj Q (Finset.mem_filter.mp hQ).1 β hβ hgood
      simpa only [(Finset.mem_filter.mp hQ).2] using h)
  have hsum := Finset.sum_le_sum (fun P (_ : P ∈ dyadicChainCubes n I (j + 1)) ↦ hp P)
  have hleft :
      (∑ P ∈ dyadicChainCubes n I (j + 1), ∑ Q ∈ child P,
        ∑ α ∈ dyadicCapLabels s (e j), σ (U j Q) *
          ∫⁻ x, ‖f j K Q α x‖ₑ ^ 2 ∂((volume (U j Q))⁻¹ • volume.restrict (U j Q))) =
        markedCircleLocalEnergy ψ hψ hzero s t r hg k hk n e good K σ I L j := by
    exact sum_dyadicChainCubes_fibers hn I j _
  change _ ≤ _ at hsum
  rw [hleft] at hsum
  apply hsum.trans_eq
  dsimp only [markedCircleLocalEnergy, markedCircleErrorEnergy]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib, mul_assoc]

end FalconerPacking
