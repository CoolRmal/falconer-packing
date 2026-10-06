/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.MarkedCircleInitialLocalization

/-!
# Initial pin energy summed over the actual dyadic cells

The normalized local main term is precisely the initial energy of the proved chain.
The global tail is bounded by the actual source circle energy; disjoint dyadic cells
cost only the total pin mass.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap
open scoped ENNReal Topology

namespace FalconerPacking

/-- Actual cells of one dyadic generation have total mass at most the mass of all pins. -/
theorem sum_measure_dyadicCube_le_univ
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n : ℕ) (I : Finset (Fin 2 → ℤ)) :
    ∑ Q ∈ I, σ (dyadicCube n Q) ≤ σ univ := by
  have hcount (x : EuclideanSpace ℝ (Fin 2)) :
      (I.filter (fun Q ↦ x ∈ dyadicCube n Q)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro Q hQ P hP
    exact (mem_dyadicCube_iff.mp (Finset.mem_filter.mp hQ).2).symm.trans
      (mem_dyadicCube_iff.mp (Finset.mem_filter.mp hP).2)
  simpa only [Nat.cast_one, one_mul] using sum_measure_le_mul_of_multiplicity σ I
    (dyadicCube n) MeasurableSet.univ (fun _ _ ↦ measurableSet_dyadicCube _ _)
    (fun _ _ ↦ subset_univ _) 1 hcount

/-- Initial pin localization has the chain's exact main energy and a source-spectrum tail. -/
theorem markedCircle_initial_pin_energy (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (s t : ℕ) (R r : ℝ), 1 ≤ R → 0 < r → r ≤ 2 * R →
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k),
        Function.support k ⊆ closedBall 0 1 →
      ∀ (n e : ℕ → ℕ) (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
        (K : ℕ) (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (I : Finset (Fin 2 → ℤ)) (L : ℝ), 2 ≤ L →
        let a := ((2 : ℝ) ^ n 0)⁻¹
        let f := markedDyadicCircle ψ hψ hzero s t r
          (integrable_circle_planarMeasureFourier μ r) k hk n e good 0 K
        let E := markedCircleLocalEnergy ψ hψ hzero s t r
          (integrable_circle_planarMeasureFourier μ r) k hk n e good K σ I L 0
        let B := ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
          ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
          ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2
            ∂radialAngularProbability
        (∑ Q ∈ I, ∑ α ∈ dyadicCapLabels s (e 0),
          ∫⁻ x in dyadicCube (n 0) Q, ‖f Q α x‖ₑ ^ 2 ∂σ) ≤
          (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
            ((ENNReal.ofReal ((4 * R) ^ 2) * 81 *
              ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
                SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) *
              ENNReal.ofReal (L ^ 2 * a) ^ 2) * E +
              ENNReal.ofReal ((4 * R) ^ 2 * C / (1 + 4 * R * (L ^ 2 * a / 2 - a)) ^ m) *
                σ univ * B) := by
  obtain ⟨C, hC, hloc⟩ := markedDyadicCircle_pin_cube_localization m
  refine ⟨C, hC, ?_⟩
  intro ψ hψ hzero s t R r hR hr hrR μ hμ k hk hkball n e good K σ hσ I L hL
  dsimp only
  let a := ((2 : ℝ) ^ n 0)⁻¹
  let U := enlargedGridSquare a (L ^ 2)
  let f := markedDyadicCircle ψ hψ hzero s t r
    (integrable_circle_planarMeasureFourier μ r) k hk n e good 0 K
  let B := ENNReal.ofReal (1 / r) * (∫⁻ x, ‖k x‖ₑ ^ 2) *
    ENNReal.ofReal ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ 2) *
    ∫⁻ θ, ‖planarMeasureFourier μ (r • angularDirection θ)‖ₑ ^ 2 ∂radialAngularProbability
  let D := ENNReal.ofReal ((4 * R) ^ 2) * 81 *
    ENNReal.ofReal (SchwartzMap.seminorm ℝ 0 0 unitReproducingKernel +
      SchwartzMap.seminorm ℝ 4 0 unitReproducingKernel) * ENNReal.ofReal (L ^ 2 * a) ^ 2
  let T := ENNReal.ofReal ((4 * R) ^ 2 * C / (1 + 4 * R * (L ^ 2 * a / 2 - a)) ^ m)
  have hp (Q : Fin 2 → ℤ) (α : ℕ ⊕ (ℕ × ℕ)) :=
    hloc ψ hψ hzero s t R r hR hr hrR (planarMeasureFourier μ)
      (integrable_circle_planarMeasureFourier μ r) k hk hkball n e good 0 K Q α σ
      (L ^ 2) (by nlinarith)
  have hsum := Finset.sum_le_sum (fun Q (_ : Q ∈ I) ↦
    Finset.sum_le_sum (fun α (_ : α ∈ dyadicCapLabels s (e 0)) ↦ hp Q α))
  have hglobal : (∑ Q ∈ I, σ (dyadicCube (n 0) Q) *
      ∑ α ∈ dyadicCapLabels s (e 0), ∫⁻ x, ‖f Q α x‖ₑ ^ 2) ≤ σ univ * B := by
    calc
      _ ≤ ∑ Q ∈ I, σ (dyadicCube (n 0) Q) * B := by
        apply Finset.sum_le_sum
        intro Q _
        apply mul_le_mul_right
        exact sum_markedDyadicCircle_energy_le ψ hψ hzero μ hr (by norm_num)
          k hk hkball s t n e good 0 K Q
      _ = (∑ Q ∈ I, σ (dyadicCube (n 0) Q)) * B := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_left (sum_measure_dyadicCube_le_univ σ (n 0) I) B
  apply hsum.trans
  have heq : markedCircleLocalEnergy ψ hψ hzero s t r
      (integrable_circle_planarMeasureFourier μ r) k hk n e good K σ I L 0 =
      ∑ Q ∈ I, ∑ α ∈ dyadicCapLabels s (e 0), σ (U Q) *
        ∫⁻ x, ‖f Q α x‖ₑ ^ 2 ∂((volume (U Q))⁻¹ • volume.restrict (U Q)) := by
    simp only [markedCircleLocalEnergy, dyadicChainCubes_zero, mul_zero, zero_add]
    rfl
  rw [heq]
  change (∑ Q ∈ I, ∑ α ∈ dyadicCapLabels s (e 0),
    (∫⁻ x, ‖unitReproducingKernel x‖ₑ) *
      (D * σ (U Q) * (∫⁻ x, ‖f Q α x‖ₑ ^ 2
        ∂((volume (U Q))⁻¹ • volume.restrict (U Q))) +
        T * σ (dyadicCube (n 0) Q) * ∫⁻ x, ‖f Q α x‖ₑ ^ 2)) ≤ _
  dsimp only [D, T]
  simp only [mul_assoc, ← Finset.mul_sum, Finset.sum_add_distrib]
  gcongr
  simpa only [B, mul_assoc] using hglobal

end FalconerPacking
