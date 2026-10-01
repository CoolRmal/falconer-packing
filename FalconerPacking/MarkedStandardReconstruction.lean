/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InitialPacketDecomposition
import FalconerPacking.DyadicCircleIdentification
import FalconerPacking.CircleCellTerminal

/-!
# Initial marked circle functions and the common standard spectrum

Physical marks depend only on whole standard labels. Summing the actual terminal fine
cells therefore recovers precisely those standard caps, with no nominal-support loss.
At initial angular depth zero the entire marked spectrum has one initial label.
-/

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)

/-- A whole-standard survival decision commutes with summation of all actual fine cells. -/
theorem inheritedCoarseCapCircle_standard_keep (S : ℕ) (hS : 0 < S) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    {T : ℕ} (hT : 0 < T) (P : ℕ → Prop) :
    inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk S T (fun p ↦ P p.1) 0 =
      ∑ j ∈ (Finset.range S).filter P,
        standardCapCircleSchwartz ψ hψ hzero S hS r hg k hk j := by
  let J := ((Finset.range S).filter P) ×ˢ Finset.range T
  have hsub : (fineCapLabels S T).filter (fun p ↦ p.1 / S = 0 ∧ P p.1) ⊆ J := by
    intro p hp
    obtain ⟨hp, _, hP⟩ := Finset.mem_filter.mp hp
    have hi := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hi.1, hP⟩, hi.2⟩
  unfold inheritedCoarseCapCircle inheritedLabelSum
  dsimp only
  have he : (∑ p ∈ (fineCapLabels S T).filter (fun p ↦ p.1 / S = 0 ∧ P p.1),
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk T p :
        SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) =
      ∑ p ∈ J, fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk T p := by
    apply Finset.sum_subset hsub
    intro p hp hnot
    have hi := Finset.mem_product.mp hp
    have hj := Finset.mem_range.mp (Finset.mem_filter.mp hi.1).1
    apply fineCapCircleSchwartz_eq_zero_of_notMem ψ hψ hzero S hS r hg k hk
      hj (Finset.mem_range.mp hi.2)
    intro hmem
    exact hnot (Finset.mem_filter.mpr ⟨hmem, Nat.div_eq_of_lt hj,
      (Finset.mem_filter.mp hi.1).2⟩)
  have ht : (∑ p ∈ J, fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk T p :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) =
      ∑ j ∈ (Finset.range S).filter P,
        standardCapCircleSchwartz ψ hψ hzero S hS r hg k hk j := by
    dsimp only [J]
    rw [Finset.sum_product]
    simp only [sum_fineCapCircleSchwartz_standard ψ hψ hzero S hS r hg k hk hT]
  convert he.trans ht using 2
  ext p
  simp only [Finset.mem_filter]

/-- At depth zero the marked physical function is the exact sum of surviving whole caps. -/
theorem markedDyadicCircle_initial_standard_sum
    (s t : ℕ) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (he : e 0 = 0)
    (K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (Q : Fin 2 → ℤ) :
    markedDyadicCircle ψ hψ hzero s t r hg k hk n e
        (physicalDyadicGood σ n e s K L H) 0 K Q (Sum.inl 0) =
      ∑ j ∈ (Finset.range (2 ^ s)).filter
        (standardPacketSurvives σ n e s t K L H 0 Q),
        standardCapCircleSchwartz ψ hψ hzero (2 ^ s) (by positivity) r hg k hk j := by
  rw [markedDyadicCircle_coarse ψ hψ hzero s t r hg k hk n e
    (physicalDyadicGood σ n e s K L H) 0 K Q 0 (by omega), he, Nat.sub_zero]
  have hs : dyadicCapSpatialSurvives s t n e (physicalDyadicGood σ n e s K L H) 0 K Q =
      fun p ↦ standardPacketSurvives σ n e s t K L H 0 Q p.1 := by
    funext p
    exact propext (dyadicCapSpatialSurvives_physical_iff σ n e s t K L H 0 Q p)
  rw [hs]
  exact inheritedCoarseCapCircle_standard_keep ψ hψ hzero (2 ^ s) (by positivity)
    r hg k hk (by positivity) _

/-- The actual initial marked function is the fixed spatial multiplier times the original
common source spectrum with its whole-standard survival mask. -/
theorem markedDyadicCircle_initial_common_spectrum
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (s t : ℕ) (r : ℝ)
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)
    (σ : Measure (EuclideanSpace ℝ (Fin 2))) (n e : ℕ → ℕ) (he : e 0 = 0)
    (K : ℕ) (L : ℝ) (H : ℕ → ℝ≥0∞) (Q : Fin 2 → ℤ)
    (y : EuclideanSpace ℝ (Fin 2)) :
    markedDyadicCircle ψ hψ hzero s t r (integrable_circle_planarMeasureFourier μ r)
        k hk n e (physicalDyadicGood σ n e s K L H) 0 K Q (Sum.inl 0) y =
      (𝓕⁻ k) y * circleSpectralExtension r
        (initialCommonSourceSpectrum μ ψ hψ hzero (2 ^ s) (by positivity)
          ((Finset.range (2 ^ s)).filter
            (standardPacketSurvives σ n e s t K L H 0 Q))) y := by
  rw [markedDyadicCircle_initial_standard_sum ψ hψ hzero s t r
    (integrable_circle_planarMeasureFourier μ r) k hk σ n e he K L H Q]
  simp only [standardCapCircleSchwartz, sum_circlePhysicalSchwartz_data,
    circlePhysicalSchwartz_apply]
  congr 2
  funext ξ
  simp only [initialCommonSourceSpectrum, standardCapData, sourcePacketSpectrum,
    planarMeasureFourier_eq_charFun]

end FalconerPacking
