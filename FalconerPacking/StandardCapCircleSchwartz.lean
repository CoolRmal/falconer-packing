/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.StandardCapLabelData
public import FalconerPacking.CircleCellSupport

/-!
# Actual Schwartz functions for the standard-cap angular tree

The circular data are smoothed only after angular restriction. Exact parent sums hold
for whole coarse caps, fine auxiliary cells, and edges crossing the standard scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Filter Classical
open scoped FourierTransform Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (S : ℕ) (hS : 0 < S) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)

/-- Actual smoothed circle data for a whole standard label. -/
def standardCapCircleSchwartz (j : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  circlePhysicalSchwartz r (integrable_standardCapData ψ hψ hzero S hS hg j) k hk

/-- Coarse labels group whole standard functions, not repeated standard labels with large balls. -/
def coarseCapCircleSchwartz (M c : ℕ) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  ∑ j ∈ (Finset.range S).filter (fun j ↦ j / M = c),
    standardCapCircleSchwartz ψ hψ hzero S hS r hg k hk j

/-- Fine labels preserve the standard label while restricting actual circular spectral data. -/
def fineCapCircleSchwartz (F : ℕ) (p : ℕ × ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  circleCellPhysicalSchwartz r (integrable_standardCapData ψ hψ hzero S hS hg p.1)
    F p.2 k hk

/-- The coarse sum is exactly the circle function of the actual grouped data. -/
theorem coarseCapCircleSchwartz_eq_data (M c : ℕ) :
    coarseCapCircleSchwartz ψ hψ hzero S hS r hg k hk M c =
      circlePhysicalSchwartz r (integrable_coarseStandardCapData ψ hψ hzero S hS hg M c) k hk := by
  exact sum_circlePhysicalSchwartz_data _ r _
    (fun j ↦ integrable_standardCapData ψ hψ hzero S hS hg j) k hk

/-- Every standard function is recovered by all its fine cells, including boundary crossings. -/
theorem sum_fineCapCircleSchwartz_standard {F : ℕ} (hF : 0 < F) (j : ℕ) :
    ∑ i ∈ Finset.range F, fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F (j, i) =
      standardCapCircleSchwartz ψ hψ hzero S hS r hg k hk j :=
  sum_circleCellPhysicalSchwartz hF r (integrable_standardCapData ψ hψ hzero S hS hg j) k hk

/-- Fine physical parent sums keep their inherited standard label exactly. -/
theorem sum_fineCapCircleSchwartz_refinement {M F : ℕ} (hM : 0 < M) (hF : 0 < F)
    (j c : ℕ) :
    ∑ i ∈ (Finset.range (M * F)).filter (fun i ↦ i / M = c),
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F) (j, i) =
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F (j, c) :=
  sum_circleCellPhysicalSchwartz_refinement hM hF c r
    (integrable_standardCapData ψ hψ hzero S hS hg j) k hk

/-- Crossing the standard angular scale is an exact physical sum, without an extra spatial step. -/
theorem sum_fineCapCircleSchwartz_coarse {F : ℕ} (hF : 0 < F) (M c : ℕ) :
    ∑ j ∈ (Finset.range S).filter (fun j ↦ j / M = c), ∑ i ∈ Finset.range F,
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F (j, i) =
      coarseCapCircleSchwartz ψ hψ hzero S hS r hg k hk M c := by
  simp only [sum_fineCapCircleSchwartz_standard ψ hψ hzero S hS r hg k hk hF]
  rfl

/-- Coarse ancestors regroup whole standard Schwartz functions exactly. -/
theorem coarseCapCircleSchwartz_regroup {L M N : ℕ} (hL : 0 < L)
    (hsize : S = L * (M * N)) (c : ℕ) :
    coarseCapCircleSchwartz ψ hψ hzero S hS r hg k hk (L * M) c =
      ∑ j ∈ (Finset.range (M * N)).filter (fun j ↦ j / M = c),
        coarseCapCircleSchwartz ψ hψ hzero S hS r hg k hk L j := by
  have hlabel : ∀ j ∈ Finset.range S, j / L ∈ Finset.range (M * N) := by
    intro j hj
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hL).mpr
    rw [mul_comm]
    exact hsize ▸ Finset.mem_range.mp hj
  have h := inheritedLabelSum_regroup (Finset.range S) (Finset.range (M * N))
    (fun j ↦ j / L) (fun j ↦ j / M) hlabel c (fun _ ↦ True) (fun _ ↦ True)
    (standardCapCircleSchwartz ψ hψ hzero S hS r hg k hk)
  simpa only [inheritedLabelSum, Function.comp_apply, Nat.div_div_eq_div_mul, and_true,
    coarseCapCircleSchwartz] using h

/-- Fine Fourier supports lie in the actual auxiliary cell balls; no indicator derivatives occur. -/
theorem fineCapCircleSchwartz_fourier_ball {C : ℝ} (hr : 0 < r)
    {F : ℕ} (hF : 0 < F) (hscale : (F : ℝ) ≤ C * r)
    (hkball : Function.support k ⊆ closedBall 0 1) (p : ℕ × ℕ) :
    Function.support (𝓕 (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) ⊆
      ball (r • angularDirection (angularGridPoint F p.2))
        ((2 * Real.pi + C + 1) * r / F) :=
  circleCellPhysicalSchwartz_fourier_ball hr hF hscale
    (integrable_standardCapData ψ hψ hzero S hS hg p.1) p.2 k hk hkball

/-- Actual fine Fourier supports have a uniform overlap bound over incident pair labels. -/
theorem fineCapCircleSchwartz_fourier_overlap {C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    {F : ℕ} (hSF : S ≤ F) (hscale : (F : ℝ) ≤ C * r)
    (hkball : Function.support k ⊆ closedBall 0 1) (ξ : EuclideanSpace ℝ (Fin 2)) :
    ((fineCapLabels S F).filter (fun p ↦
      𝓕 (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p) ξ ≠ 0)).card ≤
        Nat.ceil (10 * Real.pi + C + 1) * Nat.ceil (4 * Real.pi + C + 1) := by
  have hsub : (fineCapLabels S F).filter (fun p ↦
      𝓕 (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p) ξ ≠ 0) ⊆
      (fineCapLabels S F).filter (fun p ↦
        ξ ∈ ball (r • angularDirection (angularGridPoint F p.2))
          ((2 * Real.pi + C + 1) * r / F)) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
      fineCapCircleSchwartz_fourier_ball ψ hψ hzero S hS r hg k hk hr
        (hS.trans_le hSF) hscale hkball p (Finset.mem_filter.mp hp).2⟩
  apply (Finset.card_le_card hsub).trans
  simpa only [show (2 * Real.pi + C + 1) + 8 * Real.pi =
      10 * Real.pi + C + 1 by ring,
    show (2 * Real.pi + C + 1) + 2 * Real.pi = 4 * Real.pi + C + 1 by ring] using
    fineCapLabels_ball_overlap hS hSF hr (by positivity : 0 ≤ 2 * Real.pi + C + 1) ξ

end FalconerPacking
