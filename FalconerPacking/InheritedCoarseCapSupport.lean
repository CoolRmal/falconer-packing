/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.InheritedFineCapSupport
import FalconerPacking.CoarseCapCircleSupport
import FalconerPacking.CircleCapChordGeometry

/-!
# Actual coarse ancestors of surviving terminal cap labels

Coarse ancestors group whole standard labels. Terminal auxiliary cells may be arbitrarily
fine; their marks never create separate coarse enclosing balls. This includes a spatial
edge crossing the standard angular scale, without adding a spatial step.
-/

noncomputable section

open MeasureTheory Set Metric SchwartzMap FourierTransform Filter Classical
open scoped FourierTransform Topology

namespace FalconerPacking

variable (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
    (S : ℕ) (hS : 0 < S) (r : ℝ)
    {g : EuclideanSpace ℝ (Fin 2) → ℂ} (hg : Integrable g (normalizedCircleMeasure r))
    (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k)

/-- The actual coarse function with every later terminal deletion retained inside its sum. -/
def inheritedCoarseCapCircle (M T : ℕ) (keep : ℕ × ℕ → Prop) (c : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  inheritedLabelSum (fineCapLabels S T) (fun q ↦ q.1 / M) c keep
    (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk T)

/-- Unmarked terminal descendants reconstruct the grouped whole-standard function exactly. -/
theorem inheritedCoarseCapCircle_all {T : ℕ} (hT : 0 < T) (M c : ℕ) :
    inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M T (fun _ ↦ True) c =
      coarseCapCircleSchwartz ψ hψ hzero S hS r hg k hk M c := by
  simpa only [inheritedCoarseCapCircle, inheritedLabelSum, and_true] using
    sum_active_fineCapCircleSchwartz_coarse ψ hψ hzero S hS r hg k hk hT M c

/-- Crossing to a coarse ancestor regroups fine functions and keeps the standard index intact. -/
theorem inheritedCoarseCapCircle_eq_sum_fine {U F : ℕ} (hU : 0 < U) (hF : 0 < F)
    (M c : ℕ) (keep : ℕ × ℕ → Prop) :
    inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M (U * F) keep c =
      ∑ p ∈ (fineCapLabels S F).filter (fun p ↦ p.1 / M = c),
        inheritedFineCapCircle ψ hψ hzero S hS r hg k hk U F keep p := by
  simpa only [inheritedCoarseCapCircle, inheritedFineCapCircle, Function.comp_def,
    and_true, true_and] using
    inheritedLabelSum_regroup (fineCapLabels S (U * F)) (fineCapLabels S F)
      (fun q ↦ (q.1, q.2 / U)) (fun p ↦ p.1 / M)
      (fun q hq ↦ fineCapLabels_parent_mem hU hF hq) c (fun _ ↦ True) keep
      (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (U * F))

/-- Actual terminal data preserve their standard cap's nominal coarse ancestor support. -/
theorem inheritedCoarseCapCircle_fourier_support_of_thickening {ε : ℝ} (hr : 0 < r)
    {M N T : ℕ} (hM : 0 < M) (hN : 0 < N) (hsize : S = M * N)
    (keep : ℕ × ℕ → Prop) (c : ℕ) (hkball : Function.support k ⊆ closedBall 0 ε)
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : ∀ v, ‖v‖ = 1 → dist v (angularDirection (angularGridPoint N c)) < 6 * Real.pi / N →
      ∀ z, ‖z‖ ≤ ε → r • v + z ∈ A) :
    Function.support (fun z ↦
      𝓕 (inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M T keep c) z) ⊆ A := by
  subst S
  apply fourier_support_inheritedLabelSum
  intro q _ hparent _
  apply circlePhysicalSchwartz_fourier_support_of_data hr
    (integrable_circleCellData (integrable_standardCapData ψ hψ hzero _ hS hg q.1) T q.2)
    k hk hkball
  intro ξ hnorm hdata z hz
  have hstd : standardCapData ψ hψ hzero (M * N) hS q.1 g ξ ≠ 0 := by
    intro he
    by_cases hcell : ξ ∈ circleAngularCell T q.2
    · simp only [circleCellData, indicator_of_mem hcell, he, ne_eq, not_true_eq_false] at hdata
    · simp only [circleCellData, indicator_of_notMem hcell, ne_eq, not_true_eq_false] at hdata
  have hd := smoothAngularCap_direction_support ψ hψ hzero (M * N) hS q.1
    (mul_ne_zero_iff.mp hstd).1
  simp only [mem_ball, Nat.cast_mul] at hd
  have hc := standardCap_coarse_direction_bound hM hN q.1 hd
  rw [hparent] at hc
  have hv : ‖‖ξ‖⁻¹ • ξ‖ = 1 := norm_smul_inv_norm (norm_ne_zero_iff.mp (hnorm.trans_ne hr.ne'))
  have he : r • (‖ξ‖⁻¹ • ξ) = ξ := by
    rw [hnorm, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  simpa only [he] using hA (‖ξ‖⁻¹ • ξ) hv hc z hz

variable {R a b : ℝ}

/-- Arbitrary surviving descendants of a coarse label occupy one uniform enclosing ball. -/
theorem inheritedCoarseCapCircle_fourier_ball (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ 2 * R) (ha : 0 < a) (ha₁ : a ≤ 1)
    {M N T : ℕ} (hM : 0 < M) (hN : 0 < N) (hsize : S = M * N) (hscale : R * a ≤ N)
    (keep : ℕ × ℕ → Prop) (c : ℕ) (hkball : Function.support k ⊆ closedBall 0 1) :
    Function.support (fun z ↦
      𝓕 (inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M T keep c) z) ⊆
      ball (r • angularDirection (angularGridPoint N c)) (1000 / a) := by
  apply inheritedCoarseCapCircle_fourier_support_of_thickening ψ hψ hzero S hS r hg k hk
    hr hM hN hsize keep c hkball
  intro v _ hd z hz
  have hw : 6 * Real.pi / N ≤ 24 / (R * a) := by
    calc
      _ ≤ (24 : ℝ) / N := by gcongr; linarith [Real.pi_lt_four]
      _ ≤ _ := by gcongr
  have ht : r * (24 / (R * a)) ≤ 48 / a := by
    rw [show r * (24 / (R * a)) = 24 * (r / (R * a)) by ring]
    have : r / (R * a) ≤ 2 / a := by
      rw [div_le_div_iff₀ (mul_pos hR ha) ha]
      nlinarith
    calc
      _ ≤ 24 * (2 / a) := by gcongr
      _ = _ := by ring
  have he : dist (r • v + z) (r • v) = ‖z‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  have hunit : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha₁)
  change dist _ _ < _
  calc
    _ ≤ dist (r • v + z) (r • v) + dist (r • v) _ := dist_triangle _ _ _
    _ = ‖z‖ + r * dist v (angularDirection (angularGridPoint N c)) := by
      rw [he, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
    _ ≤ 1 / a + 48 / a := add_le_add (hz.trans hunit)
      ((mul_le_mul_of_nonneg_left (hd.le.trans hw) hr.le).trans ht)
    _ < 1000 / a := by rw [← add_div]; apply div_lt_div_of_pos_right (by norm_num) ha

/-- The coarse nominal frame satisfies actual curvature admissibility, also across the branch cut. -/
theorem inheritedCoarseCapCircle_fourier_rectangle (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ 2 * R) (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) {M N T : ℕ} (hM : 0 < M) (hN : 0 < N)
    (hsize : S = M * N) (hscale : R * a ≤ N) (keep : ℕ × ℕ → Prop) (c : ℕ)
    (hkball : Function.support k ⊆ closedBall 0 1) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Function.support (fun z ↦
      𝓕 (inheritedCoarseCapCircle ψ hψ hzero S hS r hg k hk M T keep c) z)) :
    |circleCapFrame (angularGridPoint N c) (z - r • angularDirection (angularGridPoint N c)) 0| ≤
      1000 / a ∧
    |circleCapFrame (angularGridPoint N c) (z - r • angularDirection (angularGridPoint N c)) 1| ≤
      1000 / b := by
  apply inheritedCoarseCapCircle_fourier_support_of_thickening ψ hψ hzero S hS r hg k hk
    hr hM hN hsize keep c hkball _ _ hz
  intro v hv hd w hw
  have hwidth : 6 * Real.pi / N ≤ 24 / (R * a) := by
    calc
      _ ≤ (24 : ℝ) / N := by gcongr; linarith [Real.pi_lt_four]
      _ ≤ _ := by gcongr
  exact circleCapFrame_chord_admissible_rectangle hR hr.le hrR ha ha₁ hb hb₁ hab
    v hv (hd.le.trans hwidth) w hw

/-- Coarse balls are indexed by coarse ancestors only, with an absolute overlap bound. -/
theorem inheritedCoarseCapCircle_ball_overlap {N : ℕ} (hN : 0 < N)
    {R r a : ℝ} (hR : 0 < R) (hrR : R ≤ r) (ha : 0 < a)
    (hscale : (N : ℝ) ≤ 2 * (R * a)) (z : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun c ↦
      z ∈ ball (r • angularDirection (angularGridPoint N c)) (1000 / a))).card ≤
        Nat.ceil (2000 + 2 * Real.pi) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hw : 1000 / a ≤ 2000 * r / N := by
    rw [div_le_div_iff₀ ha hN']
    nlinarith
  apply (Finset.card_le_card (show (Finset.range N).filter (fun c ↦
    z ∈ ball (r • angularDirection (angularGridPoint N c)) (1000 / a)) ⊆
      (Finset.range N).filter (fun c ↦
    z ∈ ball (r • angularDirection (angularGridPoint N c)) (2000 * r / N)) from ?_)).trans
      (card_circle_grid_balls_le N hN (hR.trans_le hrR) (by norm_num) z)
  intro c hc
  obtain ⟨hc, hz⟩ := Finset.mem_filter.mp hc
  exact Finset.mem_filter.mpr ⟨hc, lt_of_lt_of_le hz hw⟩

end FalconerPacking
