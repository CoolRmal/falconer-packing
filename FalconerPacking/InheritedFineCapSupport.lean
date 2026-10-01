/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ActiveCapCircleTree
import FalconerPacking.CircleCapScaledGeometry

/-!
# Fourier geometry of actual surviving fine descendants

A current function is the sum of arbitrary surviving terminal circle pieces. Its
Fourier support stays in the current auxiliary arc, while its physical frame remains
the standard cap's frame. Both enclosing-ball overlap and curvature bounds are uniform.
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

/-- One common function per current label, before any child-dependent selection is applied. -/
def inheritedFineCapCircle (M F : ℕ) (keep : ℕ × ℕ → Prop) (p : ℕ × ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ :=
  inheritedLabelSum (fineCapLabels S (M * F)) (fun q ↦ (q.1, q.2 / M)) p keep
    (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F))

/-- Every surviving terminal piece lies in its actual current ancestor's thickened arc. -/
theorem inheritedFineCapCircle_fourier_support_of_thickening {ε : ℝ} (hr : 0 < r)
    {M F : ℕ} (hM : 0 < M) (hF : 0 < F) (keep : ℕ × ℕ → Prop) (p : ℕ × ℕ)
    (hkball : Function.support k ⊆ closedBall 0 ε)
    (T : Set (EuclideanSpace ℝ (Fin 2)))
    (hT : ∀ θ ∈ angularGridCell F p.2, ∀ z, ‖z‖ ≤ ε → r • angularDirection θ + z ∈ T) :
    Function.support (fun z ↦
      𝓕 (inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep p) z) ⊆ T := by
  apply fourier_support_inheritedLabelSum
  intro q _ hp _
  apply circleCellPhysicalSchwartz_fourier_support_of_thickening hr
    (integrable_standardCapData ψ hψ hzero S hS hg q.1) (M * F) q.2 k hk hkball
  intro θ hθ z hz
  have hparent := angularGridCell_refinement_subset hM hF q.2 hθ
  have he : q.2 / M = p.2 := congrArg Prod.snd hp
  rw [he] at hparent
  exact hT θ hparent z hz

/-- Forgetting all later marks recovers the actual unmarked current function exactly. -/
theorem inheritedFineCapCircle_all {M F : ℕ} (hM : 0 < M) (hF : 0 < F)
    (p : ℕ × ℕ) (hp : p.1 < S) :
    inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F (fun _ ↦ True) p =
      fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk F p := by
  rcases p with ⟨j, c⟩
  simpa only [inheritedFineCapCircle, inheritedLabelSum, and_true, Prod.mk.injEq] using
    sum_active_fineCapCircleSchwartz_refinement ψ hψ hzero S hS r hg k hk hM hF hp c

/-- The whole selected sum is the exact terminal sum with the corresponding ancestor mark. -/
theorem sum_inheritedFineCapCircle_selected {M F : ℕ} (hM : 0 < M) (hF : 0 < F)
    (keep : ℕ × ℕ → Prop) (selection : Finset (ℕ × ℕ))
    (hselection : selection ⊆ fineCapLabels S F) :
    ∑ p ∈ selection, inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep p =
      ∑ q ∈ (fineCapLabels S (M * F)).filter
        (fun q ↦ (q.1, q.2 / M) ∈ selection ∧ keep q),
        fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F) q := by
  have h := inheritedLabelSum_regroup (fineCapLabels S (M * F)) (fineCapLabels S F)
    (fun q ↦ (q.1, q.2 / M)) (fun _ ↦ ())
    (fun q hq ↦ fineCapLabels_parent_mem hM hF hq) ()
    (fun p ↦ p ∈ selection) keep
    (fineCapCircleSchwartz ψ hψ hzero S hS r hg k hk (M * F))
  have he : (fineCapLabels S F).filter (fun p ↦ p ∈ selection) =
      selection := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hp ↦ ⟨hselection hp, hp⟩⟩
  simp only [true_and] at h
  rw [he] at h
  simpa only [inheritedFineCapCircle, inheritedLabelSum, Function.comp_apply, true_and]
    using h.symm

variable {R a b : ℝ}

/-- The inherited arc has an actual enclosing ball of radius `100/a`. -/
theorem inheritedFineCapCircle_fourier_ball (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ 2 * R) (ha : 0 < a) (ha₁ : a ≤ 1)
    {M F : ℕ} (hM : 0 < M) (hF : 0 < F) (hscale : R * a ≤ F)
    (keep : ℕ × ℕ → Prop) (p : ℕ × ℕ)
    (hkball : Function.support k ⊆ closedBall 0 1) :
    Function.support (fun z ↦
      𝓕 (inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep p) z) ⊆
      ball (r • angularDirection (angularGridPoint F p.2)) (100 / a) := by
  apply inheritedFineCapCircle_fourier_support_of_thickening ψ hψ hzero S hS r hg k hk
    hr hM hF keep p hkball
  intro θ hθ z hz
  have hw : 2 * Real.pi / F ≤ 8 / (R * a) := by
    calc
      _ ≤ (8 : ℝ) / F := by gcongr; linarith [Real.pi_lt_four]
      _ ≤ _ := by gcongr
  have ht : r * (8 / (R * a)) ≤ 16 / a := by
    rw [show r * (8 / (R * a)) = 8 * (r / (R * a)) by ring]
    have : r / (R * a) ≤ 2 / a := by
      rw [div_le_div_iff₀ (mul_pos hR ha) ha]
      nlinarith
    calc
      _ ≤ 8 * (2 / a) := by gcongr
      _ = _ := by ring
  have hdist := circleGridCell_dist_le hr.le hθ
  have ht' := dist_triangle (r • angularDirection θ + z) (r • angularDirection θ)
    (r • angularDirection (angularGridPoint F p.2))
  have he : dist (r • angularDirection θ + z) (r • angularDirection θ) = ‖z‖ := by
    rw [dist_eq_norm, add_sub_cancel_left]
  rw [he] at ht'
  have hunit : 1 ≤ 1 / a := (le_div_iff₀ ha).mpr (by simpa using ha₁)
  change dist _ _ < _
  calc
    _ ≤ ‖z‖ + r * (2 * Real.pi / F) := ht'.trans (add_le_add_right hdist _)
    _ ≤ 1 / a + 16 / a := add_le_add (hz.trans hunit)
      ((mul_le_mul_of_nonneg_left hw hr.le).trans ht)
    _ < 100 / a := by rw [← add_div]; apply div_lt_div_of_pos_right (by norm_num) ha

/-- Arbitrary terminal deletions preserve the curvature rectangle needed by embedding. -/
theorem inheritedFineCapCircle_fourier_rectangle (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ 2 * R) (ha : 0 < a) (ha₁ : a ≤ 1) (hb : 0 < b) (hb₁ : b ≤ 1)
    (hab : b ≤ R * a ^ 2) {M F : ℕ} (hM : 0 < M) (hF : 0 < F)
    (hscale : R * a ≤ F) (keep : ℕ × ℕ → Prop) (p : ℕ × ℕ)
    (hkball : Function.support k ⊆ closedBall 0 1) {z : EuclideanSpace ℝ (Fin 2)}
    (hz : z ∈ Function.support (fun z ↦
      𝓕 (inheritedFineCapCircle ψ hψ hzero S hS r hg k hk M F keep p) z)) :
    |circleCapFrame (angularGridPoint F p.2)
        (z - r • angularDirection (angularGridPoint F p.2)) 0| ≤ 100 / a ∧
      |circleCapFrame (angularGridPoint F p.2)
        (z - r • angularDirection (angularGridPoint F p.2)) 1| ≤ 100 / b := by
  apply inheritedFineCapCircle_fourier_support_of_thickening ψ hψ hzero S hS r hg k hk
    hr hM hF keep p hkball _ _ hz
  intro θ hθ w hw
  have hwidth : 2 * Real.pi / F ≤ 8 / (R * a) := by
    calc
      _ ≤ (8 : ℝ) / F := by gcongr; linarith [Real.pi_lt_four]
      _ ≤ _ := by gcongr
  obtain ⟨h₀, h₁⟩ := circleCapFrame_scaled_admissible_rectangle hR (by norm_num : (0 : ℝ) ≤ 8)
    hr.le hrR ha ha₁ hb hb₁ hab ((angularGridCell_angle_bound hθ).trans hwidth) w hw
  exact ⟨h₀.trans (by norm_num; gcongr; norm_num),
    h₁.trans (by norm_num; gcongr; norm_num)⟩

/-- The enclosing balls for actual active labels have an absolute, grid-independent overlap. -/
theorem inheritedFineCapCircle_ball_overlap {S F : ℕ} (hS : 0 < S) (hSF : S ≤ F)
    {R r a : ℝ} (hR : 0 < R) (hrR : R ≤ r) (ha : 0 < a)
    (hscale : (F : ℝ) ≤ 2 * (R * a)) (z : EuclideanSpace ℝ (Fin 2)) :
    ((fineCapLabels S F).filter (fun p ↦
      z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (100 / a))).card ≤
      Nat.ceil (200 + 8 * Real.pi) * Nat.ceil (200 + 2 * Real.pi) := by
  have hF : (0 : ℝ) < F := Nat.cast_pos.mpr (hS.trans_le hSF)
  have hw : 100 / a ≤ 200 * r / F := by
    rw [div_le_div_iff₀ ha hF]
    nlinarith
  apply (Finset.card_le_card (show (fineCapLabels S F).filter (fun p ↦
    z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (100 / a)) ⊆
      (fineCapLabels S F).filter (fun p ↦
    z ∈ ball (r • angularDirection (angularGridPoint F p.2)) (200 * r / F)) from ?_)).trans
      (fineCapLabels_ball_overlap hS hSF (hR.trans_le hrR) (by norm_num) z)
  intro p hp
  obtain ⟨hp, hz⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hp, lt_of_lt_of_le hz hw⟩

end FalconerPacking
