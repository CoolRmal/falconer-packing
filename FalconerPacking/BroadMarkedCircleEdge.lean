/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.BroadSelectedCircleParents
import FalconerPacking.MarkedCircleParentEdge
import FalconerPacking.DyadicCircleIdentification
import FalconerPacking.DyadicGridEdgeGeometry

/-!
# One actual marked spatial edge through coarse and fine angular scales

The child selections, the common parent function, angular regrouping, Fourier supports,
and spatial center geometry all come from their explicit constructions. Only the numerical
scale conditions and the physical selected-tube mass tests remain as inputs.
-/

noncomputable section

open MeasureTheory Set Metric Filter Classical SchwartzMap
open scoped ENNReal Topology

namespace FalconerPacking

/-- A complete marked edge, including a crossing of the standard angular scale. -/
theorem selected_markedDyadicCircle_parent_embedding_ratio (Bann : ℝ) (hBann : 0 < Bann) (pwr K : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[𝓝 0] 0)
        (s t : ℕ) (n e : ℕ → ℕ), Antitone n → Monotone e →
      ∀ (good : ℕ → (Fin 2 → ℤ) → (ℕ ⊕ (ℕ × ℕ)) → Prop)
        (j : ℕ), j < K → e (j + 1) ≤ t →
      ∀ (R r L : ℝ), 0 < R → R ≤ Bann * r → r ≤ 2 * R → 346 ≤ L →
      ∀ (g : EuclideanSpace ℝ (Fin 2) → ℂ)
        (hg : Integrable g (normalizedCircleMeasure r))
        (k : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hk : HasCompactSupport k),
        Function.support k ⊆ closedBall 0 1 →
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure σ]
        (I : Finset (Fin 2 → ℤ)) (P : Fin 2 → ℤ),
        (∀ Q ∈ I, ancestor (n j - n (j + 1)) Q = P) →
        let a := ((2 : ℝ) ^ n j)⁻¹
        let b := ((2 : ℝ) ^ n (j + 1))⁻¹
        let E := enlargedGridSquare a (L ^ (2 * j + 2))
        let U := enlargedGridSquare b (L ^ (2 * (j + 1) + 2)) P
        let f := markedDyadicCircle ψ hψ hzero s t r hg k hk n e good
        b ≤ R * a ^ 2 → R * a ≤ 2 ^ e (j + 1) →
        (2 : ℝ) ^ e (j + 1) ≤ 2 * (R * a) →
        (s < e (j + 1) → ((2 : ℝ) ^ s)⁻¹ ≤ a / b) →
      ∀ H : ℝ≥0∞,
        (∀ Q ∈ I, ∀ β ∈ dyadicCapLabels s (e (j + 1)), good j Q β →
          σ (frameRectangle (dyadicCapPhysicalFrame s (e (j + 1)) β)
            (gridSquareCenter a Q) (L ^ (4 * K + 20) * a / 2)
            (L ^ (4 * K + 20) * b / 2) ∩ U) ≤
            H * ENNReal.ofReal (a / b) * σ U) →
        (∑ Q ∈ I, ∑ α ∈ dyadicCapLabels s (e j), σ (E Q) *
          ∫⁻ x, ‖f j K Q α x‖ₑ ^ 2 ∂((volume (E Q))⁻¹ • volume.restrict (E Q))) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal (L ^ (8 * j + 14)) * H * σ U *
                (∑ β ∈ dyadicCapLabels s (e (j + 1)), ∫⁻ x, ‖f (j + 1) K P β x‖ₑ ^ 2
                  ∂((volume U)⁻¹ • volume.restrict U)) +
              ENNReal.ofReal ((a ^ 2)⁻¹ * (L ^ pwr)⁻¹) * σ U *
                ∑ β ∈ dyadicCapLabels s (e (j + 1)), ∫⁻ x, ‖f (j + 1) K P β x‖ₑ ^ 2) := by
  obtain ⟨Cc, hCc, hc⟩ := selected_inheritedCoarseCapCircle_parents_embedding_ratio Bann hBann pwr K
  obtain ⟨Cf, hCf, hf⟩ := selected_inheritedFineCapCircle_parents_embedding_ratio Bann hBann pwr K
  refine ⟨Cc + Cf, by positivity, ?_⟩
  intro ψ hψ hzero s t n e hn he good j hj het R r L hR hrR hr₂ hL
    g hg k hk hkball σ hσ I P hP
  dsimp only
  intro hcurv hscale₀ hscale₁ hframe H htest
  let a := ((2 : ℝ) ^ n j)⁻¹
  let b := ((2 : ℝ) ^ n (j + 1))⁻¹
  let U := enlargedGridSquare b (L ^ (2 * (j + 1) + 2)) P
  let keep := dyadicCapSpatialSurvives s t n e good (j + 1) K P
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_right₀ (by norm_num) (hn (Nat.le_succ j)))
  have hb₁ : b ≤ 1 := by
    dsimp [b]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hcenters : ∀ Q ∈ I, ∀ i,
      |(gridSquareCenter a Q) i - (gridSquareCenter b P) i| ≤ b / 2 := by
    intro Q hQ i
    have h := dyadic_child_center_parent_bound (hn (Nat.le_succ j)) Q i
    simpa only [hP Q hQ] using h
  have hU : U = frameRectangle (LinearIsometryEquiv.refl ℝ _) (gridSquareCenter b P)
      (L ^ (2 * j + 4) * b / 2) (L ^ (2 * j + 4) * b / 2) :=
    enlargedGridSquare_next_level b L j P
  by_cases hes : e (j + 1) ≤ s
  · let J := Finset.range (2 ^ e (j + 1))
    let selection := fun Q ↦ J.filter (fun c ↦ good j Q (Sum.inl c))
    let parent := fun c ↦ dyadicCapParent s (e j) (e (j + 1)) (Sum.inl c)
    have hparent : ∀ c ∈ J, parent c ∈ dyadicCapLabels s (e j) := by
      intro c hc
      apply dyadicCapParent_mem (he (Nat.le_succ j))
      simp only [dyadicCapLabels, if_pos hes]
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have hsize : (2 : ℕ) ^ s = 2 ^ (s - e (j + 1)) * 2 ^ e (j + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hes]
    have hbound := hc ψ hψ hzero (2 ^ s) (2 ^ (s - e (j + 1))) (2 ^ e (j + 1))
      (2 ^ t) (by positivity) (by positivity) (by positivity) hsize R r a b L hR hrR hr₂
      ha hab hb₁ hcurv (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale₀) (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale₁)
      (by linarith) g hg k hk hkball (dyadicCapLabels s (e j)) parent hparent keep I selection
      (fun _ _ ↦ Finset.filter_subset _ _) σ (gridSquareCenter b P) j hj hcenters H
    have ht : ∀ Q ∈ I, ∀ c ∈ selection Q,
        σ (frameRectangle (circleCapFrame (angularGridPoint (2 ^ e (j + 1)) c))
          (gridSquareCenter a Q) (L ^ (4 * K + 20) * a / 2)
          (L ^ (4 * K + 20) * b / 2) ∩ U) ≤ H * ENNReal.ofReal (a / b) * σ U := by
      intro Q hQ c hc
      have hc' := Finset.mem_filter.mp hc
      apply htest Q hQ (Sum.inl c)
      · simp only [dyadicCapLabels, if_pos hes]
        exact Finset.mem_image.mpr ⟨c, hc'.1, rfl⟩
      · exact hc'.2
    rw [← hU] at hbound
    have hh := hbound ht
    have hid (Q) (hQ : Q ∈ I) (α) :
        markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α =
        ∑ c ∈ (selection Q).filter (fun c ↦ parent c = α),
          inheritedCoarseCapCircle ψ hψ hzero (2 ^ s) (by positivity) r hg k hk
            (2 ^ (s - e (j + 1))) (2 ^ t) keep c := by
      rw [markedDyadicCircle_step_coarse ψ hψ hzero s t r hg k hk n e hn he good hj het hes]
      simp only [hP Q hQ]
      apply Finset.sum_congr
      · ext c
        simp only [selection, J, parent, Finset.mem_filter, and_assoc, and_comm]
      · intro c _
        rfl
    have henergy (ν : Measure (EuclideanSpace ℝ (Fin 2))) :
        (∑ β ∈ dyadicCapLabels s (e (j + 1)), ∫⁻ x,
          ‖markedDyadicCircle ψ hψ hzero s t r hg k hk n e good (j + 1) K P β x‖ₑ ^ 2 ∂ν) =
        ∑ c ∈ J, ∫⁻ x, ‖inheritedCoarseCapCircle ψ hψ hzero (2 ^ s) (by positivity)
          r hg k hk (2 ^ (s - e (j + 1))) (2 ^ t) keep c x‖ₑ ^ 2 ∂ν := by
      rw [sum_dyadicCapLabels_coarse hes]
      simp_rw [markedDyadicCircle_coarse ψ hψ hzero s t r hg k hk n e good _ _ _ _ hes]
      rfl
    rw [henergy, henergy]
    rw [Finset.sum_comm] at hh
    refine (le_of_eq ?_).trans (hh.trans ?_)
    · apply Finset.sum_congr rfl
      intro Q hQ
      simp_rw [hid Q hQ, sum_apply]
      apply Finset.sum_congr rfl
      intro α _
      congr 1
      apply lintegral_congr
      intro x
      apply congrArg (fun z : ℂ ↦ ‖z‖ₑ ^ 2)
      apply Finset.sum_congr
      · ext c
        simp only [Finset.mem_filter]
      · intro c _
        rfl
    · gcongr
      exact le_add_of_nonneg_right hCf.le
  · have hse : s < e (j + 1) := Nat.lt_of_not_ge hes
    let J := fineCapLabels (2 ^ s) (2 ^ e (j + 1))
    let selection := fun Q ↦ J.filter (fun c ↦ good j Q (Sum.inr c))
    let parent := fun c ↦ dyadicCapParent s (e j) (e (j + 1)) (Sum.inr c)
    have hparent : ∀ c ∈ J, parent c ∈ dyadicCapLabels s (e j) := by
      intro c hc
      apply dyadicCapParent_mem (he (Nat.le_succ j))
      simp only [dyadicCapLabels, if_neg hes]
      exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have hbound := hf ψ hψ hzero (2 ^ s) (2 ^ (t - e (j + 1))) (2 ^ e (j + 1))
      (by positivity) (by positivity) (Nat.pow_le_pow_right (by norm_num) hse.le)
      R r a b L hR hrR hr₂ ha hab hb₁ hcurv
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale₀) (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hscale₁)
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hframe hse) hL g hg k hk hkball (dyadicCapLabels s (e j))
      parent hparent keep I selection (fun _ _ ↦ Finset.filter_subset _ _)
      σ (gridSquareCenter b P) j hj hcenters H
    have ht : ∀ Q ∈ I, ∀ c ∈ selection Q,
        σ (frameRectangle (circleCapFrame (angularGridPoint (2 ^ s) c.1))
          (gridSquareCenter a Q) (L ^ (4 * K + 20) * a / 2)
          (L ^ (4 * K + 20) * b / 2) ∩ U) ≤ H * ENNReal.ofReal (a / b) * σ U := by
      intro Q hQ c hc
      have hc' := Finset.mem_filter.mp hc
      apply htest Q hQ (Sum.inr c)
      · simp only [dyadicCapLabels, if_neg hes]
        exact Finset.mem_image.mpr ⟨c, hc'.1, rfl⟩
      · exact hc'.2
    rw [← hU] at hbound
    have hh := hbound ht
    have hid (Q) (hQ : Q ∈ I) (α) :
        markedDyadicCircle ψ hψ hzero s t r hg k hk n e good j K Q α =
        ∑ c ∈ (selection Q).filter (fun c ↦ parent c = α),
          inheritedFineCapCircle ψ hψ hzero (2 ^ s) (by positivity) r hg k hk
            (2 ^ (t - e (j + 1))) (2 ^ e (j + 1)) keep c := by
      rw [markedDyadicCircle_step_fine ψ hψ hzero s t r hg k hk n e hn he good hj het hse]
      simp only [hP Q hQ]
      apply Finset.sum_congr
      · ext c
        simp only [selection, J, parent, Finset.mem_filter, and_assoc, and_comm]
      · intro c _
        rfl
    have henergy (ν : Measure (EuclideanSpace ℝ (Fin 2))) :
        (∑ β ∈ dyadicCapLabels s (e (j + 1)), ∫⁻ x,
          ‖markedDyadicCircle ψ hψ hzero s t r hg k hk n e good (j + 1) K P β x‖ₑ ^ 2 ∂ν) =
        ∑ c ∈ J, ∫⁻ x, ‖inheritedFineCapCircle ψ hψ hzero (2 ^ s) (by positivity)
          r hg k hk (2 ^ (t - e (j + 1))) (2 ^ e (j + 1)) keep c x‖ₑ ^ 2 ∂ν := by
      rw [sum_dyadicCapLabels_fine hse]
      simp_rw [markedDyadicCircle_fine ψ hψ hzero s t r hg k hk n e good _ _ _ _ hse het]
      rfl
    rw [henergy, henergy]
    rw [Finset.sum_comm] at hh
    refine (le_of_eq ?_).trans (hh.trans ?_)
    · apply Finset.sum_congr rfl
      intro Q hQ
      simp_rw [hid Q hQ, sum_apply]
      apply Finset.sum_congr rfl
      intro α _
      congr 1
      apply lintegral_congr
      intro x
      apply congrArg (fun z : ℂ ↦ ‖z‖ₑ ^ 2)
      apply Finset.sum_congr
      · ext c
        simp only [Finset.mem_filter]
      · intro c _
        rfl
    · gcongr
      exact le_add_of_nonneg_left hCc.le

end FalconerPacking
