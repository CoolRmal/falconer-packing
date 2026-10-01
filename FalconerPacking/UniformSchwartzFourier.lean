/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Uniform actual inverse-Fourier bounds for compact symbol families

Common bounded support and uniform bounds for each derivative order make a symbol family
bounded in Schwartz space. Continuity of the actual inverse Fourier transform then supplies
uniform rapid decay and weighted first-norm bounds for its kernels.
-/

noncomputable section

open MeasureTheory Set Metric Bornology FourierTransform

namespace FalconerPacking

/-- A common compact support and actual derivative estimates bound the full Schwartz family. -/
theorem isVonNBounded_schwartz_range_of_derivatives {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (R : ℝ)
    (hs : ∀ i, tsupport (F i) ⊆ closedBall 0 R)
    (hd : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖iteratedFDeriv ℝ n (F i) x‖ ≤ C) :
    IsVonNBounded ℝ (range F) := by
  apply (schwartz_withSeminorms ℝ _ _).isVonNBounded_iff_seminorm_bounded.mpr
  intro p
  obtain ⟨C, hC, hbound⟩ := hd p.2
  refine ⟨(max 1 R) ^ p.1 * C + 1, by positivity, ?_⟩
  rintro _ ⟨i, rfl⟩
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ p.1 p.2 (F i) (by positivity) ?_)
    (lt_add_one _)
  intro x
  by_cases hx : x ∈ tsupport (F i)
  · have hn : ‖x‖ ≤ max 1 R :=
      (show ‖x‖ ≤ R by simpa only [mem_closedBall, dist_zero_right] using hs i hx).trans
        (le_max_right _ _)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg x) hn _) (hbound i x)
      (norm_nonneg _) (by positivity)
  · have hz : iteratedFDeriv ℝ p.2 (F i) x = 0 := by
      by_contra h
      exact hx (support_iteratedFDeriv_subset p.2 h)
    simp only [hz, norm_zero, mul_zero]
    positivity

/-- The actual inverse-Fourier image of a bounded Schwartz family is bounded. -/
theorem isVonNBounded_fourierInv_range {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hF : IsVonNBounded ℝ (range F)) :
    IsVonNBounded ℝ (range (fun i ↦ (𝓕⁻ (F i) :
      SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ))) := by
  have h := hF.image (fourierInvCLM ℝ (SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ))
  simpa only [← range_comp, Function.comp_def, fourierInvCLM_apply] using h

/-- Bounded Schwartz families have a uniform constant in every rapid-decay estimate. -/
theorem exists_uniform_schwartz_decay {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hF : IsVonNBounded ℝ (range F)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i x, ‖F i x‖ ≤ C / (1 + ‖x‖) ^ m := by
  have hp := (schwartz_withSeminorms ℝ _ _).isVonNBounded_iff_seminorm_bounded.mp hF
  obtain ⟨C₀, hC₀, hb₀⟩ := hp (0, 0)
  obtain ⟨C₁, hC₁, hb₁⟩ := hp (m, 0)
  refine ⟨2 ^ m * (C₀ + C₁), by positivity, ?_⟩
  intro i x
  apply (le_div_iff₀ (by positivity)).mpr
  by_cases hx : ‖x‖ ≤ 1
  · have hn : ‖F i x‖ ≤ C₀ :=
      ((F i).norm_le_seminorm ℝ x).trans (hb₀ (F i) (mem_range_self i)).le
    calc
      _ ≤ C₀ * 2 ^ m := by gcongr; linarith
      _ ≤ _ := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
  · have hn : ‖x‖ ^ m * ‖F i x‖ ≤ C₁ := by
      have h := SchwartzMap.le_seminorm ℝ m 0 (F i) x
      simpa only [norm_iteratedFDeriv_zero] using
        h.trans (hb₁ (F i) (mem_range_self i)).le
    calc
      _ ≤ ‖F i x‖ * (2 * ‖x‖) ^ m := by gcongr; linarith
      _ = 2 ^ m * (‖x‖ ^ m * ‖F i x‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ m * C₁ := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]

/-- Actual weighted first norms are uniformly bounded for every bounded Schwartz family. -/
theorem exists_uniform_schwartz_moment {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ)
    (hF : IsVonNBounded ℝ (range F)) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i, (∫ x, ‖x‖ ^ m * ‖F i x‖) ≤ C := by
  have hp := (schwartz_withSeminorms ℝ _ _).isVonNBounded_iff_seminorm_bounded.mp hF
  obtain ⟨C₀, hC₀, hb₀⟩ := hp (0, 0)
  obtain ⟨C₁, hC₁, hb₁⟩ :=
    hp (m + (volume : Measure (EuclideanSpace ℝ (Fin 2))).integrablePower, 0)
  let D := 2 ^ (volume : Measure (EuclideanSpace ℝ (Fin 2))).integrablePower *
    ∫ x : EuclideanSpace ℝ (Fin 2),
      (1 + ‖x‖) ^ (-(volume : Measure (EuclideanSpace ℝ (Fin 2))).integrablePower : ℝ)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D * (C₀ + C₁) + 1, by positivity, ?_⟩
  intro i
  have h := (F i).integral_pow_mul_iteratedFDeriv_le ℝ volume m 0
  simp only [norm_iteratedFDeriv_zero] at h
  apply (h.trans ?_).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
  exact mul_le_mul_of_nonneg_left
    (add_le_add (hb₀ (F i) (mem_range_self i)).le (hb₁ (F i) (mem_range_self i)).le) hD

/-- Uniform actual symbol derivatives produce both actual inverse-kernel estimates. -/
theorem exists_uniform_fourierInv_bounds_of_derivatives {ι : Type*}
    (F : ι → SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (R : ℝ)
    (hs : ∀ i, tsupport (F i) ⊆ closedBall 0 R)
    (hd : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, ‖iteratedFDeriv ℝ n (F i) x‖ ≤ C)
    (m : ℕ) :
    (∃ C : ℝ, 0 < C ∧ ∀ i x,
      ‖(𝓕⁻ (F i) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖ ≤
        C / (1 + ‖x‖) ^ m) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ i,
      (∫ x, ‖x‖ ^ m * ‖(𝓕⁻ (F i) : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) x‖) ≤ C) := by
  have h := isVonNBounded_fourierInv_range F
    (isVonNBounded_schwartz_range_of_derivatives F R hs hd)
  exact ⟨exists_uniform_schwartz_decay _ h m, exists_uniform_schwartz_moment _ h m⟩

end FalconerPacking
