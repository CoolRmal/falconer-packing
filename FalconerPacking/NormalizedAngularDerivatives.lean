/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.AngularBumpDerivatives
public import FalconerPacking.RegularizedReciprocal
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!+# Uniform derivatives of normalized angular bumps

A fixed smooth reciprocal extends the normalization away from the unit circle. After rescaling by
the cap width, every derivative of this actual extension is uniformly bounded. Bounded overlap,
rather than the number of caps, controls the denominator.
-/

@[expose] public section

noncomputable section

open Set Metric Filter SchwartzMap Classical
open scoped ContDiff Topology

namespace FalconerPacking

private theorem uniform_derivative_mul {ι : Type*}
    {f g : ι → EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ∀ i, ContDiff ℝ ∞ (g i))
    (hfb : ∀ m, ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C)
    (hgb : ∀ m, ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ m (g i) x‖ ≤ C) (m : ℕ) :
    ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ m (fun y ↦ f i y * g i y) x‖ ≤ C := by
  choose F hF hFb using hfb
  choose G hG hGb using hgb
  let C := ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * F k * G (m - k)
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ ↦
    mul_nonneg (mul_nonneg (by positivity) (hF k).le) (hG (m - k)).le)
  refine ⟨C + 1, by positivity, ?_⟩
  intro i x
  apply (norm_iteratedFDeriv_mul_le (hf i) (hg i) x (mod_cast le_top)).trans
  apply le_trans (Finset.sum_le_sum fun k _ ↦ ?_) (show C ≤ C + 1 by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb k i x) (by positivity))
    (hGb (m - k) i x) (norm_nonneg _) (mul_nonneg (by positivity) (hF k).le)

private theorem uniform_derivative_reciprocal {ι : Type*}
    {f : ι → EuclideanSpace ℝ (Fin 2) → ℝ}
    (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hfb : ∀ m, ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ m (f i) x‖ ≤ C) (m : ℕ) :
    ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ m
      (fun y ↦ scaledRegularizedReciprocal (1 / 2) (f i y)) x‖ ≤ C := by
  choose F hF hFb using hfb
  let D := 1 + ∑ k ∈ Finset.range (m + 1), F k
  have hD : 1 ≤ D := by
    have hs : 0 ≤ ∑ k ∈ Finset.range (m + 1), F k :=
      Finset.sum_nonneg (fun k _ ↦ (hF k).le)
    dsimp [D]
    linarith
  have hFD (k : ℕ) (hk : k ≤ m) : F k ≤ D := by
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (m + 1)) ↦ (hF j).le)
      (show k ∈ Finset.range (m + 1) by simpa using Nat.lt_succ_of_le hk)
    dsimp [D]
    linarith
  let B := regularizedReciprocalOrderBound m * (2 : ℝ) ^ (m + 1)
  have hB : 0 < B := mul_pos (regularizedReciprocalOrderBound_pos m) (by positivity)
  refine ⟨m.factorial * B * D ^ m + 1, by positivity, ?_⟩
  intro i x
  have he := norm_iteratedFDeriv_comp_le
    (contDiff_scaledRegularizedReciprocal (1 / 2)) (hf i)
    (n := m) (mod_cast le_top) x (C := B) (D := D) ?_ ?_
  · exact he.trans (by linarith)
  · intro k hk
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    apply (norm_iteratedDeriv_scaledRegularizedReciprocal_le_orderBound
      (by norm_num : (0 : ℝ) < 1 / 2) hk (f i x)).trans
    dsimp [B]
    norm_num only [one_div, inv_inv]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right hk 1))
      (regularizedReciprocalOrderBound_pos m).le
  · intro k hk hkm
    exact (hFb k i x).trans ((hFD k hkm).trans (le_self_pow₀ hD (by omega)))

/-- A globally smooth ambient extension of the actual normalized angular weight. -/
def normalizedAngularAmbientWeight (N : ℕ) (hN : 0 < N) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  angularCapBump N hN j x *
    scaledRegularizedReciprocal (1 / 2) (angularAmbientDenominator N hN x)

theorem contDiff_normalizedAngularAmbientWeight (N : ℕ) (hN : 0 < N) (j : ℕ) :
    ContDiff ℝ ∞ (normalizedAngularAmbientWeight N hN j) :=
  (angularCapBump N hN j).contDiff.mul
    ((contDiff_scaledRegularizedReciprocal _).comp
      (ContDiff.sum fun k _ ↦ (angularCapBump N hN k).contDiff))

/-- On actual directions, the smooth ambient extension equals the original normalized weight. -/
theorem normalizedAngularAmbientWeight_direction (N : ℕ) (hN : 0 < N) (j : ℕ)
    {ξ : EuclideanSpace ℝ (Fin 2)} (hξ : ξ ≠ 0) :
    normalizedAngularAmbientWeight N hN j (‖ξ‖⁻¹ • ξ) = angularCapWeight N hN j ξ := by
  have hd := one_le_angularCapDenominator N hN hξ
  have he : angularAmbientDenominator N hN (‖ξ‖⁻¹ • ξ) =
      angularCapDenominator N hN ξ := rfl
  simp only [normalizedAngularAmbientWeight, he]
  rw [scaledRegularizedReciprocal_eq_inv (by norm_num)]
  · rfl
  · exact le_trans (by norm_num : (1 / 2 : ℝ) ≤ 1) (hd.trans (le_abs_self _))

/-- The actual normalized extension has uniform derivatives in cap-width coordinates. -/
theorem normalizedAngularAmbientWeight_rescaled_derivative_bound (m : ℕ) :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N) (j : ℕ) (c x : EuclideanSpace ℝ (Fin 2)),
      ‖iteratedFDeriv ℝ m
        (fun y ↦ normalizedAngularAmbientWeight N hN j
          ((2 * Real.pi / N) • y + c)) x‖ ≤ C := by
  let f (i : ℕ+ × ℕ × EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)) :=
    angularCapBump i.1 i.1.pos i.2.1 ((2 * Real.pi / i.1) • x + i.2.2)
  let g (i : ℕ+ × ℕ × EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 2)) :=
    angularAmbientDenominator i.1 i.1.pos ((2 * Real.pi / i.1) • x + i.2.2)
  have hf (i) : ContDiff ℝ ∞ (f i) :=
    (angularCapBump i.1 i.1.pos i.2.1).contDiff.comp
      ((contDiff_const_smul (2 * Real.pi / (i.1 : ℝ))).add contDiff_const)
  have hg (i) : ContDiff ℝ ∞ (g i) :=
    (ContDiff.sum (fun k _ ↦ (angularCapBump i.1 i.1.pos k).contDiff)).comp
      ((contDiff_const_smul (2 * Real.pi / (i.1 : ℝ))).add contDiff_const)
  have hfb (k : ℕ) : ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C := by
    obtain ⟨C, hC, hbound⟩ := angularCapBump_derivative_bound k
    refine ⟨C, hC, ?_⟩
    intro i x
    have hδ : 0 < 2 * Real.pi / (i.1 : ℝ) := by positivity
    apply (norm_iteratedFDeriv_dilate_add_le (angularCapBump i.1 i.1.pos i.2.1).contDiff
      k _ i.2.2 x).trans
    apply le_trans (mul_le_mul_of_nonneg_right (hbound i.1 i.1.pos i.2.1 _)
      (pow_nonneg (abs_nonneg _) k))
    rw [abs_of_pos hδ, mul_assoc, ← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow, mul_one]
  have hgb (k : ℕ) : ∃ C > 0, ∀ i x, ‖iteratedFDeriv ℝ k (g i) x‖ ≤ C := by
    obtain ⟨C, hC, hbound⟩ := angularAmbientDenominator_rescaled_derivative_bound k
    exact ⟨C, hC, fun i x ↦ hbound i.1 i.1.pos i.2.2 x⟩
  obtain ⟨C, hC, hbound⟩ := uniform_derivative_mul hf
    (fun i ↦ (contDiff_scaledRegularizedReciprocal _).comp (hg i)) hfb
    (uniform_derivative_reciprocal hg hgb) m
  exact ⟨C, hC, fun N hN j c x ↦ hbound (⟨N, hN⟩, j, c) x⟩

end FalconerPacking
