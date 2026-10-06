/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!+# Pointwise derivative bounds for locally smooth compositions

These versions of the derivative estimates require smoothness only near the evaluation point.
They allow the direction chart to be used on its natural half-space.
-/

@[expose] public section

noncomputable section

open Set Function
open scoped ContDiff

namespace FalconerPacking

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The composition estimate remains valid when the inner map is only locally smooth. -/
theorem norm_iteratedFDeriv_comp_le_at {f : F → G} {g : E → F} {x : E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) {C D : ℝ}
    (hC : ∀ k ≤ m, ‖iteratedFDeriv ℝ k f (g x)‖ ≤ C)
    (hD : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv ℝ k g x‖ ≤ D ^ k) :
    ‖iteratedFDeriv ℝ m (f ∘ g) x‖ ≤ m.factorial * C * D ^ m := by
  obtain ⟨U, hU, hx, hgU⟩ := hg.contDiffOn' (m := m) (mod_cast le_top) (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hgU
  have h := norm_iteratedFDerivWithin_comp_le
    ((hf.of_le (m := m) (mod_cast le_top)).contDiffOn)
    hgU (by rfl) uniqueDiffOn_univ hU.uniqueDiffOn (mapsTo_univ _ _) hx
    (C := C) (D := D) ?_ ?_
  · rwa [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hf.contDiffAt.comp x hg).of_le (mod_cast le_top)) hx] at h
  · intro k hk
    simpa only [iteratedFDerivWithin_univ] using hC k hk
  · intro k hk hkm
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (hg.of_le (mod_cast le_top)) hx]
    exact hD k hk hkm

/-- Restriction along a continuous linear map has its exact operator-norm derivative bound. -/
theorem norm_iteratedFDeriv_comp_linear_le_at (L : E →L[ℝ] F) {f : F → G} {x : E}
    (hf : ContDiffAt ℝ ∞ f (L x)) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ m f (L x)‖ * ‖L‖ ^ m := by
  obtain ⟨U, hU, hx, hfU⟩ := hf.contDiffOn' (m := m) (mod_cast le_top) (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hfU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfU hU.uniqueDiffOn hpre.uniqueDiffOn hx
    (i := m) (by rfl)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn
    ((hf.comp x L.contDiff.contDiffAt).of_le (mod_cast le_top)) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (hf.of_le (mod_cast le_top)) hx] at he
  rw [he]
  simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ m f (L x)) (fun _ ↦ L)

/-- Fixing a parameter can only decrease the norm of a derivative. -/
theorem norm_iteratedFDeriv_fix_parameter_le_at {f : ℝ × E → F} (ε : ℝ) {x : E}
    (hf : ContDiffAt ℝ ∞ f (ε, x)) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f (ε, y)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (ε, x)‖ := by
  let L := ContinuousLinearMap.inr ℝ ℝ E
  let g (p : ℝ × E) := f (p + (ε, 0))
  have he : L x + (ε, 0) = (ε, x) := by simp [L]
  have hg : ContDiffAt ℝ ∞ g (L x) := by
    exact (show ContDiffAt ℝ ∞ f (L x + (ε, 0)) from he.symm ▸ hf).comp (L x)
      (contDiffAt_id.add contDiffAt_const)
  have h := norm_iteratedFDeriv_comp_linear_le_at L hg m
  have hfun : (fun y ↦ f (ε, y)) = g ∘ L := by ext y; simp [g, L]
  rw [← hfun] at h
  have hnorm : ‖L‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ E
  apply h.trans
  rw [show g = fun p ↦ f (p + (ε, 0)) from rfl, iteratedFDeriv_comp_add_right, he]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg L) hnorm)

/-- The pointwise Leibniz bound needs only local smoothness of its two factors. -/
theorem norm_iteratedFDeriv_smul_le_at {f : E → ℝ} {g : E → F} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f y • g y) x‖ ≤
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ‖iteratedFDeriv ℝ k f x‖ *
        ‖iteratedFDeriv ℝ (m - k) g x‖ := by
  obtain ⟨U, hU, hx, hfgU⟩ := (hf.prodMk hg).contDiffOn'
    (m := m) (mod_cast le_top) (by simp)
  simp only [insert_eq_of_mem (mem_univ _), univ_inter] at hfgU
  have h := norm_iteratedFDerivWithin_smul_le hfgU.fst hfgU.snd hU.uniqueDiffOn hx
    (n := m) (by rfl)
  dsimp only at h
  have hfg : ContDiffAt ℝ m (fun y ↦ f y • g y) x :=
    (hf.smul hg).of_le (mod_cast le_top)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hfg hx] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
    (hf.of_le (mod_cast le_top)) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hx]

end FalconerPacking
