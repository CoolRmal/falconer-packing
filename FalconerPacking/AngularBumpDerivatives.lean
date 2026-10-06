/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SmoothAngularCaps

/-!+# Uniform derivatives of the actual angular covering bumps

The bumps used in the angular partition are translates and dilates of one fixed compact smooth
function. Their derivative constants therefore depend only on the derivative order, rather than
on the angular grid or cap index. No rotational invariance of the chosen bump is required.
-/

@[expose] public section

noncomputable section

open Set Metric SchwartzMap Classical
open scoped ContDiff

namespace FalconerPacking

/-- The fixed bump underlying every angular covering bump. -/
def angularUnitBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin 2)) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The fixed bump bundled as a real Schwartz function. -/
def angularUnitSchwartz : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ :=
  angularUnitBump.hasCompactSupport.toSchwartzMap angularUnitBump.contDiff

/-- The actual grid bumps use precisely the same fixed profile. -/
theorem angularCapBump_eq_unit (N : ℕ) (hN : 0 < N) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    angularCapBump N hN j x = angularUnitSchwartz
      ((2 * Real.pi / N)⁻¹ • (x - angularDirection (angularGridPoint N j))) := by
  have hδ : 2 * Real.pi / (N : ℝ) ≠ 0 := by positivity
  simp only [ContDiffBump.apply, angularCapBump, angularUnitSchwartz,
    HasCompactSupport.toSchwartzMap_toFun, angularUnitBump, sub_zero,
    inv_one, one_smul, div_one]
  congr 2
  field_simp

/-- A fixed Schwartz function has scale-uniform bounds after scalar dilation and translation. -/
theorem norm_iteratedFDeriv_schwartz_dilate_translate_le
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (m : ℕ) (a : ℝ)
    (c x : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f (a • (y - c))) x‖ ≤
      SchwartzMap.seminorm ℝ 0 m f * |a| ^ m := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    a • ContinuousLinearMap.id ℝ _
  have hfun : (fun y ↦ f (a • (y - c))) = fun y ↦ (f ∘ L) (y - c) := rfl
  rw [hfun, iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right (f.smooth ⊤)
    _ (mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ m f (L (x - c))‖ * ‖L‖ ^ m := by
      simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ m f (L (x - c))) (fun _ ↦ L)
    _ ≤ SchwartzMap.seminorm ℝ 0 m f * |a| ^ m := by
      simpa [L, norm_smul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (f.norm_iteratedFDeriv_le_seminorm ℝ m (L (x - c)))
          (pow_nonneg (norm_nonneg L) m)

/-- All derivatives of the constructed angular bumps have their natural scale bound. -/
theorem angularCapBump_derivative_bound (m : ℕ) :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N) (j : ℕ) (x : EuclideanSpace ℝ (Fin 2)),
      ‖iteratedFDeriv ℝ m (angularCapBump N hN j) x‖ ≤
        C * ((2 * Real.pi / N)⁻¹) ^ m := by
  refine ⟨SchwartzMap.seminorm ℝ 0 m angularUnitSchwartz + 1,
    by positivity, ?_⟩
  intro N hN j x
  have hfun : (angularCapBump N hN j : EuclideanSpace ℝ (Fin 2) → ℝ) =
      fun y ↦ angularUnitSchwartz
        ((2 * Real.pi / N)⁻¹ • (y - angularDirection (angularGridPoint N j))) :=
    funext (angularCapBump_eq_unit N hN j)
  rw [hfun]
  exact (norm_iteratedFDeriv_schwartz_dilate_translate_le _ m _ _ x).trans (by
    rw [abs_of_nonneg (by positivity : 0 ≤ (2 * Real.pi / (N : ℝ))⁻¹)]
    gcongr
    linarith)

/-- Derivatives of any order retain the same bounded cap overlap. -/
theorem card_angularCapBump_derivative_support_le (m N : ℕ) (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin 2)) :
    ((Finset.range N).filter (fun j ↦
      iteratedFDeriv ℝ m (angularCapBump N hN j) x ≠ 0)).card ≤
        Nat.ceil (8 * Real.pi) := by
  have h := card_circle_grid_balls_le N hN (r := 1) (C := 6 * Real.pi)
    (by norm_num) (by positivity) x
  have hc : 6 * Real.pi + 2 * Real.pi = 8 * Real.pi := by ring
  rw [hc] at h
  apply (Finset.card_le_card ?_).trans h
  intro j hj
  obtain ⟨hjN, hjd⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨hjN, ?_⟩
  have hs := support_iteratedFDeriv_subset m hjd
  rw [ContDiffBump.tsupport_eq] at hs
  simp only [mem_closedBall, angularCapBump] at hs
  simp only [one_smul, mul_one, mem_ball]
  have hδ : 0 < 2 * Real.pi / (N : ℝ) := by positivity
  have he : 6 * Real.pi / (N : ℝ) = 3 * (2 * Real.pi / (N : ℝ)) := by ring
  rw [he]
  linarith

/-- The unnormalized denominator in the ambient plane. -/
def angularAmbientDenominator (N : ℕ) (hN : 0 < N)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ j ∈ Finset.range N, angularCapBump N hN j x

/-- Bounded overlap prevents the denominator's derivative constants from growing with `N`. -/
theorem angularAmbientDenominator_derivative_bound (m : ℕ) :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N) (x : EuclideanSpace ℝ (Fin 2)),
      ‖iteratedFDeriv ℝ m (angularAmbientDenominator N hN) x‖ ≤
        C * ((2 * Real.pi / N)⁻¹) ^ m := by
  obtain ⟨C, hC, hbound⟩ := angularCapBump_derivative_bound m
  refine ⟨((Nat.ceil (8 * Real.pi) : ℝ) + 1) * C, by positivity, ?_⟩
  intro N hN x
  change ‖iteratedFDeriv ℝ m (fun y ↦ ∑ j ∈ Finset.range N,
    angularCapBump N hN j y) x‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply
    (fun j _ ↦ (angularCapBump N hN j).contDiffAt)]
  let J := (Finset.range N).filter (fun j ↦
    iteratedFDeriv ℝ m (angularCapBump N hN j) x ≠ 0)
  have hsum : ∑ j ∈ Finset.range N, iteratedFDeriv ℝ m (angularCapBump N hN j) x =
      ∑ j ∈ J, iteratedFDeriv ℝ m (angularCapBump N hN j) x := by
    symm
    exact Finset.sum_filter_ne_zero _
  rw [hsum]
  calc
    _ ≤ ∑ j ∈ J, ‖iteratedFDeriv ℝ m (angularCapBump N hN j) x‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ J, C * ((2 * Real.pi / (N : ℝ))⁻¹) ^ m :=
      Finset.sum_le_sum (fun j _ ↦ hbound N hN j x)
    _ = (J.card : ℝ) * (C * ((2 * Real.pi / (N : ℝ))⁻¹) ^ m) := by simp
    _ ≤ _ := by
      have hj : (J.card : ℝ) ≤ Nat.ceil (8 * Real.pi) := by
        exact_mod_cast card_angularCapBump_derivative_support_le m N hN x
      have hc : 0 ≤ C * ((2 * Real.pi / (N : ℝ))⁻¹) ^ m := by positivity
      nlinarith

/-- Scalar rescaling and translation multiply the derivative bound by the expected power. -/
theorem norm_iteratedFDeriv_dilate_add_le
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} (hf : ContDiff ℝ ∞ f)
    (m : ℕ) (a : ℝ) (c x : EuclideanSpace ℝ (Fin 2)) :
    ‖iteratedFDeriv ℝ m (fun y ↦ f (a • y + c)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (a • x + c)‖ * |a| ^ m := by
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    a • ContinuousLinearMap.id ℝ _
  have hfc : ContDiff ℝ ∞ (fun y ↦ f (y + c)) :=
    hf.comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ m ((fun y ↦ f (y + c)) ∘ L) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_right hfc _ (mod_cast le_top), iteratedFDeriv_comp_add_right]
  simpa [L, norm_smul, Real.norm_eq_abs] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ m f (L x + c)) (fun _ ↦ L)

/-- In bump-scale coordinates, the actual denominator has bounded derivatives of every order. -/
theorem angularAmbientDenominator_rescaled_derivative_bound (m : ℕ) :
    ∃ C > 0, ∀ (N : ℕ) (hN : 0 < N) (c x : EuclideanSpace ℝ (Fin 2)),
      ‖iteratedFDeriv ℝ m
        (fun y ↦ angularAmbientDenominator N hN ((2 * Real.pi / N) • y + c)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := angularAmbientDenominator_derivative_bound m
  refine ⟨C, hC, ?_⟩
  intro N hN c x
  have hδ : 0 < 2 * Real.pi / (N : ℝ) := by positivity
  have hf : ContDiff ℝ ∞ (angularAmbientDenominator N hN) :=
    ContDiff.sum (fun j _ ↦ (angularCapBump N hN j).contDiff)
  calc
    _ ≤ ‖iteratedFDeriv ℝ m (angularAmbientDenominator N hN)
        ((2 * Real.pi / N) • x + c)‖ * |2 * Real.pi / N| ^ m :=
      norm_iteratedFDeriv_dilate_add_le hf m _ c x
    _ ≤ (C * ((2 * Real.pi / (N : ℝ))⁻¹) ^ m) * |2 * Real.pi / N| ^ m :=
      mul_le_mul_of_nonneg_right (hbound N hN _) (pow_nonneg (abs_nonneg _) m)
    _ = C := by
      rw [abs_of_pos hδ, mul_assoc, ← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow, mul_one]

end FalconerPacking
