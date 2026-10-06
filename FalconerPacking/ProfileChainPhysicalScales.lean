/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ProfileChainSequences
public import FalconerPacking.PhysicalChainScales

/-!
# Actual dyadic scales of the finite profile chain

The profile admissibility inequality gives the physical curvature inequality. Auxiliary
angular depths use a possibly larger frequency depth, without changing the profile costs.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- Integer admissibility is exactly the required curvature inequality of dyadic scales. -/
theorem admissible_dyadic_curvature {N m n : ℕ} (h : Admissible N m n) :
    ((2 : ℝ) ^ m)⁻¹ ≤ (2 : ℝ) ^ N * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  have hp : (2 : ℝ) ^ (2 * n) ≤ 2 ^ (N + m) :=
    pow_le_pow_right₀ (by norm_num) h
  rw [pow_add, Nat.mul_comm 2 n, pow_mul] at hp
  rw [inv_pow, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [one_mul, mul_comm] using hp

/-- Larger frequencies preserve curvature, even though the chain was built at the base depth. -/
theorem admissible_dyadic_curvature_of_le {N F m n : ℕ} (hNF : N ≤ F)
    (h : Admissible N m n) :
    ((2 : ℝ) ^ m)⁻¹ ≤ (2 : ℝ) ^ F * (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
  exact (admissible_dyadic_curvature h).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNF) (sq_nonneg _))

/-- The selected angular cardinality equals frequency times child side length exactly. -/
theorem profileChainAngle_cardinality {N n : ℕ} {l : List ℕ} (hn : n ≤ N)
    (hl : List.IsChain (fun n m ↦ m < n) (n :: l)) (j : ℕ) :
    (2 : ℝ) ^ profileChainAngle N n l (j + 1) =
      (2 : ℝ) ^ N * ((2 : ℝ) ^ profileChainDepth n l j)⁻¹ := by
  have hd : profileChainDepth n l j ≤ N := (profileChainDepth_le_initial hl j).trans hn
  change (2 : ℝ) ^ (N - profileChainDepth n l j) = _
  exact pow_sub₀ 2 (by norm_num) hd

/-- The usual ceiling half-depth is a valid standard angular resolution. -/
theorem sqrt_dyadic_le_half_depth (N : ℕ) :
    Real.sqrt ((2 : ℝ) ^ N) ≤ (2 : ℝ) ^ ((N + 1) / 2) := by
  rw [Real.sqrt_le_left (by positivity), ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- Every genuine edge of the constructed profile has all physical scale comparisons.
The standard angular grid only needs to resolve the base frequency, including when the
chosen auxiliary frequency is larger. -/
theorem profileChain_physical_scales {N F n s : ℕ} {l : List ℕ}
    (hNF : N ≤ F) (hn : n ≤ N)
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l))
    (hs : Real.sqrt ((2 : ℝ) ^ N) ≤ (2 : ℝ) ^ s)
    {j : ℕ} (hj : j < l.length) :
    let a := ((2 : ℝ) ^ profileChainDepth n l j)⁻¹
    let b := ((2 : ℝ) ^ profileChainDepth n l (j + 1))⁻¹
    0 < a ∧ a ≤ b ∧ b ≤ 1 ∧ b ≤ (2 : ℝ) ^ F * a ^ 2 ∧
      (2 : ℝ) ^ profileChainAngle F n l (j + 1) = (2 : ℝ) ^ F * a ∧
      ((2 : ℝ) ^ s)⁻¹ ≤ a / b := by
  dsimp only
  have hl' : List.IsChain (fun n m ↦ m < n) (n :: l) :=
    hl.imp (fun _ _ h ↦ h.1)
  obtain ⟨hdec, hcurv⟩ := profileChainDepth_edge hl hj
  have hb : 0 < ((2 : ℝ) ^ profileChainDepth n l (j + 1))⁻¹ := by positivity
  have hb₁ : ((2 : ℝ) ^ profileChainDepth n l (j + 1))⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  refine ⟨by positivity, ?_, hb₁, admissible_dyadic_curvature_of_le hNF hcurv,
    profileChainAngle_cardinality (hn.trans hNF) hl' j, ?_⟩
  · exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) hdec.le)
  · exact standard_angle_le_spatial_ratio (by positivity) (by positivity) hb hb₁
      (admissible_dyadic_curvature hcurv) hs

end FalconerPacking
