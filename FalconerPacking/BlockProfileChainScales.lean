/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ProfileChainPhysicalScales

/-!
# Block profiles at their actual spatial scales

Regularized profiles use block indices. Their actual dyadic depths are multiplied by the
block size, while angular depths use one fixed upper frequency for the entire annulus.
-/

noncomputable section

namespace FalconerPacking

/-- Multiplication by the block size preserves the exact admissibility inequality. -/
theorem Admissible.mul_block {N m n : ℕ} (h : Admissible N m n) (T : ℕ) :
    Admissible (T * N) (T * m) (T * n) := by
  have hh := Nat.mul_le_mul_left T h
  simpa only [Admissible, Nat.mul_add, show T * (2 * n) = 2 * (T * n) by ring] using hh

/-- The angular depth follows the preceding actual spatial depth, with zero initial depth. -/
def blockProfileChainAngle (F T n : ℕ) (l : List ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => F - T * profileChainDepth n l j

/-- Block scaling gives the actual global sequences and keeps the exact original cost. -/
theorem blockProfileChain_scales {N F T n s : ℕ} {l : List ℕ}
    (hNF : T * N ≤ F) (hn : n ≤ N)
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l))
    (hend : chainEnd n l = 0)
    (hs : Real.sqrt ((2 : ℝ) ^ (T * N)) ≤ (2 : ℝ) ^ s) :
    let d := fun j ↦ T * profileChainDepth n l j
    let e := blockProfileChainAngle F T n l
    Antitone d ∧ Monotone e ∧ d 0 = T * n ∧ d l.length = 0 ∧ e 0 = 0 ∧
      (∀ j, d j ≤ T * N ∧ e j ≤ F) ∧
      (∀ j, j < l.length →
        let a := ((2 : ℝ) ^ d j)⁻¹
        let b := ((2 : ℝ) ^ d (j + 1))⁻¹
        0 < a ∧ a ≤ b ∧ b ≤ 1 ∧ b ≤ (2 : ℝ) ^ F * a ^ 2 ∧
          (2 : ℝ) ^ e (j + 1) = (2 : ℝ) ^ F * a ∧
          ((2 : ℝ) ^ s)⁻¹ ≤ a / b) := by
  dsimp only
  have hl' : List.IsChain (fun n m ↦ m < n) (n :: l) :=
    hl.imp (fun _ _ h ↦ h.1)
  have hd : Antitone (fun j ↦ T * profileChainDepth n l j) :=
    fun i j hij ↦ Nat.mul_le_mul_left T (antitone_profileChainDepth hl' hij)
  have he : Monotone (blockProfileChainAngle F T n l) := by
    apply monotone_nat_of_le_succ
    intro j
    cases j with
    | zero => exact Nat.zero_le _
    | succ j => exact Nat.sub_le_sub_left (hd (Nat.le_succ j)) F
  have hdN (j : ℕ) : T * profileChainDepth n l j ≤ T * N :=
    Nat.mul_le_mul_left T ((profileChainDepth_le_initial hl' j).trans hn)
  refine ⟨hd, he, rfl, ?_, rfl, ?_, ?_⟩
  · rw [profileChainDepth_length, hend, Nat.mul_zero]
  · intro j
    refine ⟨hdN j, ?_⟩
    cases j with
    | zero => exact Nat.zero_le _
    | succ j => exact Nat.sub_le _ _
  · intro j hj
    have hc := (profileChainDepth_edge hl hj).2.mul_block T
    have hb₁ : ((2 : ℝ) ^ (T * profileChainDepth n l (j + 1)))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    refine ⟨by positivity, ?_, hb₁, admissible_dyadic_curvature_of_le hNF hc, ?_, ?_⟩
    · exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
        (pow_le_pow_right₀ (by norm_num) (hd (Nat.le_succ j)))
    · exact pow_sub₀ 2 (by norm_num) ((hdN j).trans hNF)
    · exact standard_angle_le_spatial_ratio (by positivity) (by positivity) (by positivity)
        hb₁ (admissible_dyadic_curvature hc) hs

end FalconerPacking
