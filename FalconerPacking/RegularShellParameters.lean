/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RegularPartitionInitialLoss
public import FalconerPacking.PaddedChainDecay
public import FalconerPacking.AnnularScaleSchedule

/-!
# Compatible scalar choices for the actual regularized shells

The strict profile margin is fixed first. The angular integer and both heavy thresholds
are chosen before the regularization block; any sufficiently large block then works.
The later derivative orders may exceed arbitrary prescribed lower bounds. All comparisons
refer to the complete shell schedule, whose packet parameter is the product `J * T`.
-/

@[expose] public section

noncomputable section

open Filter

namespace FalconerPacking

/-- One ordered choice supplies the actual source and pin deletion exponents, the complete
finite-chain loss budget, and the remaining initial-localization and normalization margin.
The block size is universally quantified after its minimum is fixed. -/
theorem exists_regular_shell_parameters {η q ε : ℝ}
    (hη : 0 < η) (hq : 1 < q) (hε : 0 < ε) (K : ℕ) :
    let A : ℝ := 28 * K + 114
    ∃ (J : ℕ) (D₁ D₂ h ρ : ℝ) (T₀ : ℕ),
      4 ≤ J ∧ h = 1 / (4 * J) ∧ 0 < D₁ ∧ 0 < D₂ ∧
      0 < h ∧ h ≤ 1 / 16 ∧ 0 < ρ ∧ ρ ≤ ε / 2 ∧ ρ ≤ η / 16 ∧
      4 * A * ρ ≤ h ∧ 4 * h ≤ η / 8 ∧
      (A - (q - 1) * D₁) * h + A * ρ ≤ -2 * h ∧
      (A + D₁ - D₂) * h + A * ρ ≤ -2 * h ∧
      A - (q - 1) * D₁ + A * ρ / h ≤ -2 ∧
      A + D₁ - D₂ + A * ρ / h ≤ -2 ∧
      2 ≤ T₀ ∧
      (∀ T : ℕ, T₀ ≤ T →
        (K : ℝ) * ((28 * K + 114) * h + D₂ * h) * T + 3 * K ≤ η * T / 4) ∧
      (∀ ζ : ℝ, 2 * ζ ≤ η / 8 →
        4 * h + 2 * ζ + ρ - η / 2 ≤ -η / 8) := by
  dsimp only
  let A : ℝ := 28 * K + 114
  have hA : 1 ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hA₀ : 0 < A := lt_of_lt_of_le zero_lt_one hA
  obtain ⟨J, hJ, D₁, D₂, h, ρ₀, hhdef, hD₁, hD₂, hh, hhsmall,
    hρ₀, hρ₀ε, hρ₀h, hbudget, hbad₁, hbad₂, _⟩ :=
    exists_shell_threshold_parameters hη hq hA (show (0 : ℝ) ≤ 0 by norm_num)
      (half_pos hε) K
  let ρ := min ρ₀ (η / 16)
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρle : ρ ≤ ρ₀ := min_le_left _ _
  have hρmul : A * ρ ≤ A * ρ₀ := mul_le_mul_of_nonneg_left hρle hA₀.le
  have hnonneg : 0 ≤ A * ((K : ℝ) + 1) * ρ₀ := by positivity
  have hsum : (A + (K : ℝ) * (A + D₂)) * h ≤ η / 8 := by linarith
  have hKh : 0 ≤ (K : ℝ) * (A + D₂) * h := by positivity
  have hAh : A * h ≤ η / 8 := by nlinarith
  have hsmall : 4 * h ≤ η / 8 := by
    have hA₄ : 4 ≤ A := by dsimp [A]; linarith [Nat.cast_nonneg (α := ℝ) K]
    nlinarith
  have hchain : (K : ℝ) * ((28 * K + 114) * h + D₂ * h) ≤ η / 8 := by
    change (K : ℝ) * (A * h + D₂ * h) ≤ _
    nlinarith
  obtain ⟨T₀, hT₀⟩ := exists_nat_gt (max 2 (24 * (K : ℝ) / η))
  have hT₀₂ : 2 ≤ T₀ := by
    exact_mod_cast ((le_max_left _ _).trans_lt hT₀).le
  have hT₀loss : 24 * (K : ℝ) ≤ η * T₀ := by
    have h := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hT₀)
    nlinarith
  refine ⟨J, D₁, D₂, h, ρ, T₀, hJ, hhdef, hD₁, hD₂, hh, hhsmall, hρ,
    hρle.trans hρ₀ε, min_le_right _ _, ?_, hsmall, ?_, ?_, ?_, ?_, hT₀₂, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hρle (by positivity)).trans hρ₀h
  · linarith
  · linarith
  · apply (mul_le_mul_iff_of_pos_right hh).mp
    have he : (A - (q - 1) * D₁ + A * ρ / h) * h =
        (A - (q - 1) * D₁) * h + A * ρ := by field_simp
    nlinarith [he]
  · apply (mul_le_mul_iff_of_pos_right hh).mp
    have he : (A + D₁ - D₂ + A * ρ / h) * h =
        (A + D₁ - D₂) * h + A * ρ := by field_simp
    nlinarith [he]
  · intro T hT
    have hT' : (T₀ : ℝ) ≤ T := by exact_mod_cast hT
    have hlarge : 24 * (K : ℝ) ≤ η * T :=
      hT₀loss.trans (mul_le_mul_of_nonneg_left hT' hη.le)
    have hc := mul_le_mul_of_nonneg_right hchain (Nat.cast_nonneg T)
    nlinarith
  · intro ζ hζ
    have hρη : ρ ≤ η / 16 := min_le_right _ _
    linarith

/-- After fixing the actual block, all derivative and reconstruction orders can be made
simultaneously large. The reconstruction inequality uses `J * T`, so it applies to every
shell of the complete annular family rather than to a subsequence. -/
theorem exists_regular_shell_decay_orders {h ρ A D₂ P : ℝ}
    (hh : 0 < h) (K J T p₀ m₀ q₀ : ℕ) :
    ∃ pwr m tail : ℕ, p₀ ≤ pwr ∧ m₀ ≤ m ∧ q₀ ≤ tail ∧
      pwr + 4 * K + 20 ≤ m ∧ pwr ≤ 2 * m ∧
      2 + h * ((4 * K + 8 : ℕ) - (pwr : ℝ)) < 0 ∧
      P + K * (1 + (A + D₂) * h + A * ρ) + 4 - pwr * h < -2 ∧
      (∀ s ζ : ℝ, 1 ≤ s → 0 ≤ ζ → 3 - s - m * (2 * h + ζ) ≤ -1) ∧
      (8 * (J * T) : ℝ) - 2 * tail ≤ -1 := by
  obtain ⟨pwr, hpwr⟩ := exists_nat_gt (max (p₀ : ℝ)
    (max ((2 + h * (4 * K + 8)) / h)
      ((P + K * (1 + (A + D₂) * h + A * ρ) + 6) / h)))
  have hp₀ : p₀ ≤ pwr := by exact_mod_cast ((le_max_left _ _).trans_lt hpwr).le
  have hp₁ := (div_lt_iff₀ hh).mp
    (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hpwr)
  have hp₂ := (div_lt_iff₀ hh).mp
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hpwr)
  obtain ⟨m, hm⟩ := exists_nat_gt
    (max (m₀ : ℝ) (max ((pwr + 4 * K + 20 : ℕ) : ℝ) (3 / (2 * h))))
  have hm₀ : m₀ ≤ m := by exact_mod_cast ((le_max_left _ _).trans_lt hm).le
  have hmp : pwr + 4 * K + 20 ≤ m := by
    exact_mod_cast (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hm).le
  have hm₁ := (div_lt_iff₀ (by positivity : 0 < 2 * h)).mp
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hm)
  refine ⟨pwr, m, max q₀ (4 * (J * T) + 1), hp₀, hm₀, le_max_left _ _, hmp,
    by omega, ?_, ?_, ?_, ?_⟩
  · push_cast
    nlinarith
  · nlinarith
  · intro s ζ hs hζ
    nlinarith [mul_nonneg (Nat.cast_nonneg m) hζ]
  · have ht : (4 * (J * T) + 1 : ℕ) ≤ max q₀ (4 * (J * T) + 1) := le_max_right _ _
    have ht' : (4 * (J * T) + 1 : ℝ) ≤ (max q₀ (4 * (J * T) + 1) : ℕ) := by
      exact_mod_cast ht
    linarith

end FalconerPacking
