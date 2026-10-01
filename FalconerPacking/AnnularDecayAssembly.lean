/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.AnnularComponentGluing
import FalconerPacking.EventualAnnularCriterion

/-!
# One summable bound for the actual annular pieces

The retained second norm, deleted first norm, and discarded-pin mass may decay at different
positive rates. They have one common rate, including the shift between packet shell index
and the full compact annular expansion.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace FalconerPacking

/-- Three independently obtained shell bounds have a single positive exponential rate.
The output is indexed by the actual compact-annulus index `k + 1`. -/
theorem exists_common_annular_decay {A B C : ℝ≥0∞}
    (hA : A ≠ ∞) (hB : B ≠ ∞) (hC : C ≠ ∞)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ D ε : ℝ, 0 ≤ D ∧ 0 < ε ∧ ∀ k : ℕ,
      A * (2 : ℝ≥0∞) ^ (-a * k) ≤
        ENNReal.ofReal (D * (2 : ℝ) ^ (-ε * (k + 1 : ℕ))) ∧
      B * (2 : ℝ≥0∞) ^ (-(k : ℝ)) + C * (2 : ℝ≥0∞) ^ (-b * k) ≤
        ENNReal.ofReal (D * (2 : ℝ) ^ (-ε * (k + 1 : ℕ))) := by
  let ε := min a (min 1 b)
  let H := A + B + C
  have hε : 0 < ε := lt_min ha (lt_min zero_lt_one hb)
  have hH : H ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hA, hB⟩, hC⟩
  refine ⟨H.toReal * (2 : ℝ) ^ ε, ε, by positivity, hε, fun k ↦ ?_⟩
  have heq : ENNReal.ofReal
      (H.toReal * (2 : ℝ) ^ ε * (2 : ℝ) ^ (-ε * (k + 1 : ℕ))) =
      H * (2 : ℝ≥0∞) ^ (-ε * k) := by
    rw [mul_assoc, ← Real.rpow_add (by norm_num)]
    have hexp : ε + -ε * (k + 1 : ℕ) = -ε * k := by push_cast; ring
    rw [hexp, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hH,
      ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [heq]
  have hp (c : ℝ) (hc : ε ≤ c) :
      (2 : ℝ≥0∞) ^ (-c * k) ≤ (2 : ℝ≥0∞) ^ (-ε * k) := by
    apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right (neg_le_neg hc) (Nat.cast_nonneg k)
  constructor
  · exact mul_le_mul' (by dsimp [H]; exact le_self_add.trans (le_self_add))
      (hp a (min_le_left _ _))
  · calc
      _ ≤ B * (2 : ℝ≥0∞) ^ (-ε * k) + C * (2 : ℝ≥0∞) ^ (-ε * k) := by
        apply add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_)
        · simpa only [neg_mul, one_mul] using hp 1 ((min_le_right _ _).trans (min_le_left _ _))
        · exact hp b ((min_le_right _ _).trans (min_le_right _ _))
      _ = (B + C) * (2 : ℝ≥0∞) ^ (-ε * k) := (add_mul _ _ _).symm
      _ ≤ H * (2 : ℝ≥0∞) ^ (-ε * k) :=
        mul_le_mul' (by dsimp [H]; rw [add_assoc]; exact le_add_self) le_rfl

end FalconerPacking
