/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RegularConditionalEnergy

/-!
# Truncated energy under the physical parent enlargement

The finite slope grid uses an enlarged parent ball. Enlarging both of the original spatial
scales by a factor lambda costs at most lambda in truncated energy, including on the diagonal.
This connects the actual finite-grid energy to the regular profile estimate.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Increasing the inner cutoff only decreases the truncated kernel. -/
theorem truncKernel_mono_inner {a a' b : ℝ} (ha : 0 < a) (haa : a ≤ a')
    (hb : 0 ≤ b) (x y : EuclideanSpace ℝ (Fin 2)) :
    truncKernel a' b x y ≤ truncKernel a b x y := by
  have hr : b / a' ≤ b / a := div_le_div_of_nonneg_left hb ha haa
  unfold truncKernel
  split
  · exact ENNReal.ofReal_le_ofReal hr
  · exact ENNReal.ofReal_le_ofReal (min_le_min hr le_rfl)

/-- Scaling the outer length multiplies the kernel by exactly that factor. -/
theorem truncKernel_scale_outer {Λ : ℝ} (hΛ : 0 ≤ Λ) (a b : ℝ)
    (x y : EuclideanSpace ℝ (Fin 2)) :
    truncKernel a (Λ * b) x y = ENNReal.ofReal Λ * truncKernel a b x y := by
  unfold truncKernel
  split
  · rw [show Λ * b / a = Λ * (b / a) by ring, ENNReal.ofReal_mul hΛ]
  · rw [show Λ * b / a = Λ * (b / a) by ring,
      show Λ * b / dist x y = Λ * (b / dist x y) by ring,
      ← mul_min_of_nonneg _ _ hΛ, ENNReal.ofReal_mul hΛ]

/-- Both physical scale enlargements cost at most their common enlargement factor. -/
theorem truncEnergy_enlarge_le (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {a b Λ : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hΛ : 1 ≤ Λ) :
    truncEnergy μ (Λ * a) (Λ * b) ≤ ENNReal.ofReal Λ * truncEnergy μ a b := by
  have hΛ₀ : 0 ≤ Λ := le_trans zero_le_one hΛ
  have haa : a ≤ Λ * a := by nlinarith
  unfold truncEnergy
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, truncKernel a (Λ * b) x y ∂μ ∂μ := by
      apply lintegral_mono
      intro x
      exact lintegral_mono fun y ↦ truncKernel_mono_inner ha haa (mul_nonneg hΛ₀ hb) x y
    _ = _ := by
      simp_rw [truncKernel_scale_outer hΛ₀,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The actual regular conditional energy estimate remains valid for enlarged spatial scales. -/
theorem normalized_regular_enlarged_energy_le_edgeCost
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {T L : ℕ} (hT : 0 < T) {A : Finset (Fin 2 → ℤ)} {e : ℕ → ℕ}
    (he : ∀ j < L, e j ≤ 2 * T)
    (hA : μ (finiteDyadicUnion (T * L) A) ≠ 0)
    (hreg : FiniteTreeRegular A
      (fun k ↦ (normalizedRestrict μ (finiteDyadicUnion (T * L) A)).real
        (dyadicCube (T * L) k)) (ancestor T) L e)
    (hroot : ∀ x ∈ A, ∀ y ∈ A, ancestor (T * L) x = ancestor (T * L) y)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ L)
    {q : Fin 2 → ℤ}
    (hq : 0 < normalizedRestrict μ (finiteDyadicUnion (T * L) A) (dyadicCube (T * m) q))
    {X : Set (EuclideanSpace ℝ (Fin 2))} (hXm : MeasurableSet X)
    (hX : dyadicCube (T * m) q ⊆ X) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    truncEnergy (normalizedRestrict (normalizedRestrict μ (finiteDyadicUnion (T * L) A)) X)
        (Λ * dyadicRadius (T * n)) (Λ * dyadicRadius (T * m)) ≤
      ENNReal.ofReal Λ *
        (4 * (n + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
          (3 * (L : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T L e) m n)) := by
  apply (truncEnergy_enlarge_le _ (dyadicRadius_pos _) (dyadicRadius_pos _).le hΛ).trans
  exact mul_le_mul' le_rfl
    (normalized_regular_conditional_energy_le_edgeCost μ hT he hA hreg hroot hmn hn hq hXm hX)

end FalconerPacking
