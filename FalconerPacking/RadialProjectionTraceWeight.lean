/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RadialProjectionEnergy

/-!
# The positive weighting step in radial trace duality

Hölder on the product measure bounds the Riesz energy of an actual weighted measure.
Choosing the pin-energy exponent to be exactly `p * (2 - s)` avoids any bounded-support
comparison of distinct kernels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Exact dual exponents retain strict angular integrability and require no support loss. -/
theorem radialProjection_exact_exponents {s : ℝ} (hs : 1 < s) (hs₂ : s < 2) :
    let p := 1 + (s - 1) / 8
    1 < p ∧ p < 2 ∧ 0 < p * (2 - s) ∧ p * (2 - s) < 1 ∧
      p * (2 - s) < 2 - p := by
  dsimp
  refine ⟨by linarith, by linarith, mul_pos (by linarith) (by linarith), ?_, ?_⟩
  · nlinarith [sq_nonneg (s - 1)]
  · nlinarith [sq_nonneg (s - 1)]

/-- A normalized dual weight raises the unweighted energy exponent by exactly `p`. -/
theorem weighted_rieszEnergy_le
    (κ : Measure ℝ) [SFinite κ] {p q : ℝ} (hpq : p.HolderConjugate q)
    (a : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hnorm : (∫⁻ x, f x ^ q ∂κ) ≤ 1) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal |x - y| ^ (-a)
      ∂κ.withDensity f ∂κ.withDensity f) ≤
      (∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal |x - y| ^ (-(p * a)) ∂κ ∂κ) ^ (1 / p) := by
  let k : ℝ × ℝ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal |z.1 - z.2| ^ (-a)
  let g : ℝ × ℝ → ℝ≥0∞ := fun z ↦ f z.1 * f z.2
  have hk : Measurable k := by fun_prop
  have hg : Measurable g := by fun_prop
  have hinner (x : ℝ) :
      (∫⁻ y : ℝ, ENNReal.ofReal |x - y| ^ (-a) ∂κ.withDensity f) =
      ∫⁻ y : ℝ, f y * ENNReal.ofReal |x - y| ^ (-a) ∂κ :=
    lintegral_withDensity_eq_lintegral_mul κ hf (by fun_prop)
  have hweighted : (∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal |x - y| ^ (-a)
      ∂κ.withDensity f ∂κ.withDensity f) = ∫⁻ z, (k * g) z ∂κ.prod κ := by
    simp_rw [hinner]
    rw [lintegral_withDensity_eq_lintegral_mul κ hf (by fun_prop),
      lintegral_prod _ (hk.mul hg).aemeasurable]
    apply lintegral_congr
    intro x
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul (f x) (by fun_prop)]
    apply lintegral_congr
    intro y
    dsimp [k, g]
    ac_rfl
  have hkg := ENNReal.lintegral_mul_le_Lp_mul_Lq (κ.prod κ) hpq
    hk.aemeasurable hg.aemeasurable
  have hknorm : (∫⁻ z, k z ^ p ∂κ.prod κ) =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal |x - y| ^ (-(p * a)) ∂κ ∂κ := by
    rw [lintegral_prod _ (hk.pow_const p).aemeasurable]
    simp only [k, ← ENNReal.rpow_mul, neg_mul, mul_comm a p]
  have hgnorm : (∫⁻ z, g z ^ q ∂κ.prod κ) = (∫⁻ x, f x ^ q ∂κ) ^ 2 := by
    rw [lintegral_prod _ (hg.pow_const q).aemeasurable]
    simp only [g, ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg]
    simp_rw [lintegral_const_mul _ (hf.pow_const q)]
    rw [lintegral_mul_const _ (hf.pow_const q), pow_two]
  rw [hweighted]
  apply hkg.trans
  rw [hknorm, hgnorm]
  apply mul_le_of_le_one_right'
  exact ENNReal.rpow_le_one (pow_le_one₀ bot_le hnorm)
    (one_div_nonneg.mpr hpq.symm.nonneg)

end FalconerPacking
