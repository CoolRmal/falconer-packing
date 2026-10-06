/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.BorelCompactReduction
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Strict exponents and bounded Frostman data for the coherent branch

The strict packing inequality leaves room to lower the Hausdorff exponent before compact
extraction. Frostman constants can be increased to at least one without changing the measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Increasing the Frostman constant preserves the same exponent and actual measure. -/
theorem IsFrostman.mono_constant
    {μ : Measure (EuclideanSpace ℝ (Fin 2))} {s C D : ℝ}
    (h : IsFrostman μ s C) (hCD : C ≤ D) : IsFrostman μ s D := by
  intro x r hr hr₁
  exact (h x r hr hr₁).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hr.le s)))

/-- A compact conull source provides a genuine almost-everywhere norm bound. -/
theorem exists_ae_norm_le_of_compact_conull
    (μ : Measure (EuclideanSpace ℝ (Fin 2)))
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K) (hμ : μ Kᶜ = 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ᵐ x ∂μ, ‖x‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := hK.isBounded.exists_pos_norm_le
  exact ⟨M, hM, (ae_iff.mpr hμ).mono fun x hx ↦ hbound x hx⟩

/-- The strict coherent cutoff permits source and covering exponents with a positive gap. -/
theorem exists_strict_exponents_of_coherent_cutoff
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ}
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd₂ : d < 2)
    (hpack : packingDim E < ENNReal.ofReal (2 * d - 1)) :
    ∃ s u : ℝ, 1 < s ∧ s < d ∧ s < 2 ∧ s < u ∧
      ENNReal.ofReal s < dimH E ∧ packingDim E < ENNReal.ofReal u ∧ u < 2 * s - 1 := by
  have hfin : packingDim E ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpack.le
  have hD : (packingDim E).toReal < 2 * d - 1 :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfin).mp hpack
  have hdD : d ≤ (packingDim E).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfin).mp (hdim ▸ dimH_le_packingDim E)
  obtain ⟨s, hs, hsd⟩ := exists_between (show ((packingDim E).toReal + 1) / 2 < d by
    linarith)
  have hs₁ : 1 < s := by linarith only [hs, hdD, hd]
  obtain ⟨u, hDu, hu⟩ := exists_between (show (packingDim E).toReal < 2 * s - 1 by
    linarith)
  refine ⟨s, u, hs₁, hsd, hsd.trans hd₂, hsd.trans (hdD.trans_lt hDu), ?_, ?_, hu⟩
  · rw [hdim]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hsd
  · exact (ENNReal.lt_ofReal_iff_toReal_lt hfin).mpr hDu

/-- Borel sets below the coherent cutoff give all separated compact measure data, with
positive normalized Frostman constants and a separation parameter at most one. -/
theorem exists_coherent_compact_data_of_measurableSet
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ} (hE : MeasurableSet E)
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd₂ : d < 2)
    (hpack : packingDim E < ENNReal.ofReal (2 * d - 1)) :
    ∃ (s u : ℝ) (K L : Set (EuclideanSpace ℝ (Fin 2)))
      (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) (Cμ Cν δ : ℝ),
      1 < s ∧ s < 2 ∧ s < u ∧ u < 2 * s - 1 ∧
      IsCompact K ∧ IsCompact L ∧ K ⊆ E ∧ L ⊆ E ∧
      HasUpperBoxBound K u ∧
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) Kᶜ = 0 ∧
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) Lᶜ = 0 ∧
      1 ≤ Cμ ∧ 1 ≤ Cν ∧
      IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ ∧
      IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) s Cν ∧
      0 < δ ∧ δ ≤ 1 ∧ ∀ x ∈ K, ∀ y ∈ L, δ ≤ dist x y := by
  obtain ⟨s, u, hs, _, hs₂, hsu, hsdim, hpacku, hu⟩ :=
    exists_strict_exponents_of_coherent_cutoff hdim hd hd₂ hpack
  obtain ⟨K, L, μ, ν, Cμ, Cν, δ, hK, hL, hKE, hLE, hbox, _,
    hμK, hνL, hμ, hν, hδ, hsep⟩ :=
    exists_separated_frostman_probabilities_of_measurableSet hE hs
      (lt_trans zero_lt_one (hs.trans hsu)) hsdim hpacku
  refine ⟨s, u, K, L, μ, ν, max Cμ 1, max Cν 1, min δ 1,
    hs, hs₂, hsu, hu, hK, hL, hKE, hLE, hbox, hμK, hνL,
    le_max_right _ _, le_max_right _ _, hμ.mono_constant (le_max_left _ _),
    hν.mono_constant (le_max_left _ _), lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro x hx y hy
  exact (min_le_left δ 1).trans (hsep x hx y hy)

end FalconerPacking
