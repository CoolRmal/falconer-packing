/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.PolarFourierEnergy
public import FalconerPacking.FourierDensity

/-!
# Square-integrable Fourier transforms of orthogonal projections

The polar energy estimates imply square integrability on almost every line through the
origin. The characteristic function of the projected measure is its restriction to that line.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace FalconerPacking

/-- Reflection and evenness identify the two half-line integrals. -/
theorem lintegral_Iio_eq_Ioi_of_even {f : ℝ → ℝ≥0∞} (hf : ∀ x, f (-x) = f x) :
    ∫⁻ r in Iio (0 : ℝ), f r = ∫⁻ r in Ioi (0 : ℝ), f r := by
  have h := ((Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Iio (0 : ℝ)) measurableSet_Iio).lintegral_comp_emb
      (MeasurableEquiv.neg ℝ).measurableEmbedding f
  have hset : (Neg.neg ⁻¹' Iio (0 : ℝ)) = Ioi 0 := by ext x; simp
  simpa only [hf, hset] using h.symm

/-- For an even function, finite positive half-line integral gives finite total integral. -/
theorem lintegral_lt_top_of_even_of_Ioi {f : ℝ → ℝ≥0∞} (hf : ∀ x, f (-x) = f x)
    (hpos : ∫⁻ r in Ioi (0 : ℝ), f r < ∞) : ∫⁻ r, f r < ∞ := by
  have hneg := lintegral_Iio_eq_Ioi_of_even hf
  rw [← lintegral_add_compl f measurableSet_Ioi, compl_Ioi,
    ← setLIntegral_congr Iio_ae_eq_Iic, hneg]
  exact ENNReal.add_lt_top.mpr ⟨hpos, hpos⟩

/-- Positive radial integrability yields square integrability on almost every full line. -/
theorem ae_memLp_charFun_on_line
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      MemLp (fun r : ℝ ↦ charFun μ (r • angularDirection θ)) 2 volume := by
  have hfin := lintegral_angular_positive_fourier_lt_top μ hs hs₂ hfr
  have hm : Measurable (fun θ : ℝ ↦ ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2)) := by fun_prop
  filter_upwards [ae_lt_top hm hfin.ne] with θ hθ
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) (by fun_prop)]
  have heven (r : ℝ) : ENNReal.ofReal (‖charFun μ ((-r) • angularDirection θ)‖ ^ 2) =
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) := by
    simp only [neg_smul, charFun_neg, RCLike.norm_conj]
  have h := lintegral_lt_top_of_even_of_Ioi heven hθ
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h

/-- Orthogonal projection restricts the planar characteristic function to a line. -/
theorem charFun_orthogonalProjection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    (v : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    charFun (μ.map (fun x ↦ ⟪x, v⟫)) r = charFun μ (r • v) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by simp only [real_inner_comm,
    real_inner_smul_right, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Almost every orthogonal projection has a square-integrable characteristic function. -/
theorem ae_memLp_charFun_orthogonalProjection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi),
      MemLp (charFun (μ.map (fun x ↦ ⟪x, angularDirection θ⟫))) 2 volume := by
  filter_upwards [ae_memLp_charFun_on_line μ hs hs₂ hfr] with θ hθ
  change MemLp (fun r ↦ charFun (μ.map (fun x ↦ ⟪x, angularDirection θ⟫)) r) 2 volume
  simpa only [charFun_orthogonalProjection] using hθ

/-- Frostman probabilities of exponent above one have nonnegative L² projection densities
for almost every angle. -/
theorem ae_exists_L2_density_orthogonalProjection
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∀ᵐ θ ∂volume.restrict (Ioo (-Real.pi) Real.pi), ∃ f : ℝ → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧ MemLp f 2 volume ∧
      μ.map (fun x ↦ ⟪x, angularDirection θ⟫) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  filter_upwards [ae_memLp_charFun_orthogonalProjection μ hs hs₂ hfr] with θ hθ
  obtain ⟨f, hpos, hint, hLp, hdensity, _⟩ := exists_L2_density_of_memLp_charFun _ hθ
  exact ⟨f, hpos, hint, hLp, hdensity⟩

end FalconerPacking
