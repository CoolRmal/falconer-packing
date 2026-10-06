/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.GaussianBallEnergy
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Polar integration and angular Fourier energy

Polar coordinates are transferred from the complex plane to the Euclidean plane by a
volume-preserving linear isometry. The radial Jacobian then converts Fourier ball growth
into angular band bounds.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- The unit vector in the plane with angle θ. -/
def angularDirection (θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)

@[simp]
theorem norm_angularDirection (θ : ℝ) : ‖angularDirection θ‖ = 1 := by
  rw [angularDirection, LinearIsometryEquiv.norm_map]
  simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_cos_add_sin_mul_I θ

@[fun_prop]
theorem continuous_angularDirection : Continuous angularDirection := by
  unfold angularDirection
  fun_prop

/-- Polar integration for nonnegative functions on the Euclidean plane. -/
theorem lintegral_polar_euclidean (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * f (p.1 • angularDirection p.2) = ∫⁻ x, f x := by
  have h := Complex.lintegral_comp_polarCoord_symm
    (fun z ↦ f (Complex.orthonormalBasisOneI.repr z))
  have he := Complex.orthonormalBasisOneI.repr.measurePreserving.lintegral_comp_emb
    Complex.orthonormalBasisOneI.repr.toHomeomorph.measurableEmbedding f
  rw [he] at h
  simpa only [polarCoord_target, Complex.polarCoord_symm_apply,
    angularDirection, ← Complex.real_smul, map_smul, smul_eq_mul] using h

/-- On a positive radial band the inverse inner radius removes the polar Jacobian. -/
theorem lintegral_polar_band_le (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞)
    {L R : ℝ} (hL : 0 < L) :
    ∫⁻ p : ℝ × ℝ in Ioo L R ×ˢ Ioo (-Real.pi) Real.pi,
      f (p.1 • angularDirection p.2) ≤
        (ENNReal.ofReal L)⁻¹ * ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
          f x := by
  let A := Ioo L R ×ˢ Ioo (-Real.pi) Real.pi
  let B := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R
  have hA : MeasurableSet A := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : A ⊆ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := fun p hp ↦
    ⟨hL.trans hp.1.1, hp.2⟩
  apply (ENNReal.mul_le_iff_le_inv (ne_of_gt (ENNReal.ofReal_pos.mpr hL))
    ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal L * ∫⁻ p : ℝ × ℝ in A, f (p.1 • angularDirection p.2) =
        ∫⁻ p : ℝ × ℝ in A, ENNReal.ofReal L * f (p.1 • angularDirection p.2) :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ p : ℝ × ℝ in A,
        ENNReal.ofReal p.1 * B.indicator f (p.1 • angularDirection p.2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with p hp
      have hpB : p.1 • angularDirection p.2 ∈ B := by
        simpa only [B, Metric.mem_ball, dist_zero_right, norm_smul,
          Real.norm_eq_abs, abs_of_pos (hL.trans hp.1.1), norm_angularDirection,
          mul_one] using hp.1.2
      rw [indicator_of_mem hpB]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hp.1.1.le) _
    _ ≤ ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * B.indicator f (p.1 • angularDirection p.2) :=
      lintegral_mono_set hsub
    _ = ∫⁻ x in B, f x := by
      rw [lintegral_polar_euclidean, lintegral_indicator Metric.isOpen_ball.measurableSet]

/-- The angular integral of radial band mass is bounded by planar ball mass. -/
theorem lintegral_angular_band_le {f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    (hf : Measurable f) {L R : ℝ} (hL : 0 < L) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioo L R, f (r • angularDirection θ) ≤
      (ENNReal.ofReal L)⁻¹ * ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        f x := by
  have hm : Measurable (fun p : ℝ × ℝ ↦ f (p.1 • angularDirection p.2)) := by fun_prop
  rw [← setLIntegral_prod_symm _ hm.aemeasurable]
  exact lintegral_polar_band_le f hL

/-- The characteristic function has integrable squared norm on every bounded ball. -/
theorem integrableOn_charFun_norm_sq_ball
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ] (R : ℝ) :
    IntegrableOn (fun ξ ↦ ‖charFun μ ξ‖ ^ 2)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R) volume :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall _ R)
    ((continuous_charFun (μ := μ)).norm.pow 2).continuousOn).mono_set
      Metric.ball_subset_closedBall

/-- Frostman growth gives one uniform angular Fourier band estimate. -/
theorem exists_angular_fourier_band_bound
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∃ A : ℝ, 0 < A ∧ ∀ R : ℝ, 0 < R →
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioo (R / 2) (2 * R),
        ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) ≤
          ENNReal.ofReal (A * R ^ (1 - s)) := by
  obtain ⟨A, hA, hbound⟩ := exists_fourier_ball_energy_bound μ hs hs₂ hfr
  refine ⟨2 * A * (2 : ℝ) ^ (2 - s), by positivity, fun R hR ↦ ?_⟩
  have hpolar := lintegral_angular_band_le (R := 2 * R)
    (f := fun ξ ↦ ENNReal.ofReal (‖charFun μ ξ‖ ^ 2)) (by fun_prop)
    (show 0 < R / 2 by positivity)
  have hint := ofReal_integral_eq_lintegral_ofReal
    (integrableOn_charFun_norm_sq_ball μ (2 * R))
    (Filter.Eventually.of_forall fun ξ ↦ sq_nonneg (‖charFun μ ξ‖))
  rw [← hint] at hpolar
  have he : (ENNReal.ofReal (R / 2))⁻¹ * ENNReal.ofReal (A * (2 * R) ^ (2 - s)) =
      ENNReal.ofReal ((2 * A * (2 : ℝ) ^ (2 - s)) * R ^ (1 - s)) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow (by norm_num) hR.le, show 2 - s = 1 + (1 - s) by ring,
      Real.rpow_add hR, Real.rpow_one]
    field_simp
  exact (hpolar.trans (mul_le_mul'
    le_rfl (ENNReal.ofReal_le_ofReal (hbound (2 * R) (by positivity))))).trans_eq he

private theorem positive_band_cover_aux : Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi ⊆
    (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) ∪
      ⋃ n : ℕ, Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n) ×ˢ Ioo (-Real.pi) Real.pi := by
  intro p hp
  by_cases h : p.1 < 1
  · exact Or.inl ⟨⟨hp.1, h⟩, hp.2⟩
  · obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near (le_of_not_gt h) (by norm_num : (1 : ℝ) < 2)
    apply Or.inr
    refine mem_iUnion.mpr ⟨n, ⟨?_, ?_⟩, hp.2⟩
    · have : (0 : ℝ) < 2 ^ n := by positivity
      linarith
    · simpa only [pow_succ, mul_comm] using hn'

private theorem summable_fourier_band_bound_aux {s : ℝ} (hs : 1 < s) (K : ℝ) :
    Summable (fun n : ℕ ↦ K * ((2 : ℝ) ^ n) ^ (1 - s)) := by
  have hq : |(2 : ℝ) ^ (1 - s)| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeometric : Summable (fun n : ℕ ↦ K * ((2 : ℝ) ^ (1 - s)) ^ n) :=
    (summable_geometric_of_norm_lt_one (by simpa using hq)).mul_left K
  apply hgeometric.congr
  intro n
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (n : ℝ),
    Real.rpow_mul_natCast (by norm_num)]

/-- Positive radial Fourier energy is integrable jointly in radius and angle when s>1. -/
theorem lintegral_angular_positive_fourier_lt_top
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ] {s C : ℝ}
    (hs : 1 < s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (‖charFun μ (r • angularDirection θ)‖ ^ 2) < ∞ := by
  let f (p : ℝ × ℝ) := ENNReal.ofReal (‖charFun μ (p.1 • angularDirection p.2)‖ ^ 2)
  let A := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  let B (n : ℕ) := Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n) ×ˢ Ioo (-Real.pi) Real.pi
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hlow : ∫⁻ p in A, f p < ∞ := by
    have hle : ∀ p, f p ≤ 1 := fun p ↦ by
      apply (ENNReal.ofReal_le_ofReal ?_).trans_eq (ENNReal.ofReal_one)
      nlinarith [norm_charFun_le_one (μ := μ) (p.1 • angularDirection p.2),
        norm_nonneg (charFun μ (p.1 • angularDirection p.2))]
    apply (lintegral_mono hle).trans_lt
    simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
    change (volume.prod volume) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) < ∞
    rw [Measure.prod_prod]
    simp only [Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  obtain ⟨K, hK, hbound⟩ := exists_angular_fourier_band_bound μ (by linarith) hs₂ hfr
  have hsum := summable_fourier_band_bound_aux hs K
  have hhigh : ∫⁻ p in ⋃ n, B n, f p < ∞ := by
    refine (lintegral_iUnion_le B f).trans_lt ((ENNReal.tsum_le_tsum ?_).trans_lt
      hsum.tsum_ofReal_lt_top)
    intro n
    change (∫⁻ p in Ioo ((2 : ℝ) ^ n / 2) (2 * (2 : ℝ) ^ n) ×ˢ
      Ioo (-Real.pi) Real.pi, f p ∂volume.prod volume) ≤ _
    rw [setLIntegral_prod_symm _ hf.aemeasurable]
    exact hbound ((2 : ℝ) ^ n) (by positivity)
  rw [← setLIntegral_prod_symm f hf.aemeasurable]
  exact (lintegral_mono_set positive_band_cover_aux).trans_lt
    ((lintegral_union_le f A (⋃ n, B n)).trans_lt (ENNReal.add_lt_top.mpr ⟨hlow, hhigh⟩))

end FalconerPacking
