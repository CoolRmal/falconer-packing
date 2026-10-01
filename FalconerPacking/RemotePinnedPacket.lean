/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.SourcePacketFrequency

/-!
# Remote pinned first-norm estimates for actual source packets

The frequency representation is combined with full-circle nonstationary phase. The spatial
cutoff gives bounded distance support, so the resulting estimate controls the entire distance
density, rather than just a single circular average.
-/

noncomputable section

open MeasureTheory Set Metric FourierTransform
open scoped FourierTransform RealInnerProductSpace

namespace FalconerPacking

/-- Uniform full-circle decay at each actual nonzero frequency. -/
theorem exists_remote_frequency_circle_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (m : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w γ R : ℝ), 0 < w → w ≤ γ → γ ≤ 1 → 0 < R →
      ∀ (ξ y : EuclideanSpace ℝ (Fin 2)) (α ε r : ℝ) (k : ℤ),
        R ≤ ‖ξ‖ → |r| ≤ L → 0 ≤ ε →
        ‖‖ξ‖⁻¹ • ξ - angularDirection α‖ ≤ ε →
        γ + w + L * ε ≤ |⟪angularDirection (α + Real.pi / 2), y⟫ - w * k| →
        ‖∫ θ, Complex.exp ((-2 * Real.pi * r * ⟪ξ, angularDirection θ⟫ : ℝ) *
          Complex.I) *
          (circularPacketAmplitude χ w (angularDirection (α + Real.pi / 2)) y k r θ : ℂ)
          ∂radialAngularMeasure‖ ≤ C * (R * w * γ)⁻¹ ^ m := by
  obtain ⟨C, hC, hbound⟩ := exists_remote_circularPacket_circle_integral_bound χ m L L
  refine ⟨C, hC, ?_⟩
  intro w γ R hw hwγ hγ₁ hR ξ y α ε r k hξ hr hε hnear hremote
  have hγ : 0 < γ := hw.trans_le hwγ
  have hξpos : 0 < ‖ξ‖ := hR.trans_le hξ
  have hξne : ξ ≠ 0 := norm_pos_iff.mp hξpos
  have hv : ‖‖ξ‖⁻¹ • ξ‖ = 1 := norm_smul_inv_norm hξne
  have hrv : ‖r • (‖ξ‖⁻¹ • ξ)‖ ≤ L := by simpa [norm_smul, hv] using hr
  have hremote' : γ + w + |r| * ε ≤
      |⟪angularDirection (α + Real.pi / 2), y⟫ - w * k| :=
    by linarith [mul_le_mul_of_nonneg_right hr hε]
  have ht : -2 * Real.pi * ‖ξ‖ ≠ 0 := by positivity
  have hb := hbound w γ hw hwγ hγ₁ (‖ξ‖⁻¹ • ξ) y α ε r k hr hrv hnear hremote'
    (-2 * Real.pi * ‖ξ‖) ht
  have he : ∀ θ, oscillatoryPhase (circularPhase (r • (‖ξ‖⁻¹ • ξ)))
      (-2 * Real.pi * ‖ξ‖) θ =
      Complex.exp ((-2 * Real.pi * r * ⟪ξ, angularDirection θ⟫ : ℝ) * Complex.I) := by
    intro θ
    simp only [oscillatoryPhase, circularPhase, real_inner_smul_left]
    congr 1
    push_cast
    field_simp [show (‖ξ‖ : ℂ) ≠ 0 by exact_mod_cast hξpos.ne']
  simp_rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  apply inv_anti₀ (by positivity : 0 < R * w * γ)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
  rw [abs_mul, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0),
    abs_of_pos Real.pi_pos, abs_of_pos hξpos]
  norm_num only [neg_neg]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hξ.trans (le_mul_of_one_le_left hξpos.le hπ)) hw.le)
    (hw.trans_le hwγ).le

/-- A source supported within distance `L` of the pin has its complete distance density
supported in `[0,L]`, including for signed or complex sources. -/
theorem tsupport_complexDistanceDensity_subset
    {f : EuclideanSpace ℝ (Fin 2) → ℂ} (y : EuclideanSpace ℝ (Fin 2)) (L : ℝ)
    (hf : ∀ x ∈ Function.support f, dist x y ≤ L) :
    tsupport (complexDistanceDensity f y) ⊆ Icc 0 L := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  by_contra hnot
  apply hr
  by_cases hpos : 0 < r
  · rw [complexDistanceDensity_eq_circle_integral f y hpos]
    have hz : ∀ θ, f (y - r • angularDirection θ) = 0 := by
      intro θ
      by_contra hne
      have hdist := hf _ hne
      have hd : dist (y - r • angularDirection θ) y = r := by
        rw [dist_eq_norm]
        simp only [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          norm_angularDirection, mul_one, abs_of_pos hpos]
      rw [hd] at hdist
      exact hnot ⟨hpos.le, hdist⟩
    simp only [hz, integral_zero, mul_zero]
  · simp only [complexDistanceDensity, hpos, ↓reduceIte]

/-- The constructed packet's complete distance support follows from the actual source cutoff. -/
theorem tsupport_distanceDensity_sourceWavePacket_subset
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
    (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
    (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (N : ℕ) (hN : 0 < N) {w : ℝ} (hw : 0 < w) (j : ℕ) (k : ℤ)
    (y : EuclideanSpace ℝ (Fin 2)) {L : ℝ}
    (hL : sourceCutoffRadius χ hχ + ‖y‖ ≤ L) :
    tsupport (complexDistanceDensity
      (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y) ⊆ Icc 0 L := by
  apply tsupport_complexDistanceDensity_subset
  intro x hx
  have hχx := (support_sourceWavePacket_subset μ hμ ψ hψ hzero χ hχ N hN hw j k hx).1
  have hxbound := support_subset_sourceCutoffRadius χ hχ hχx
  rw [mem_closedBall, dist_zero_right] at hxbound
  exact (dist_le_norm_add_norm x y).trans (by linarith)

/-- The actual source packet satisfies arbitrary polynomial remote-pin decay in the entire
distance first norm. Only the lower annular frequency bound is needed. -/
theorem exists_remote_sourceWavePacket_distance_L1_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (m : ℕ) {L : ℝ} (hLpos : 0 < L) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsFiniteMeasure μ]
        (M : ℝ) (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M)
        (ψ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℂ) (hψ : HasCompactSupport ψ)
        (hzero : (ψ : EuclideanSpace ℝ (Fin 2) → ℂ) =ᶠ[nhds 0] 0)
        (N : ℕ) (hN : 0 < N) (w γ R : ℝ),
        0 < w → w ≤ γ → γ ≤ 1 → 0 < R →
        (∀ ξ ∈ Function.support ψ, R ≤ ‖ξ‖) →
        ∀ (j : ℕ) (k : ℤ) (y : EuclideanSpace ℝ (Fin 2)),
          sourceCutoffRadius χ hχ + ‖y‖ ≤ L →
          γ + w + L * (4 * Real.pi / N) ≤
            |⟪sourceWavePacketNormal N j, y⟫ - w * k| →
          (∫ r, ‖complexDistanceDensity
            (sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k) y r‖) ≤
              C * (R * w * γ)⁻¹ ^ m * μ.real univ *
                ∫ ξ, ‖smoothAngularCap ψ hψ hzero N hN j ξ‖ := by
  obtain ⟨B, hB, hbound⟩ := exists_remote_frequency_circle_bound χ m L
  refine ⟨L ^ 2 * B, by positivity, ?_⟩
  intro μ _ M hμ ψ hψ hzero N hN w γ R hw hwγ hγ₁ hR hfreq j k y hL hremote
  let cap := smoothAngularCap ψ hψ hzero N hN j
  let f := sourceWavePacket μ hμ ψ hψ hzero χ hχ N hN w j k
  let D := B * (R * w * γ)⁻¹ ^ m
  have hγ : 0 < γ := hw.trans_le hwγ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmass : 0 ≤ μ.real univ := ENNReal.toReal_nonneg
  have hcap : 0 ≤ ∫ ξ, ‖cap ξ‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hs : tsupport (complexDistanceDensity f y) ⊆ Icc 0 L :=
    tsupport_distanceDensity_sourceWavePacket_subset μ hμ ψ hψ hzero χ hχ N hN
      hw j k y hL
  have hb : ∀ r, ‖complexDistanceDensity f y r‖ ≤ L * (D * μ.real univ * ∫ ξ, ‖cap ξ‖) := by
    intro r
    by_cases hrs : r ∈ Ioc 0 L
    · rw [complexDistanceDensity_sourceWavePacket_eq_frequency μ hμ ψ hψ hzero χ hχ
        N hN w j k y hrs.1, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrs.1]
      have hint : ‖∫ ξ, (Complex.exp ((2 * Real.pi * ⟪ξ, y⟫ : ℝ) * Complex.I) *
          sourcePacketSpectrum μ cap ξ) *
          ∫ θ, Complex.exp ((-2 * Real.pi * r * ⟪ξ, angularDirection θ⟫ : ℝ) *
            Complex.I) *
            (circularPacketAmplitude χ w (sourceWavePacketNormal N j) y k r θ : ℂ)
            ∂radialAngularMeasure‖ ≤ D * μ.real univ * ∫ ξ, ‖cap ξ‖ := by
        calc
          _ ≤ ∫ ξ, (D * μ.real univ) * ‖cap ξ‖ := by
            apply norm_integral_le_of_norm_le (cap.integrable.norm.const_mul _)
            apply ae_of_all
            intro ξ
            by_cases hξ : cap ξ = 0
            · simp [sourcePacketSpectrum, hξ]
            · have hsupport : ξ ∈ Function.support
                  (smoothAngularCap ψ hψ hzero N hN j) := hξ
              have hrad := hfreq ξ (support_smoothAngularCap_subset ψ hψ hzero N hN j hsupport)
              have hdir := smoothAngularCap_direction_support ψ hψ hzero N hN j hsupport
              rw [mem_ball, dist_eq_norm] at hdir
              have hc := hbound w γ R hw hwγ hγ₁ hR ξ y (angularGridPoint N j)
                (4 * Real.pi / N) r k hrad (by simpa [abs_of_pos hrs.1] using hrs.2)
                (by positivity) hdir.le hremote
              simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
              exact (mul_le_mul (norm_sourcePacketSpectrum_le μ cap ξ) hc
                (norm_nonneg _) (mul_nonneg (norm_nonneg _) hmass)).trans_eq (by ring)
          _ = _ := integral_const_mul _ _
      exact (mul_le_mul_of_nonneg_left hint hrs.1.le).trans
        (mul_le_mul_of_nonneg_right hrs.2 (by positivity))
    · have hz : complexDistanceDensity f y r = 0 := by
        by_cases hr : 0 < r
        · exact image_eq_zero_of_notMem_tsupport (fun hx ↦ hrs ⟨hr, (hs hx).2⟩)
        · simp [complexDistanceDensity, hr]
      rw [hz, norm_zero]
      positivity
  have hi := integrable_complexDistanceDensity f.continuous.measurable f.integrable y
  have hb' := integral_norm_le_interval_length hi hs hb
  simp only [sub_zero, max_eq_left hLpos.le] at hb'
  exact hb'.trans_eq (by dsimp [D, cap]; ring)

end FalconerPacking
