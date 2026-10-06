module

public import FalconerPacking.SmoothPeriodicUnfolding
public import FalconerPacking.CircularPacketAmplitude

/-!
# Remote-pin decay for the full circle integral of a spatial packet

A fixed smooth periodic cutoff unfolds the angular chart to the real line. Since nonstationarity
is needed only on the packet support, one whole-line integration-by-parts argument suffices.
-/

@[expose] public section

open MeasureTheory Set Function Finset
open scoped ContDiff RealInnerProductSpace

namespace FalconerPacking

/-- The fixed periodic cutoff has bounded derivatives of every prescribed finite order. -/
theorem exists_smoothPeriodCutoff_derivative_bound {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ N, ∀ θ, ‖iteratedDeriv k (smoothPeriodCutoff T) θ‖ ≤ C := by
  let f : SchwartzMap ℝ ℝ := (hasCompactSupport_smoothPeriodCutoff hT).toSchwartzMap
    (contDiff_smoothPeriodCutoff T)
  let D (k : ℕ) := SchwartzMap.seminorm ℝ 0 k f
  have hD : ∀ k, 0 ≤ D k := fun _ ↦ apply_nonneg _ _
  have hsum : 0 ≤ ∑ k ∈ range (N + 1), D k := sum_nonneg (fun k _ ↦ hD k)
  refine ⟨1 + ∑ k ∈ range (N + 1), D k, by linarith, ?_⟩
  intro k hk θ
  have hnorm : ‖iteratedDeriv k (smoothPeriodCutoff T) θ‖ ≤ D k := by
    have hcoe : (f : ℝ → ℝ) = smoothPeriodCutoff T := rfl
    rw [← hcoe]
    simpa only [pow_zero, one_mul] using SchwartzMap.le_seminorm' ℝ 0 k f θ
  have hsingle := single_le_sum (fun i (_ : i ∈ range (N + 1)) ↦ hD i)
    (show k ∈ range (N + 1) from Finset.mem_range.mpr (by omega))
  linarith

/-- The actual packet amplitude after smooth unfolding of the full circle. -/
noncomputable def unfoldedCirclePacketAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) (θ : ℝ) : ℂ :=
  (smoothPeriodCutoff (2 * Real.pi) θ : ℂ) * (circularPacketAmplitude χ w e y j r θ : ℂ)

theorem contDiff_unfoldedCirclePacketAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) :
    ContDiff ℝ ∞ (unfoldedCirclePacketAmplitude χ w e y j r) :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_smoothPeriodCutoff _)).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_circularPacketAmplitude χ w e y j r))

theorem hasCompactSupport_unfoldedCirclePacketAmplitude
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) :
    HasCompactSupport (unfoldedCirclePacketAmplitude χ w e y j r) :=
  ((hasCompactSupport_smoothPeriodCutoff (show 0 < 2 * Real.pi by positivity)).comp_left
    Complex.ofReal_zero).mul_right

theorem tsupport_unfoldedCirclePacketAmplitude_subset_interval
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) :
    tsupport (unfoldedCirclePacketAmplitude χ w e y j r) ⊆ Icc (-(2 * Real.pi)) (2 * Real.pi) :=
  tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero _).trans
    (tsupport_smoothPeriodCutoff_subset (by positivity)))

theorem tsupport_unfoldedCirclePacketAmplitude_subset_packet
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r : ℝ) :
    tsupport (unfoldedCirclePacketAmplitude χ w e y j r) ⊆
      tsupport (circularPacketAmplitude χ w e y j r) :=
  tsupport_mul_subset_right.trans (tsupport_comp_subset Complex.ofReal_zero _)

/-- The fixed unfolding cutoff leaves the width exponent unchanged. -/
theorem exists_unfoldedCirclePacketAmplitude_derivative_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (N : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 0 < w → w ≤ 1 →
      ∀ e y : EuclideanSpace ℝ (Fin 2), ‖e‖ ≤ 1 → ∀ (j : ℤ) (r : ℝ), |r| ≤ R →
        ∀ k ≤ N, ∀ θ, ‖iteratedDeriv k (unfoldedCirclePacketAmplitude χ w e y j r) θ‖ ≤
          C * w⁻¹ ^ k := by
  obtain ⟨B, hB, hb⟩ := exists_circularPacketAmplitude_derivative_bound χ N R
  obtain ⟨E, hE, he⟩ := exists_smoothPeriodCutoff_derivative_bound
    (show 0 < 2 * Real.pi by positivity) N
  refine ⟨2 ^ N * E * B, by positivity, ?_⟩
  intro w hw hw₁ e y hen j r hr k hk θ
  have hwinv : 1 ≤ w⁻¹ := (one_le_inv₀ hw).mpr hw₁
  have h := norm_iteratedDeriv_mul_le
    (Complex.ofRealCLM.contDiff.comp (contDiff_smoothPeriodCutoff (2 * Real.pi)))
    (Complex.ofRealCLM.contDiff.comp (contDiff_circularPacketAmplitude χ w e y j r))
    hE.le (show 0 ≤ w⁻¹ by positivity) k θ
    (fun i hi ↦ by
      change ‖iteratedDeriv i (fun t ↦ (smoothPeriodCutoff (2 * Real.pi) t : ℂ)) θ‖ ≤ _
      rw [iteratedDeriv_ofReal (contDiff_smoothPeriodCutoff _), Complex.norm_real]
      exact (he i (hi.trans hk) θ).trans (le_mul_of_one_le_right hE.le (one_le_pow₀ hwinv)))
    (fun i hi ↦ by
      change ‖iteratedDeriv i (fun t ↦ (circularPacketAmplitude χ w e y j r t : ℂ)) θ‖ ≤ _
      rw [iteratedDeriv_ofReal (contDiff_circularPacketAmplitude χ w e y j r), Complex.norm_real]
      exact hb w hw hw₁ e y hen j r hr i (hi.trans hk) θ)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hE.le) hB.le)
    (by positivity))

/-- Exact unfolding for the actual oscillatory packet integrand over the full angular chart. -/
theorem integral_circle_packet_eq_unfolded
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (w : ℝ)
    (e y z : EuclideanSpace ℝ (Fin 2)) (j : ℤ) (r t : ℝ) :
    (∫ θ, oscillatoryPhase (circularPhase z) t θ *
      (circularPacketAmplitude χ w e y j r θ : ℂ) ∂radialAngularMeasure) =
    ∫ θ, oscillatoryPhase (circularPhase z) t θ *
      unfoldedCirclePacketAmplitude χ w e y j r θ := by
  have hc : Continuous (fun θ ↦ oscillatoryPhase (circularPhase z) t θ *
      (circularPacketAmplitude χ w e y j r θ : ℂ)) :=
    (contDiff_oscillatoryPhase (contDiff_circularPhase z) t).continuous.mul
      (Complex.continuous_ofReal.comp (contDiff_circularPacketAmplitude χ w e y j r).continuous)
  have hp : Periodic (fun θ ↦ oscillatoryPhase (circularPhase z) t θ *
      (circularPacketAmplitude χ w e y j r θ : ℂ)) (2 * Real.pi) := by
    intro θ
    simp only [oscillatoryPhase, circularPhase, circularPacketAmplitude, angularDirection,
      Real.cos_add_two_pi, Real.sin_add_two_pi]
  rw [integral_radialAngularMeasure_eq_smoothPeriodCutoff hc hp]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [unfoldedCirclePacketAmplitude, Complex.real_smul]
  ring

/-- Full-circle remote-pin decay for actual packets, with uniform constants and no endpoint loss. -/
theorem exists_remote_circularPacket_circle_integral_bound
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (N : ℕ) (R S : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w γ : ℝ), 0 < w → w ≤ γ → γ ≤ 1 →
      ∀ (v y : EuclideanSpace ℝ (Fin 2)) (α ε r : ℝ) (j : ℤ),
        |r| ≤ R → ‖r • v‖ ≤ S → ‖v - angularDirection α‖ ≤ ε →
        γ + w + |r| * ε ≤ |⟪angularDirection (α + Real.pi / 2), y⟫ - w * j| →
        ∀ t : ℝ, t ≠ 0 →
          ‖∫ θ, oscillatoryPhase (circularPhase (r • v)) t θ *
            (circularPacketAmplitude χ w (angularDirection (α + Real.pi / 2)) y j r θ : ℂ)
              ∂radialAngularMeasure‖ ≤ C * (|t| * w * γ)⁻¹ ^ N := by
  obtain ⟨B, hB, hbound⟩ := exists_unfoldedCirclePacketAmplitude_derivative_bound χ N R
  let Q := circularReciprocalDerivativeBound N S
  have hQ : 0 < Q := circularReciprocalDerivativeBound_pos N S
  refine ⟨(4 * Real.pi) * (2 ^ N * Q) ^ N * B, by positivity, ?_⟩
  intro w γ hw hwγ hγ₁ v y α ε r j hr hrv hnear hremote t ht
  have hγ : 0 < γ := hw.trans_le hwγ
  have hqφ : ∀ θ ∈ tsupport
      (unfoldedCirclePacketAmplitude χ w (angularDirection (α + Real.pi / 2)) y j r),
      circularReciprocal γ (r • v) θ * deriv (circularPhase (r • v)) θ = 1 := by
    intro θ hθ
    apply circularReciprocal_mul_deriv_eq_one (r • v) hγ
    exact le_abs_deriv_circularPhase_of_packet_support χ hw hnear hremote
      (tsupport_unfoldedCirclePacketAmplitude_subset_packet χ w _ y j r hθ)
  rw [integral_circle_packet_eq_unfolded]
  have h := norm_integral_oscillatoryPhase_mul_scale_le
    (contDiff_circularPhase (r • v)) (contDiff_circularReciprocal γ (r • v))
    (contDiff_unfoldedCirclePacketAmplitude χ w _ y j r)
    (hasCompactSupport_unfoldedCirclePacketAmplitude χ w _ y j r) hqφ hQ.le hB.le hw hγ
    (tsupport_unfoldedCirclePacketAmplitude_subset_interval χ w _ y j r) N
    (fun k hk θ ↦ norm_iteratedDeriv_circularReciprocal_scale_le (r • v) hw hwγ hγ₁ hrv hk θ)
    (hbound w hw (hwγ.trans hγ₁) _ y (by simp) j r hr) ht
  simpa only [sub_neg_eq_add, show 2 * Real.pi + 2 * Real.pi = 4 * Real.pi by ring,
    max_eq_left (show 0 ≤ 4 * Real.pi by positivity)] using h

end FalconerPacking
