import FalconerPacking.SmoothStripPartition
import FalconerPacking.CircularPlancherel

/-!
# Smooth unfolding of a periodic integral

A fixed smooth cutoff whose period translates sum to one converts a full-period integral
to a compactly supported whole-line integral, without introducing chart endpoint terms.
-/

open MeasureTheory Set Function
open scoped ContDiff

namespace FalconerPacking

/-- A smooth compact cutoff for unfolding an integral of period `T`. -/
noncomputable def smoothPeriodCutoff (T θ : ℝ) : ℝ := stripPartitionBump (θ / T)

theorem contDiff_smoothPeriodCutoff (T : ℝ) : ContDiff ℝ ∞ (smoothPeriodCutoff T) :=
  contDiff_stripPartitionBump.comp (contDiff_id.div_const T)

theorem support_smoothPeriodCutoff_subset {T : ℝ} (hT : 0 < T) :
    Function.support (smoothPeriodCutoff T) ⊆ Ioo (-T) T := by
  intro θ hθ
  have hs := support_stripPartitionBump hθ
  change -1 < θ / T ∧ θ / T < 1 at hs
  exact ⟨by have := (lt_div_iff₀ hT).mp hs.1; linarith,
    by have := (div_lt_iff₀ hT).mp hs.2; linarith⟩

theorem tsupport_smoothPeriodCutoff_subset {T : ℝ} (hT : 0 < T) :
    tsupport (smoothPeriodCutoff T) ⊆ Icc (-T) T :=
  closure_minimal ((support_smoothPeriodCutoff_subset hT).trans Ioo_subset_Icc_self) isClosed_Icc

theorem hasCompactSupport_smoothPeriodCutoff {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (smoothPeriodCutoff T) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((support_smoothPeriodCutoff_subset hT).trans Ioo_subset_Icc_self)

/-- On one period, the only two relevant translates add exactly to one, including endpoints. -/
theorem smoothPeriodCutoff_add_sub_period {T θ : ℝ} (hT : 0 < T) (hθ : θ ∈ Icc 0 T) :
    smoothPeriodCutoff T θ + smoothPeriodCutoff T (θ - T) = 1 := by
  have hq0 : 0 ≤ θ / T := div_nonneg hθ.1 hT.le
  have hq1 : θ / T ≤ 1 := (div_le_one hT).mpr hθ.2
  have he : (θ - T) / T = θ / T - 1 := by field_simp
  simp only [smoothPeriodCutoff, stripPartitionBump, he]
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ θ / T + 1),
    Real.smoothTransition.zero_of_nonpos (by linarith : θ / T - 1 ≤ 0)]
  rw [show θ / T - 1 + 1 = θ / T by ring]
  ring

/-- Exact smooth unfolding of one full period for continuous vector-valued functions. -/
theorem integral_period_eq_integral_smoothPeriodCutoff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} (hT : 0 < T)
    {f : ℝ → E} (hf : Continuous f) (hp : Periodic f T) :
    (∫ θ in (0 : ℝ)..T, f θ) = ∫ θ, smoothPeriodCutoff T θ • f θ := by
  have hg : Continuous (fun θ ↦ smoothPeriodCutoff T θ • f θ) :=
    (contDiff_smoothPeriodCutoff T).continuous.smul hf
  have hgsub : Continuous (fun θ ↦ smoothPeriodCutoff T (θ - T) • f (θ - T)) :=
    hg.comp (continuous_id.sub continuous_const)
  have he : (∫ θ in (-T)..T, smoothPeriodCutoff T θ • f θ) =
      ∫ θ, smoothPeriodCutoff T θ • f θ := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    have hz : smoothPeriodCutoff T θ = 0 := by
      by_contra hne
      exact hθ (Ioo_subset_Ioc_self (support_smoothPeriodCutoff_subset hT hne))
    rw [hz, zero_smul]
  rw [← he, ← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (-T) 0) (hg.intervalIntegrable 0 T)]
  have hshift : (∫ θ in (0 : ℝ)..T, smoothPeriodCutoff T (θ - T) • f (θ - T)) =
      ∫ θ in (-T)..0, smoothPeriodCutoff T θ • f θ := by
    simpa only [zero_sub, sub_self] using
      intervalIntegral.integral_comp_sub_right (a := 0) (b := T)
        (fun θ ↦ smoothPeriodCutoff T θ • f θ) T
  rw [← hshift, ← intervalIntegral.integral_add (hgsub.intervalIntegrable 0 T)
    (hg.intervalIntegrable 0 T)]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le hT.le] at hθ
  dsimp only
  rw [hp.sub_eq, ← add_smul, add_comm (smoothPeriodCutoff T (θ - T)),
    smoothPeriodCutoff_add_sub_period hT hθ, one_smul]

/-- The fixed angular chart can therefore be unfolded smoothly on the whole line. -/
theorem integral_radialAngularMeasure_eq_smoothPeriodCutoff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : Continuous f) (hp : Periodic f (2 * Real.pi)) :
    (∫ θ, f θ ∂radialAngularMeasure) =
      ∫ θ, smoothPeriodCutoff (2 * Real.pi) θ • f θ := by
  change (∫ θ in Ioc (-Real.pi) Real.pi, f θ) = _
  rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hperiod := hp.intervalIntegral_add_eq (-Real.pi) 0
  have hchart : (∫ θ in (-Real.pi)..Real.pi, f θ) = ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ := by
    convert hperiod using 1 <;> congr 1 <;> ring
  rw [hchart]
  exact integral_period_eq_integral_smoothPeriodCutoff (by positivity) hf hp

end FalconerPacking
