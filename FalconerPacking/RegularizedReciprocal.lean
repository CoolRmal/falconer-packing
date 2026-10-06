module

public import FalconerPacking.NonstationaryPhaseBounds
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A smooth reciprocal with uniform derivative bounds

The reciprocal is cut off near zero. Its derivatives are bounded on a fixed compact interval;
outside that interval they are exactly the derivatives of the ordinary reciprocal.
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped ContDiff Topology

namespace FalconerPacking

/-- A fixed smooth reciprocal, zero near the singularity. -/
noncomputable def regularizedReciprocal (x : ℝ) : ℝ :=
  Real.smoothTransition (4 * x ^ 2 - 1) / x

theorem regularizedReciprocal_eq_zero {x : ℝ} (hx : |x| ≤ 1 / 2) :
    regularizedReciprocal x = 0 := by
  have hx2 : x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg x) hx 2
  rw [regularizedReciprocal, Real.smoothTransition.zero_of_nonpos (by nlinarith), zero_div]

theorem regularizedReciprocal_eq_inv {x : ℝ} (hx : 1 ≤ |x|) :
    regularizedReciprocal x = x⁻¹ := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  rw [regularizedReciprocal, Real.smoothTransition.one_of_one_le (by nlinarith), one_div]

/-- The cutoff cancels the singularity at zero, giving a globally smooth function. -/
theorem contDiff_regularizedReciprocal : ContDiff ℝ ∞ regularizedReciprocal := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro y hy
    exact regularizedReciprocal_eq_zero (by simpa only [dist_zero_right, Real.norm_eq_abs]
      using hy.le)
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ ↦ Real.smoothTransition (4 * y ^ 2 - 1)) :=
      Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul (contDiff_id.pow 2)).sub contDiff_const)
    exact hnum.contDiffAt.div contDiffAt_id hx

/-- Away from the cutoff, all derivatives are exactly those of the inverse function. -/
theorem iteratedDeriv_regularizedReciprocal_of_one_lt_abs (k : ℕ) {x : ℝ}
    (hx : 1 < |x|) :
    iteratedDeriv k regularizedReciprocal x =
      (-1 : ℝ) ^ k * k.factorial * x ^ (-1 - (k : ℤ)) := by
  have he : regularizedReciprocal =ᶠ[𝓝 x] Inv.inv := by
    filter_upwards [(continuous_abs.tendsto x).eventually (eventually_gt_nhds hx)] with y hy
    exact regularizedReciprocal_eq_inv hy.le
  rw [he.iteratedDeriv_eq k, iteratedDeriv_eq_iterate, iter_deriv_inv]

/-- Outside the fixed interval, the derivative is bounded by the factorial coefficient. -/
theorem norm_iteratedDeriv_regularizedReciprocal_tail_le (k : ℕ) {x : ℝ}
    (hx : 1 < |x|) :
    ‖iteratedDeriv k regularizedReciprocal x‖ ≤ k.factorial := by
  rw [iteratedDeriv_regularizedReciprocal_of_one_lt_abs k hx]
  have he : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast, norm_mul, norm_mul, norm_pow, norm_inv, norm_pow]
  rw [Real.norm_natCast]
  simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
  apply mul_le_of_le_one_right (by positivity)
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx.le)

/-- Every derivative has a fixed finite global bound. -/
theorem exists_regularizedReciprocal_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖iteratedDeriv k regularizedReciprocal x‖ ≤ C := by
  have hcont : Continuous (iteratedDeriv k regularizedReciprocal) :=
    contDiff_regularizedReciprocal.continuous_iteratedDeriv k (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-2 : ℝ) 2) hcont.continuousOn
  refine ⟨max B k.factorial + 1, by positivity, ?_⟩
  intro x
  by_cases hx : x ∈ Icc (-2 : ℝ) 2
  · exact (hB x hx).trans (by linarith [le_max_left B (k.factorial : ℝ)])
  · have habs : 1 < |x| := by
      rw [mem_Icc, not_and_or] at hx
      rcases hx with hx | hx
      · have := neg_le_abs x
        linarith
      · have := le_abs_self x
        linarith
    exact (norm_iteratedDeriv_regularizedReciprocal_tail_le k habs).trans
      (by linarith [le_max_right B (k.factorial : ℝ)])

/-- A positive bound for the `k`-th derivative of the fixed regularized reciprocal. -/
noncomputable def regularizedReciprocalDerivativeBound (k : ℕ) : ℝ :=
  (exists_regularizedReciprocal_derivative_bound k).choose

theorem regularizedReciprocalDerivativeBound_pos (k : ℕ) :
    0 < regularizedReciprocalDerivativeBound k :=
  (exists_regularizedReciprocal_derivative_bound k).choose_spec.1

theorem norm_iteratedDeriv_regularizedReciprocal_le (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k regularizedReciprocal x‖ ≤ regularizedReciprocalDerivativeBound k :=
  (exists_regularizedReciprocal_derivative_bound k).choose_spec.2 x

/-- The reciprocal cutoff at scale `γ`. -/
noncomputable def scaledRegularizedReciprocal (γ x : ℝ) : ℝ :=
  γ⁻¹ * regularizedReciprocal (γ⁻¹ * x)

theorem contDiff_scaledRegularizedReciprocal (γ : ℝ) :
    ContDiff ℝ ∞ (scaledRegularizedReciprocal γ) :=
  contDiff_const.mul
    (contDiff_regularizedReciprocal.comp (contDiff_const.mul contDiff_id))

theorem scaledRegularizedReciprocal_eq_inv {γ x : ℝ} (hγ : 0 < γ) (hx : γ ≤ |x|) :
    scaledRegularizedReciprocal γ x = x⁻¹ := by
  have hscale : 1 ≤ |γ⁻¹ * x| := by
    simpa only [abs_mul, abs_inv, abs_of_pos hγ, div_eq_mul_inv, mul_comm] using
      (one_le_div hγ).mpr hx
  rw [scaledRegularizedReciprocal, regularizedReciprocal_eq_inv hscale,
    mul_inv_rev, inv_inv]
  field_simp

theorem scaledRegularizedReciprocal_mul_eq_one {γ x : ℝ}
    (hγ : 0 < γ) (hx : γ ≤ |x|) : scaledRegularizedReciprocal γ x * x = 1 := by
  have hx0 : x ≠ 0 := by intro he; simp [he] at hx; linarith
  rw [scaledRegularizedReciprocal_eq_inv hγ hx, inv_mul_cancel₀ hx0]

theorem scaledRegularizedReciprocal_eq_zero {γ x : ℝ} (hγ : 0 < γ)
    (hx : |x| ≤ γ / 2) : scaledRegularizedReciprocal γ x = 0 := by
  have hscale : |γ⁻¹ * x| ≤ 1 / 2 := by
    have hdiv : |x| / γ ≤ 1 / 2 := (div_le_iff₀ hγ).mpr (by linarith)
    simpa only [abs_mul, abs_inv, abs_of_pos hγ, div_eq_mul_inv, mul_comm] using hdiv
  rw [scaledRegularizedReciprocal, regularizedReciprocal_eq_zero hscale, mul_zero]

/-- Exact derivative scaling; the constants are independent of the scale. -/
theorem iteratedDeriv_scaledRegularizedReciprocal (γ : ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (scaledRegularizedReciprocal γ) x =
      γ⁻¹ ^ (k + 1) * iteratedDeriv k regularizedReciprocal (γ⁻¹ * x) := by
  change iteratedDeriv k (fun y ↦ γ⁻¹ * regularizedReciprocal (γ⁻¹ * y)) x = _
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul
      (contDiff_regularizedReciprocal.of_le (m := k) (by exact_mod_cast le_top))]
  simp only [pow_succ]
  ring

/-- A quantitative derivative bound with the exact inverse-scale exponent. -/
theorem norm_iteratedDeriv_scaledRegularizedReciprocal_le {γ : ℝ} (hγ : 0 < γ)
    (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (scaledRegularizedReciprocal γ) x‖ ≤
      regularizedReciprocalDerivativeBound k * γ⁻¹ ^ (k + 1) := by
  rw [iteratedDeriv_scaledRegularizedReciprocal, norm_mul, norm_pow, norm_inv,
    Real.norm_of_nonneg hγ.le]
  exact (mul_le_mul_of_nonneg_left (norm_iteratedDeriv_regularizedReciprocal_le k _)
    (by positivity)).trans_eq (mul_comm _ _)

/-- A single constant controls all derivative orders up to `N`. -/
noncomputable def regularizedReciprocalOrderBound (N : ℕ) : ℝ :=
  1 + ∑ k ∈ Finset.range (N + 1), regularizedReciprocalDerivativeBound k

theorem regularizedReciprocalOrderBound_pos (N : ℕ) :
    0 < regularizedReciprocalOrderBound N := by
  have hs : 0 ≤ ∑ k ∈ Finset.range (N + 1), regularizedReciprocalDerivativeBound k :=
    Finset.sum_nonneg (fun k _ ↦ (regularizedReciprocalDerivativeBound_pos k).le)
  unfold regularizedReciprocalOrderBound
  linarith

theorem regularizedReciprocalDerivativeBound_le_orderBound {k N : ℕ} (hk : k ≤ N) :
    regularizedReciprocalDerivativeBound k ≤ regularizedReciprocalOrderBound N := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (N + 1)) ↦
      (regularizedReciprocalDerivativeBound_pos i).le)
    (show k ∈ Finset.range (N + 1) from Finset.mem_range.mpr (by omega))
  unfold regularizedReciprocalOrderBound
  linarith

theorem norm_iteratedDeriv_scaledRegularizedReciprocal_le_orderBound {γ : ℝ}
    (hγ : 0 < γ) {k N : ℕ} (hk : k ≤ N) (x : ℝ) :
    ‖iteratedDeriv k (scaledRegularizedReciprocal γ) x‖ ≤
      regularizedReciprocalOrderBound N * γ⁻¹ ^ (k + 1) :=
  (norm_iteratedDeriv_scaledRegularizedReciprocal_le hγ k x).trans
    (mul_le_mul_of_nonneg_right (regularizedReciprocalDerivativeBound_le_orderBound hk)
      (by positivity))

end FalconerPacking
