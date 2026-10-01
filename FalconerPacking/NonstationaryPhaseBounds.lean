import FalconerPacking.NonstationaryPhase
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Uniform derivative bounds for nonstationary transport

Leibniz's formula preserves the derivative scale: one transport step costs exactly one
power of the amplitude scale and one power of the inverse phase derivative.
-/

open MeasureTheory Set Function Finset
open scoped ContDiff

namespace FalconerPacking

/-- Real-to-complex coercion commutes with all derivatives of a smooth real function. -/
theorem iteratedDeriv_ofReal {q : ℝ → ℝ} (hq : ContDiff ℝ ∞ q) (k : ℕ) :
    iteratedDeriv k (fun x ↦ (q x : ℂ)) = fun x ↦ ((iteratedDeriv k q x : ℝ) : ℂ) := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [iteratedDeriv_succ]
    exact ((hq.differentiable_iteratedDeriv k
      (by exact_mod_cast ENat.coe_lt_top k) x).hasDerivAt.ofReal_comp).deriv

/-- The binomial sum costs `2^k`, without any loss in the derivative scale. -/
theorem norm_iteratedDeriv_mul_le {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {B C D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (k : ℕ) (x : ℝ)
    (hfB : ∀ i ≤ k, ‖iteratedDeriv i f x‖ ≤ B * D ^ i)
    (hgC : ∀ i ≤ k, ‖iteratedDeriv i g x‖ ≤ C * D ^ i) :
    ‖iteratedDeriv k (f * g) x‖ ≤ 2 ^ k * B * C * D ^ k := by
  rw [iteratedDeriv_mul (hf.of_le (m := k) (by exact_mod_cast le_top)).contDiffAt
    (hg.of_le (m := k) (by exact_mod_cast le_top)).contDiffAt]
  calc
    _ ≤ ∑ i ∈ range (k + 1), ‖(k.choose i : ℂ) *
        iteratedDeriv i f x * iteratedDeriv (k - i) g x‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (k + 1), (k.choose i : ℝ) * (B * C * D ^ k) := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (k.choose i : ℝ) * (B * D ^ i) * (C * D ^ (k - i)) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hfB i hik) (by positivity))
            (hgC (k - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
        _ = _ := by
          have hp : D ^ k = D ^ i * D ^ (k - i) := by
            rw [← pow_add, Nat.add_sub_of_le hik]
          rw [hp]
          ring
    _ = 2 ^ k * B * C * D ^ k := by
      rw [← sum_mul]
      have hs : (∑ i ∈ range (k + 1), (k.choose i : ℝ)) = 2 ^ k := by
        exact_mod_cast Nat.sum_range_choose k
      rw [hs]
      ring

/-- Derivatives of every transported amplitude, with one scale factor per transport step. -/
theorem norm_iteratedDeriv_nonstationaryAmplitude_iterate_le
    {q : ℝ → ℝ} {a : ℝ → ℂ} (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (N : ℕ) (hqB : ∀ k ≤ N, ∀ x, ‖iteratedDeriv k q x‖ ≤ B * D ^ k)
    (haA : ∀ k ≤ N, ∀ x, ‖iteratedDeriv k a x‖ ≤ A * D ^ k)
    (n k : ℕ) (hnk : n + k ≤ N) (x : ℝ) :
    ‖iteratedDeriv k ((nonstationaryAmplitude q)^[n] a) x‖ ≤
      (2 ^ N * B * D) ^ n * A * D ^ k := by
  induction n generalizing k with
  | zero => simpa using haA k (by simpa using hnk) x
  | succ n ih =>
    have hk : k + 1 ≤ N := by omega
    obtain ⟨hNa, _, _⟩ := nonstationaryAmplitude_iterate_properties hq ha hac n
    rw [Function.iterate_succ_apply', nonstationaryAmplitude, ← iteratedDeriv_succ']
    have hp := norm_iteratedDeriv_mul_le (Complex.ofRealCLM.contDiff.comp hq) hNa
      hB hD (k + 1) x
      (fun i hi ↦ by
        change ‖iteratedDeriv i (fun x ↦ (q x : ℂ)) x‖ ≤ _
        rw [iteratedDeriv_ofReal hq, Complex.norm_real]
        exact hqB i (hi.trans hk) x)
      (fun i hi ↦ ih i (by omega))
    calc
      _ ≤ 2 ^ (k + 1) * B * ((2 ^ N * B * D) ^ n * A) * D ^ (k + 1) := hp
      _ ≤ 2 ^ N * B * ((2 ^ N * B * D) ^ n * A) * D ^ (k + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hB)
            (by positivity)) (by positivity)
      _ = _ := by rw [pow_succ, pow_succ]; ring

/-- The two-scale form: only `n + k` powers of the amplitude scale occur. -/
theorem norm_iteratedDeriv_nonstationaryAmplitude_iterate_scale_le
    {q : ℝ → ℝ} {a : ℝ → ℂ} (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a)
    (hac : HasCompactSupport a) {Q A δ γ : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hγ : 0 < γ) (N : ℕ)
    (hqQ : ∀ k ≤ N, ∀ x, ‖iteratedDeriv k q x‖ ≤ Q * γ⁻¹ * δ⁻¹ ^ k)
    (haA : ∀ k ≤ N, ∀ x, ‖iteratedDeriv k a x‖ ≤ A * δ⁻¹ ^ k)
    (n k : ℕ) (hnk : n + k ≤ N) (x : ℝ) :
    ‖iteratedDeriv k ((nonstationaryAmplitude q)^[n] a) x‖ ≤
      (2 ^ N * Q) ^ n * A * γ⁻¹ ^ n * δ⁻¹ ^ (n + k) := by
  have h := norm_iteratedDeriv_nonstationaryAmplitude_iterate_le hq ha hac
    (show 0 ≤ Q * γ⁻¹ by positivity) hA (show 0 ≤ δ⁻¹ by positivity) N hqQ haA n k hnk x
  convert h using 1
  simp only [mul_pow, pow_add]
  ring

/-- A bounded, integrable function supported in an interval has the expected `L¹` bound. -/
theorem integral_norm_le_interval_length {b : ℝ → ℂ} (hb : Integrable b)
    {l r C : ℝ} (hs : tsupport b ⊆ Icc l r) (hC : ∀ x, ‖b x‖ ≤ C) :
    (∫ x, ‖b x‖) ≤ max (r - l) 0 * C := by
  have he : (∫ x in Icc l r, ‖b x‖) = ∫ x, ‖b x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), norm_zero]
  rw [← he]
  calc
    _ ≤ ∫ _ in Icc l r, C :=
      setIntegral_mono_on hb.norm.integrableOn (integrableOn_const isCompact_Icc.measure_ne_top)
        measurableSet_Icc (fun x _ ↦ hC x)
    _ = _ := by simp only [integral_const, Measure.restrict_apply_univ, Measure.real,
      Real.volume_Icc, ENNReal.toReal_ofReal', smul_eq_mul]

/-- Nonstationary decay with the sharp combined frequency and derivative-scale factor. -/
theorem norm_integral_oscillatoryPhase_mul_scale_le
    {φ q : ℝ → ℝ} {a : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hq : ContDiff ℝ ∞ q) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hqφ : ∀ x ∈ tsupport a, q x * deriv φ x = 1)
    {Q A δ γ l r : ℝ} (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hδ : 0 < δ) (hγ : 0 < γ)
    (hs : tsupport a ⊆ Icc l r) (N : ℕ)
    (hqQ : ∀ k ≤ N, ∀ x, ‖iteratedDeriv k q x‖ ≤ Q * γ⁻¹ * δ⁻¹ ^ k)
    (haA : ∀ k ≤ N, ∀ x, ‖iteratedDeriv k a x‖ ≤ A * δ⁻¹ ^ k)
    {t : ℝ} (ht : t ≠ 0) :
    ‖∫ x, oscillatoryPhase φ t x * a x‖ ≤
      max (r - l) 0 * (2 ^ N * Q) ^ N * A * (|t| * δ * γ)⁻¹ ^ N := by
  have hNs := (nonstationaryAmplitude_iterate_properties hq ha hac N).2.2
  have hNbound : ∀ x, ‖((nonstationaryAmplitude q)^[N] a) x‖ ≤
      (2 ^ N * Q) ^ N * A * γ⁻¹ ^ N * δ⁻¹ ^ N := by
    intro x
    simpa only [iteratedDeriv_zero, Nat.add_zero] using
      norm_iteratedDeriv_nonstationaryAmplitude_iterate_scale_le hq ha hac
        hQ hA hδ hγ N hqQ haA N 0 (by omega) x
  calc
    _ ≤ |t|⁻¹ ^ N * ∫ x, ‖((nonstationaryAmplitude q)^[N] a) x‖ :=
      norm_integral_oscillatoryPhase_mul_le hφ hq ha hac hqφ ht N
    _ ≤ |t|⁻¹ ^ N * (max (r - l) 0 *
        ((2 ^ N * Q) ^ N * A * γ⁻¹ ^ N * δ⁻¹ ^ N)) :=
      mul_le_mul_of_nonneg_left
        (integral_norm_le_interval_length
          (integrable_nonstationaryAmplitude_iterate hq ha hac N) (hNs.trans hs) hNbound)
        (by positivity)
    _ = _ := by simp only [mul_inv_rev, mul_pow]; ring

end FalconerPacking
