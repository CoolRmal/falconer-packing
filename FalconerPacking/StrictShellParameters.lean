/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ProfileMarginParameters
public import FalconerPacking.RegularProfileParameters

/-!
# Choosing thresholds for strict-profile shell decay

The coefficient `A` bounds the finitely many enlargement and marking losses after the chain
length is fixed. The independent exponent `P` bounds the polynomial counts and norms multiplying
kernel tails. The two displayed bad exponents are respectively the source-heavy and pin-heavy
terms, after packet multiplicity. The good exponent retains the cost of every edge threshold.
No analytic estimate is assumed proved by these scalar inequalities.
-/

@[expose] public section

noncomputable section

open Filter

namespace FalconerPacking

/-- Choose source and pin thresholds, then the packet width and normalization loss. All finite
chain losses and any prescribed polynomial kernel loss have explicit strictly negative margins.
The packet width is a reciprocal integer; its integer is independent of the regularization block. -/
theorem exists_shell_threshold_parameters {η q A P ε : ℝ}
    (hη : 0 < η) (hq : 1 < q) (hA : 1 ≤ A) (_hP : 0 ≤ P) (hε : 0 < ε) (K : ℕ) :
    ∃ J : ℕ, 4 ≤ J ∧ ∃ D₁ D₂ h ρ : ℝ, h = 1 / (4 * J) ∧
      0 < D₁ ∧ 0 < D₂ ∧ 0 < h ∧ h ≤ 1 / 16 ∧
      0 < ρ ∧ ρ ≤ ε ∧ 4 * A * ρ ≤ h ∧
      (A + K * (A + D₂)) * h + A * (K + 1) * ρ ≤ η / 8 ∧
      (A - (q - 1) * D₁) * h + A * ρ ≤ -2 * h ∧
      (A + D₁ - D₂) * h + A * ρ ≤ -2 * h ∧
      ∃ p n : ℕ, p + 4 * K + 20 ≤ n ∧ p ≤ 2 * n ∧
        P + K * (1 + (A + D₂) * h + A * ρ) + 4 - p * h < -2 := by
  let D₁ := (A + 4) / (q - 1)
  let D₂ := D₁ + A + 4
  have hA₀ : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hD₁ : 0 < D₁ := by dsimp [D₁]; positivity
  have hD₂ : 0 < D₂ := by dsimp [D₂]; positivity
  have hD₁eq : (q - 1) * D₁ = A + 4 := by
    dsimp [D₁]
    field_simp [ne_of_gt (sub_pos.mpr hq)]
  let B := A + (K : ℝ) * (A + D₂) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 4 (4 * B / η))
  have hJ₄ : (4 : ℝ) ≤ J := ((le_max_left _ _).trans_lt hJ).le
  have hJ₀ : (0 : ℝ) < J := by linarith
  let h := 1 / (4 * (J : ℝ))
  have hh : 0 < h := by dsimp [h]; positivity
  have hh₁ : h ≤ 1 / 16 := by
    dsimp [h]
    rw [div_le_div_iff₀ (by positivity : 0 < 4 * (J : ℝ)) (by norm_num)]
    linarith
  have hhη : 16 * B * h ≤ η := by
    have ht := (div_lt_iff₀ hη).mp ((le_max_right _ _).trans_lt hJ)
    have hid : 16 * B * h = 4 * B / J := by
      dsimp [h]
      field_simp
      ring
    rw [hid, div_le_iff₀ hJ₀]
    nlinarith
  let ρ := min ε (min (h / (4 * A)) (η / (16 * A * (K + 1))))
  have hρ : 0 < ρ := lt_min hε (lt_min (by positivity) (by positivity))
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρh : 4 * A * ρ ≤ h := by
    have hr₂ : ρ ≤ h / (4 * A) := (min_le_right _ _).trans (min_le_left _ _)
    have hr := (le_div_iff₀ (by positivity : 0 < 4 * A)).mp hr₂
    nlinarith
  have hρη : 16 * A * (K + 1) * ρ ≤ η := by
    have hr₂ : ρ ≤ η / (16 * A * (K + 1)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hr := (le_div_iff₀ (by positivity : 0 < 16 * A * ((K : ℝ) + 1))).mp hr₂
    nlinarith
  refine ⟨J, by exact_mod_cast hJ₄, D₁, D₂, h, ρ, rfl,
    hD₁, hD₂, hh, hh₁, hρ, hρε, hρh, ?_, ?_, ?_, ?_⟩
  · dsimp [B] at hhη
    nlinarith
  · rw [hD₁eq]
    nlinarith
  · dsimp [D₂]
    nlinarith
  · obtain ⟨p, hp⟩ := exists_nat_gt ((P + K * (1 + (A + D₂) * h + A * ρ) + 6) / h)
    refine ⟨p, p + 4 * K + 20, le_rfl, by omega, ?_⟩
    have hp' := (div_lt_iff₀ hh).mp hp
    nlinarith

/-- A strict chain cost leaves a negative squared-density exponent after initial localization,
all edge threshold losses, and the logarithmic-depth factors have been included. -/
theorem strict_chain_shell_exponent_le {s η initial inflation depthLoss : ℝ}
    {N n : ℕ} {g : ℕ → ℝ} {l : List ℕ} (hN : 0 < N)
    (hcost : chainCost g n l ≤ (s - 1 - η) * N)
    (hinitial : initial ≤ η / 8) (hinflation : inflation ≤ η / 8)
    (hdepth : depthLoss ≤ η / 4) :
    1 - s + chainCost g n l / N + initial + inflation + depthLoss ≤ -η / 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := (div_le_iff₀ hN').mpr hcost
  linarith

/-- Once the regularization supplies its positive remainder exponent, all good, bad, and
kernel exponents can use a single positive dyadic decay rate. -/
theorem exists_common_shell_decay {η h θ g b₁ b₂ k : ℝ}
    (hη : 0 < η) (hh : 0 < h) (hθ : 0 < θ)
    (hg : g ≤ -η / 2) (hb₁ : b₁ ≤ -h) (hb₂ : b₂ ≤ -h) (hk : k ≤ -1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ η / 2 ∧ δ ≤ h ∧ δ ≤ θ ∧ δ ≤ 1 ∧
      g ≤ -δ ∧ b₁ ≤ -δ ∧ b₂ ≤ -δ ∧ k ≤ -δ ∧ -θ ≤ -δ := by
  let δ := min (η / 2) (min h (min θ 1))
  have hδ : 0 < δ := lt_min (half_pos hη) (lt_min hh (lt_min hθ zero_lt_one))
  have hδη : δ ≤ η / 2 := min_le_left _ _
  have hδh : δ ≤ h := (min_le_right _ _).trans (min_le_left _ _)
  have hδθ : δ ≤ θ := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₁ : δ ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨δ, hδ, hδη, hδh, hδθ, hδ₁, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

/-- The actual finite-regularization factor, discarded mass, normalization exponent, and both
profile barrier errors can all be chosen with the requested tolerance. The output block may
exceed any prescribed starting block, and the depth may exceed the strict-chain starting depth. -/
theorem exists_regularization_parameters_for_barriers {ε ρ c₀ c₁ : ℝ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hρε : ρ ≤ ε / 2)
    (hc₀ : 0 ≤ c₀) (_hc₁ : 0 ≤ c₁) (T₀ Lpre : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ 2 * θ ≤ ρ ∧ ∃ T L₀ : ℕ,
      T₀ ≤ T ∧ 2 ≤ T ∧ Lpre ≤ L₀ ∧ 0 < L₀ ∧
      (2 * (2 * T + 1) ^ 2 : ℝ) ≤ (2 : ℝ) ^ (θ * T) ∧
      ∀ L : ℕ, L₀ ≤ L →
        (2 * L + c₀ + ρ * T * L) / T ≤ ε * L ∧
        (L + c₁) / T ≤ ε * L ∧
        (2 * (2 * T + 1) ^ 2 : ℝ) ^ L * (2 : ℝ) ^ (-(ρ * T * L)) ≤
          (2 : ℝ) ^ (-(θ * T * L)) := by
  let θ := min ε ρ / 8
  have hθ : 0 < θ := div_pos (lt_min hε hρ) (by norm_num)
  have hθε : 4 * θ ≤ ε := by dsimp [θ]; linarith [min_le_left ε ρ]
  have hθρ : 2 * θ ≤ ρ := by dsimp [θ]; linarith [min_le_right ε ρ]
  obtain ⟨T, hT₀, hT, hθT, hpoly⟩ := exists_regularization_block hθ T₀
  have hT' : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  obtain ⟨N, hN⟩ := exists_nat_gt (max c₀ c₁ / (θ * T))
  let L₀ := max Lpre (max 1 N)
  refine ⟨θ, hθ, hθρ, T, L₀, hT₀, hT, le_max_left _ _, by dsimp [L₀]; omega,
    hpoly, fun L hL ↦ ?_⟩
  have hNL : (N : ℝ) ≤ L := by exact_mod_cast (show N ≤ L by dsimp [L₀] at hL; omega)
  have hcmax : max c₀ c₁ ≤ θ * T * L := by
    have hm := (div_lt_iff₀ (mul_pos hθ hT')).mp hN
    nlinarith
  have hc₀L := (le_max_left c₀ c₁).trans hcmax
  have hc₁L := (le_max_right c₀ c₁).trans hcmax
  have hTL : 0 ≤ (T : ℝ) * L := by positivity
  have hTLL := mul_le_mul_of_nonneg_right hθT (Nat.cast_nonneg L)
  have hεL := mul_le_mul_of_nonneg_right hθε hTL
  have hρL := mul_le_mul_of_nonneg_right hρε hTL
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hT']
    nlinarith
  · rw [div_le_iff₀ hT']
    nlinarith
  · have hp : (2 * (2 * T + 1) ^ 2 : ℝ) ^ L ≤ (2 : ℝ) ^ (θ * T * L) := by
      rw [Real.rpow_mul_natCast (by norm_num)]
      exact pow_le_pow_left₀ (by positivity) hpoly L
    calc
      _ ≤ (2 : ℝ) ^ (θ * T * L) * (2 : ℝ) ^ (-(ρ * T * L)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = (2 : ℝ) ^ (θ * T * L - ρ * T * L) := by
        rw [← Real.rpow_add (by norm_num), sub_eq_add_neg]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_right hθρ hTL]

/-- Every fixed polynomial in the logarithmic shell depth is absorbed by an arbitrarily
small positive dyadic exponent. This treats the conditional energy's depth factor. -/
theorem eventually_polynomial_le_dyadic {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) + 1) ^ k ≤ (2 : ℝ) ^ (δ * n) := by
  let A := (C + 1) * (2 : ℝ) ^ k
  have hA : 0 < A := by dsimp [A]; positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop k
    (mul_pos hδ (Real.log_pos (by norm_num : (1 : ℝ) < 2)))).bound (one_div_pos.mpr hA)
  have hn := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [hn, eventually_ge_atTop 1] with n hn hn₁
  have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  simp only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) ^ k by positivity),
    abs_of_pos (Real.exp_pos _)] at hn
  have hdiv : (n : ℝ) ^ k ≤ Real.exp (δ * Real.log 2 * n) / A := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hn
  have hmul := (le_div_iff₀ hA).mp hdiv
  calc
    C * ((n : ℝ) + 1) ^ k ≤ C * (2 * n) ^ k := by gcongr; linarith
    _ = C * 2 ^ k * (n : ℝ) ^ k := by rw [mul_pow]; ring
    _ ≤ A * (n : ℝ) ^ k := by dsimp [A]; gcongr; linarith
    _ ≤ Real.exp (δ * Real.log 2 * n) := by simpa only [mul_comm] using hmul
    _ = (2 : ℝ) ^ (δ * n) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      ring

end FalconerPacking
