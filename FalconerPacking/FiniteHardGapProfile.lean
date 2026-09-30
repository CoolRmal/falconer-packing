/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.HardGapProfile
import FalconerPacking.RealChainRounding
import FalconerPacking.HighSlopeProfile

/-!
# Uniform finite-grid hard-gap profile estimates

The actual real-profile chains are compressed and rounded. Endpoint clipping removes the
endpoint equality required by the low-side certificate. All hypotheses concern the finite
grid, and the chain length is uniform when its start stays a fixed proportion below the end.
-/

noncomputable section

namespace FalconerPacking

private theorem constantExtension_lipschitz_aux {g : ℕ → ℝ} {N : ℕ}
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) :
    ∀ j, |g (min (j + 1) N) - g (min j N)| ≤ 1 := by
  intro j
  by_cases hj : j < N
  · simpa only [min_eq_left (Nat.succ_le_of_lt hj), min_eq_left hj.le] using hlip j hj
  · have hNj : N ≤ j := Nat.le_of_not_gt hj
    simp only [min_eq_right hNj, min_eq_right (hNj.trans (Nat.le_succ j)),
      sub_self, abs_zero, zero_le_one]

/-- Endpoint clipping preserves the finite-grid Lipschitz bound. -/
theorem clip_lipschitz_of_finite {g : ℕ → ℝ} {N : ℕ}
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) (c : ℝ) {j : ℕ} (hj : j < N) :
    |min (g (j + 1)) (c - (j + 1 : ℕ)) - min (g j) (c - j)| ≤ 1 := by
  simpa only [min_eq_left (Nat.succ_le_of_lt hj), min_eq_left hj.le] using
    clip_lipschitz (g := fun i ↦ g (min i N)) (constantExtension_lipschitz_aux hlip) c j

/-- Every decreasing finite-grid chain costs no more before endpoint clipping. -/
theorem chainCost_le_clip_of_finite {g : ℕ → ℝ} {N : ℕ}
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) (c : ℝ)
    (n : ℕ) (l : List ℕ) (hn : n ≤ N)
    (hc : List.IsChain (fun n m ↦ m < n) (n :: l)) :
    chainCost g n l ≤ chainCost (fun j ↦ min (g j) (c - j)) n l := by
  rw [chainCost_eq_of_eq_le (g := g) (h := fun j ↦ g (min j N))
    (fun j hj ↦ by rw [min_eq_left hj]) n l hn hc]
  rw [chainCost_eq_of_eq_le (g := fun j ↦ min (g j) (c - j))
    (h := fun j ↦ min (g (min j N)) (c - j))
    (fun j hj ↦ by rw [min_eq_left hj]) n l hn hc]
  exact chainCost_le_clip (constantExtension_lipschitz_aux hlip) c n l hc

private theorem normalized_gap_scale_aux {N n k : ℕ} (hN : 0 < N) (hn : n ≤ N)
    (hscale : N ≤ 2 ^ k * (N - n)) :
    1 ≤ (2 : ℝ) ^ k * (1 - (n : ℝ) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale' : (N : ℝ) ≤ (2 : ℝ) ^ k * (N - n) := by
    exact_mod_cast (show N ≤ 2 ^ k * (N - n) from hscale)
  have hscaled := (div_le_div_iff_of_pos_right hN').mpr hscale'
  simpa only [div_self hN'.ne', mul_div_assoc, sub_div] using hscaled

private theorem rounded_chain_cost_aux {g : ℕ → ℝ} {N n k : ℕ} {C : ℝ}
    (hN : 0 < N) (hn : n < N) (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hscale : N ≤ 2 ^ k * (N - n)) {l : List ℝ}
    (hc : RealProfileChain ((n : ℝ) / N) l)
    (hend : realProfileChainEnd ((n : ℝ) / N) l = 0)
    (hcost : realProfileChainCost (normalizedProfileInterpolation g N) (n / N) l ≤ C + 1 / N) :
    ∃ l' : List ℕ, l'.length ≤ 2 * k ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l') ∧
      chainEnd n l' = 0 ∧ chainCost g n l' ≤ C * N + 4 * k + 1 := by
  obtain ⟨l', hc', he', hlen, hcost'⟩ := exists_short_integer_chain_of_real_profile hN hn.le
    hlip hc hend (normalized_gap_scale_aux hN hn.le hscale)
  refine ⟨l', hlen, hc', he', ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left hcost hN'.le
  have hcancel : (N : ℝ) * (1 / N) = 1 := mul_div_cancel₀ 1 hN'.ne'
  nlinarith [hmul, hcancel]

/-- The low-side finite-grid estimate, with no endpoint equality hypothesis. -/
theorem exists_finite_twoGap_chain {g : ℕ → ℝ} {N n k : ℕ} {a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : b * (4 + 2 * a) ≤ 1 + 2 * a) (hguard : twoGapGuard a b ≤ 0)
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    (hn : n < N) (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, l.length ≤ 2 * k ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧ chainCost g n l ≤ twoGapCost a b * N + 4 * k + 1 := by
  let c : ℝ := (1 + a) * N
  let f (j : ℕ) : ℝ := min (g j) (c - j)
  have hflip := fun j hj ↦ clip_lipschitz_of_finite hlip c (j := j) hj
  have hflow : ∀ j, j ≤ N → a * j ≤ f j :=
    fun j hj ↦ lower_barrier_le_clip (by linarith) hj (hlower j hj)
  have hfup : ∀ j, j ≤ N → f j ≤ b * j :=
    fun j hj ↦ (min_le_left _ _).trans (hupper j hj)
  have hfend : f N = a * N := clip_endpoint (hlower N le_rfl)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨r, hr, he, hcost⟩ := exists_normalizedProfileChain_twoGapCost hN ha hab hb
    htransition hguard hflip hflow hfup hfend
    (div_nonneg (Nat.cast_nonneg n) hN'.le)
    ((div_lt_one hN').mpr (by exact_mod_cast hn)) (by positivity : 0 < (1 : ℝ) / N)
  obtain ⟨l, hlen, hl, hend, hbound⟩ := rounded_chain_cost_aux hN hn hflip hscale hr he hcost
  exact ⟨l, hlen, hl, hend,
    (chainCost_le_clip_of_finite hlip c n l hn.le (hl.imp fun _ _ h ↦ h.1)).trans hbound⟩

/-- The high-side finite-grid estimate combines the low-slope and high-slope proofs. -/
theorem exists_finite_singleGap_chain {g : ℕ → ℝ} {N n k : ℕ} {a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hab : a < b)
    (htransition : 1 + 2 * a ≤ b * (4 + 2 * a))
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    (hn : n < N) (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, l.length ≤ 2 * k ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧ chainCost g n l ≤ singleGapCost a b * N + 4 * k + 1 := by
  rcases le_total b (1 / 2) with hb | hb
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    obtain ⟨r, hr, he, hcost⟩ := exists_normalizedProfileChain_singleGapCost hN ha hab hb
      htransition hlip hlower hupper (div_nonneg (Nat.cast_nonneg n) hN'.le)
      ((div_lt_one hN').mpr (by exact_mod_cast hn)) (by positivity : 0 < (1 : ℝ) / N)
    exact rounded_chain_cost_aux hN hn hlip hscale hr he hcost
  · obtain ⟨l, hlen, hl, he, hc⟩ :=
      exists_high_slope_chain ha.le hb hlip hlower hupper hn hscale
    refine ⟨l, hlen, hl, he, ?_⟩
    dsimp [singleGapCost]
    linarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

/-- Either valid algebraic branch gives an actual finite-grid chain with controlled length. -/
theorem exists_finite_hardGap_chain {g : ℕ → ℝ} {N n k : ℕ} {a b C : ℝ}
    (hN : 0 < N) (ha : 0 < a) (ha' : a ≤ 1 / 4) (hab : a < b)
    (hcase : (b * (4 + 2 * a) ≤ 1 + 2 * a ∧ twoGapGuard a b ≤ 0 ∧ C = twoGapCost a b) ∨
      (1 + 2 * a ≤ b * (4 + 2 * a) ∧ C = singleGapCost a b))
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    (hn : n < N) (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, l.length ≤ 2 * k ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧ chainCost g n l ≤ C * N + 4 * k + 1 := by
  rcases hcase with ⟨htransition, hguard, rfl⟩ | ⟨htransition, rfl⟩
  · have hb : b ≤ 1 / 2 := by nlinarith
    exact exists_finite_twoGap_chain hN ha hab hb htransition hguard hlip hlower hupper hn hscale
  · exact exists_finite_singleGap_chain hN ha hab htransition hlip hlower hupper hn hscale

private theorem finite_scale_of_gap_ratio_aux {ζ : ℝ} {N n k : ℕ}
    (hζ : 0 < ζ) (hN : 0 < N) (hstart : (n : ℝ) ≤ (1 - ζ) * N)
    (hk : 1 ≤ (2 : ℝ) ^ k * ζ) : n < N ∧ N ≤ 2 ^ k * (N - n) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn' : (n : ℝ) < N := by nlinarith [mul_pos hζ hN']
  have hn : n < N := by exact_mod_cast hn'
  refine ⟨hn, ?_⟩
  have hgap : ζ * N ≤ ((N - n : ℕ) : ℝ) := by rw [Nat.cast_sub hn.le]; linarith
  have hscale : (N : ℝ) ≤ (2 : ℝ) ^ k * ((N - n : ℕ) : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hk hN'.le,
      mul_le_mul_of_nonneg_left hgap (show 0 ≤ (2 : ℝ) ^ k by positivity)]
  exact_mod_cast hscale

/-- The full finite-grid hard-gap estimate has a length bound depending only on the initial
relative gap. The additive cost is at most twice that uniform bound. -/
theorem exists_uniform_finite_hardGap_chain {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N n : ℕ) (a b C : ℝ) (g : ℕ → ℝ),
      0 < N → 0 < a → a ≤ 1 / 4 → a < b →
      ((b * (4 + 2 * a) ≤ 1 + 2 * a ∧ twoGapGuard a b ≤ 0 ∧ C = twoGapCost a b) ∨
        (1 + 2 * a ≤ b * (4 + 2 * a) ∧ C = singleGapCost a b)) →
      (∀ j, j < N → |g (j + 1) - g j| ≤ 1) →
      (∀ j, j ≤ N → a * j ≤ g j) → (∀ j, j ≤ N → g j ≤ b * j) →
      (n : ℝ) ≤ (1 - ζ) * N →
      ∃ l : List ℕ, l.length ≤ K ∧
        List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
        chainEnd n l = 0 ∧ chainCost g n l ≤ C * N + 2 * K := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ζ) (by norm_num : (1 : ℝ) < 2)
  have hk' : 1 ≤ (2 : ℝ) ^ k * ζ := ((div_lt_iff₀ hζ).mp hk).le
  refine ⟨2 * k + 1, by omega, fun N n a b C g hN ha ha' hab hcase hlip hlo hup hstart ↦ ?_⟩
  obtain ⟨hn, hscale⟩ := finite_scale_of_gap_ratio_aux hζ hN hstart hk'
  obtain ⟨l, hlen, hl, he, hc⟩ := exists_finite_hardGap_chain hN ha ha' hab hcase
    hlip hlo hup hn hscale
  refine ⟨l, by omega, hl, he, ?_⟩
  push_cast
  linarith

private theorem affine_grid_lipschitz_aux {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (j : ℕ) :
    |s * (j + 1 : ℕ) - s * j| ≤ 1 := by
  have heq : s * (j + 1 : ℕ) - s * j = s := by push_cast; ring
  rw [heq, abs_of_nonneg hs]
  exact hs'

private theorem clamp_profile_dist_aux {u v z δ : ℝ} (hδ : 0 ≤ δ)
    (hlo : u - δ ≤ z) (hup : z ≤ v + δ) : |z - min (max z u) v| ≤ δ := by
  have htop : min (max z u) v ≤ z + δ :=
    (min_le_left _ _).trans (max_le (by linarith) (by linarith))
  have hbot : z - δ ≤ min (max z u) v :=
    le_min ((by linarith : z - δ ≤ z).trans (le_max_left _ _)) (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Additive barrier errors can be removed while retaining the finite Lipschitz bound and
changing every grid value by at most the original error. -/
theorem exists_profile_with_exact_barriers {g : ℕ → ℝ} {N : ℕ} {a b δ : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hδ : 0 ≤ δ)
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j - δ ≤ g j)
    (hupper : ∀ j, j ≤ N → g j ≤ b * j + δ) :
    ∃ f : ℕ → ℝ, (∀ j, j < N → |f (j + 1) - f j| ≤ 1) ∧
      (∀ j, j ≤ N → a * j ≤ f j) ∧ (∀ j, j ≤ N → f j ≤ b * j) ∧
      ∀ j, j ≤ N → |g j - f j| ≤ δ := by
  let f (j : ℕ) := min (max (g j) (a * j)) (b * j)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro j hj
    apply (abs_min_sub_min_le_max _ _ _ _).trans
    apply max_le
    · exact (abs_max_sub_max_le_max _ _ _ _).trans
        (max_le (hlip j hj) (affine_grid_lipschitz_aux ha (hab.trans hb) j))
    · exact affine_grid_lipschitz_aux (ha.trans hab) hb j
  · intro j _
    exact le_min (le_max_right _ _) (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg j))
  · intro j _
    exact min_le_right _ _
  · intro j hj
    exact clamp_profile_dist_aux hδ (hlower j hj) (hupper j hj)

/-- Uniform perturbation costs at most twice the error per edge using only finite-grid data. -/
theorem chainCost_perturb_of_finite {g h : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (hδ : ∀ j, j ≤ N → |g j - h j| ≤ δ) (n : ℕ) (l : List ℕ) (hn : n ≤ N)
    (hc : List.IsChain (fun n m ↦ m < n) (n :: l)) :
    |chainCost g n l - chainCost h n l| ≤ 2 * δ * l.length := by
  rw [chainCost_eq_of_eq_le (g := g) (h := fun j ↦ g (min j N))
    (fun j hj ↦ by rw [min_eq_left hj]) n l hn hc]
  rw [chainCost_eq_of_eq_le (g := h) (h := fun j ↦ h (min j N))
    (fun j hj ↦ by rw [min_eq_left hj]) n l hn hc]
  exact chainCost_perturb (fun j ↦ hδ (min j N) (min_le_right _ _)) n l hc

/-- The uniform finite-grid estimate is stable under additive barrier error `ε * N`.
The resulting cost error is at most `2 * ε * N * K`, with the same profile-independent length. -/
theorem exists_uniform_finite_hardGap_chain_with_error {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : ℕ, 0 < K ∧ ∀ (N n : ℕ) (a b C ε : ℝ) (g : ℕ → ℝ),
      0 < N → 0 < a → a ≤ 1 / 4 → a < b → b ≤ 1 → 0 ≤ ε →
      ((b * (4 + 2 * a) ≤ 1 + 2 * a ∧ twoGapGuard a b ≤ 0 ∧ C = twoGapCost a b) ∨
        (1 + 2 * a ≤ b * (4 + 2 * a) ∧ C = singleGapCost a b)) →
      (∀ j, j < N → |g (j + 1) - g j| ≤ 1) →
      (∀ j, j ≤ N → a * j - ε * N ≤ g j) →
      (∀ j, j ≤ N → g j ≤ b * j + ε * N) →
      (n : ℝ) ≤ (1 - ζ) * N →
      ∃ l : List ℕ, l.length ≤ K ∧
        List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
        chainEnd n l = 0 ∧ chainCost g n l ≤ C * N + 2 * K + 2 * ε * N * K := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_finite_hardGap_chain hζ
  refine ⟨K, hK, fun N n a b C ε g hN ha ha' hab hb hε hcase hlip hlo hup hstart ↦ ?_⟩
  have hδ : 0 ≤ ε * (N : ℝ) := mul_nonneg hε (Nat.cast_nonneg N)
  obtain ⟨f, hflip, hflow, hfup, hdist⟩ := exists_profile_with_exact_barriers ha.le hab.le hb
    hδ hlip hlo hup
  obtain ⟨l, hlen, hl, he, hc⟩ := hbound N n a b C f hN ha ha' hab hcase
    hflip hflow hfup hstart
  refine ⟨l, hlen, hl, he, ?_⟩
  have hn : n ≤ N := by exact_mod_cast (show (n : ℝ) ≤ N by
    nlinarith [mul_nonneg hζ.le (Nat.cast_nonneg (α := ℝ) N)])
  have hperturb := (abs_le.mp (chainCost_perturb_of_finite hdist n l hn
    (hl.imp fun _ _ h ↦ h.1))).2
  have hlen' : (l.length : ℝ) ≤ K := by exact_mod_cast hlen
  have herr := mul_le_mul_of_nonneg_left hlen' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)
  nlinarith [herr]

end FalconerPacking
