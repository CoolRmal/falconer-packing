/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RealChainCompression
import FalconerPacking.ProfileInterpolation

/-!
# Rounding real chains to integer profile scales

Both endpoints of an edge are rounded downward. Admissibility is preserved exactly, and
the normalized edge cost changes by at most twice the grid spacing. Equal rounded scales
are then deleted without changing the cost or the final endpoint.
-/

noncomputable section

namespace FalconerPacking

/-- The integer grid index obtained by rounding a normalized real scale downward. -/
def roundProfileScale (N : ℕ) (x : ℝ) : ℕ := ⌊(N : ℝ) * x⌋₊

theorem roundProfileScale_mono (N : ℕ) : Monotone (roundProfileScale N) := by
  intro x y hxy
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg N))

@[simp]
theorem roundProfileScale_zero (N : ℕ) : roundProfileScale N 0 = 0 := by
  simp [roundProfileScale]

theorem roundProfileScale_nat_div {N n : ℕ} (hN : 0 < N) :
    roundProfileScale N (n / N) = n := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [roundProfileScale, mul_div_cancel₀ _ hN']

theorem roundProfileScale_le_scale {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 ≤ x) :
    (roundProfileScale N x : ℝ) / N ≤ x := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hN').mpr
  simpa only [roundProfileScale, mul_comm] using
    Nat.floor_le (mul_nonneg hN'.le hx)

theorem roundProfileScale_error {N : ℕ} (hN : 0 < N) {x : ℝ} :
    x - (roundProfileScale N x : ℝ) / N ≤ 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hf := Nat.lt_floor_add_one ((N : ℝ) * x)
  have hc := div_mul_cancel₀ (roundProfileScale N x : ℝ) hN'.ne'
  rw [le_div_iff₀ hN']
  change (N : ℝ) * x < (roundProfileScale N x : ℝ) + 1 at hf
  nlinarith

theorem roundProfileScale_le {N : ℕ} {x : ℝ} (hx : x ≤ 1) : roundProfileScale N x ≤ N := by
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hx

/-- Simultaneously rounding down both endpoints preserves the admissible inequality. -/
theorem roundProfileScale_admissible {N : ℕ} {m n : ℝ} (hn : 0 ≤ n)
    (hadm : 2 * n - m ≤ 1) : Admissible N (roundProfileScale N m) (roundProfileScale N n) := by
  have hnf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hn)
  have hmf := Nat.lt_floor_add_one ((N : ℝ) * m)
  have hmul := mul_le_mul_of_nonneg_left hadm (Nat.cast_nonneg N)
  change (roundProfileScale N n : ℝ) ≤ (N : ℝ) * n at hnf
  change (N : ℝ) * m < (roundProfileScale N m : ℝ) + 1 at hmf
  have h : (2 * roundProfileScale N n : ℕ) < N + roundProfileScale N m + 1 := by
    exact_mod_cast (show (2 : ℝ) * roundProfileScale N n < N + roundProfileScale N m + 1 by
      nlinarith)
  unfold Admissible
  omega

/-- Moving both endpoints left by at most `δ` changes the minimum by at most `δ`. -/
theorem realProfileMin_perturb_left {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {m n m' n' δ : ℝ} (hmn : m ≤ n) (hmn' : m' ≤ n') (hδ : 0 ≤ δ)
    (hm : m' ≤ m) (hn : n' ≤ n) (hmδ : m - m' ≤ δ) (hnδ : n - n' ≤ δ) :
    |realProfileMin g m' n' - realProfileMin g m n| ≤ δ := by
  have hlow : realProfileMin g m n - δ ≤ realProfileMin g m' n' := by
    apply le_realProfileMin hmn'
    intro x hx
    by_cases hmx : m ≤ x
    · have h := realProfileMin_le hg.continuous (show x ∈ Set.Icc m n from
        ⟨hmx, hx.2.trans hn⟩)
      linarith
    · have h := realProfileMin_le hg.continuous (show m ∈ Set.Icc m n from ⟨le_rfl, hmn⟩)
      have h' := (abs_le.mp (profile_increment_abs_le hg (le_of_not_ge hmx))).2
      linarith [hx.1]
  have hhigh : realProfileMin g m' n' - δ ≤ realProfileMin g m n := by
    apply le_realProfileMin hmn
    intro x hx
    by_cases hxn : x ≤ n'
    · have h := realProfileMin_le hg.continuous (show x ∈ Set.Icc m' n' from
        ⟨hm.trans hx.1, hxn⟩)
      linarith
    · have h := realProfileMin_le hg.continuous (show n' ∈ Set.Icc m' n' from ⟨hmn', le_rfl⟩)
      have h' := (abs_le.mp (profile_increment_abs_le hg (le_of_not_ge hxn))).1
      linarith [hx.2]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The value at the lower endpoint contributes one further grid-spacing error. -/
theorem realProfileEdgeCost_perturb_left {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {m n m' n' δ : ℝ} (hmn : m ≤ n) (hmn' : m' ≤ n') (hδ : 0 ≤ δ)
    (hm : m' ≤ m) (hn : n' ≤ n) (hmδ : m - m' ≤ δ) (hnδ : n - n' ≤ δ) :
    |realProfileEdgeCost g m' n' - realProfileEdgeCost g m n| ≤ 2 * δ := by
  have hmin := realProfileMin_perturb_left hg hmn hmn' hδ hm hn hmδ hnδ
  have hval := (profile_increment_abs_le hg hm).trans hmδ
  rw [abs_le] at hmin hval ⊢
  unfold realProfileEdgeCost
  constructor <;> linarith [hmin.1, hmin.2, hval.1, hval.2]

/-- Rounding a normalized interpolated edge costs at most two in unnormalized grid units. -/
theorem edgeCost_roundProfileScale_le {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) {m n : ℝ}
    (hm : 0 ≤ m) (hmn : m ≤ n) (hn : n ≤ 1) :
    edgeCost g (roundProfileScale N m) (roundProfileScale N n) ≤
      N * realProfileEdgeCost (normalizedProfileInterpolation g N) m n + 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hround := roundProfileScale_mono N hmn
  have hround' : (roundProfileScale N m : ℝ) / N ≤ (roundProfileScale N n : ℝ) / N :=
    (div_le_div_iff_of_pos_right hN').mpr (by exact_mod_cast hround)
  have he := realProfileEdgeCost_perturb_left (lipschitzWith_normalizedProfileInterpolation hN hlip)
    hmn hround' (by positivity : 0 ≤ (1 : ℝ) / N)
    (roundProfileScale_le_scale hN hm) (roundProfileScale_le_scale hN (hm.trans hmn))
    (roundProfileScale_error hN) (roundProfileScale_error hN)
  have hid := normalizedProfileInterpolation_edgeCost (g := g) hN hround (roundProfileScale_le hn)
  change realProfileEdgeCost (normalizedProfileInterpolation g N)
    ((roundProfileScale N m : ℝ) / N) ((roundProfileScale N n : ℝ) / N) = _ at hid
  rw [hid] at he
  have he' := (abs_le.mp he).2
  have hc := div_mul_cancel₀ (edgeCost g (roundProfileScale N m) (roundProfileScale N n)) hN'.ne'
  have hc' := div_mul_cancel₀ (1 : ℝ) hN'.ne'
  nlinarith [mul_le_mul_of_nonneg_right he' hN'.le]

theorem chainEnd_roundProfileScale (N : ℕ) : ∀ (n : ℝ) (l : List ℝ),
    chainEnd (roundProfileScale N n) (l.map (roundProfileScale N)) =
      roundProfileScale N (realProfileChainEnd n l)
  | _, [] => rfl
  | _, m :: tail => chainEnd_roundProfileScale N m tail

/-- Rounded chains may have repeated scales, but every edge remains admissible. -/
theorem realProfileChain_round {N : ℕ} : ∀ (n : ℝ) (l : List ℝ),
    RealProfileChain n l → 0 ≤ realProfileChainEnd n l →
      List.IsChain (fun n m ↦ m ≤ n ∧ Admissible N m n)
        (roundProfileScale N n :: l.map (roundProfileScale N))
  | _, [], _, _ => List.isChain_singleton _
  | n, m :: tail, hchain, hend => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp hchain
    have hm := hend.trans (realProfileChainEnd_le m tail (htail.imp fun _ _ h ↦ h.1))
    exact List.isChain_cons_cons.mpr
      ⟨⟨roundProfileScale_mono N hnm.1.le,
        roundProfileScale_admissible (hm.trans hnm.1.le) hnm.2⟩,
        realProfileChain_round m tail htail hend⟩

/-- The total unnormalized rounding error is at most twice the number of edges. -/
theorem chainCost_roundProfileScale_le {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N)
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) : ∀ (n : ℝ) (l : List ℝ),
    RealProfileChain n l → n ≤ 1 → 0 ≤ realProfileChainEnd n l →
      chainCost g (roundProfileScale N n) (l.map (roundProfileScale N)) ≤
        N * realProfileChainCost (normalizedProfileInterpolation g N) n l + 2 * l.length
  | _, [], _, _, _ => by simp [chainCost, realProfileChainCost]
  | n, m :: tail, hchain, hn, hend => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp hchain
    have hm := hend.trans (realProfileChainEnd_le m tail (htail.imp fun _ _ h ↦ h.1))
    have hedge := edgeCost_roundProfileScale_le hN hlip hm hnm.1.le hn
    have hrec := chainCost_roundProfileScale_le hN hlip m tail htail (hnm.1.le.trans hn) hend
    simp only [List.map_cons, chainCost, realProfileChainCost, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    nlinarith

/-- Delete an edge whenever rounding has made its endpoints equal. -/
def strictifyProfileChain : ℕ → List ℕ → List ℕ
  | _, [] => []
  | n, m :: tail =>
      if m = n then strictifyProfileChain n tail else m :: strictifyProfileChain m tail

theorem strictifyProfileChain_sublist : ∀ (n : ℕ) (l : List ℕ),
    (strictifyProfileChain n l).Sublist l
  | _, [] => List.Sublist.refl _
  | n, m :: tail => by
    rw [strictifyProfileChain]
    split
    · exact (strictifyProfileChain_sublist n tail).cons m
    · exact (strictifyProfileChain_sublist m tail).cons_cons m

theorem chainEnd_strictify : ∀ (n : ℕ) (l : List ℕ),
    chainEnd n (strictifyProfileChain n l) = chainEnd n l
  | _, [] => rfl
  | n, m :: tail => by
    rw [strictifyProfileChain]
    split
    · next h => subst m; exact chainEnd_strictify n tail
    · exact chainEnd_strictify m tail

@[simp]
theorem edgeCost_self (g : ℕ → ℝ) (n : ℕ) : edgeCost g n n = 0 := by
  simp [edgeCost, gMin]

theorem chainCost_strictify (g : ℕ → ℝ) : ∀ (n : ℕ) (l : List ℕ),
    chainCost g n (strictifyProfileChain n l) = chainCost g n l
  | _, [] => rfl
  | n, m :: tail => by
    rw [strictifyProfileChain]
    split
    · next h => subst m; simpa [chainCost] using chainCost_strictify g n tail
    · simp only [chainCost, chainCost_strictify g m tail]

theorem isChain_strictify {N : ℕ} : ∀ (n : ℕ) (l : List ℕ),
    List.IsChain (fun n m ↦ m ≤ n ∧ Admissible N m n) (n :: l) →
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: strictifyProfileChain n l)
  | _, [], _ => List.isChain_singleton _
  | n, m :: tail, hchain => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp hchain
    rw [strictifyProfileChain]
    split
    · next h => subst m; exact isChain_strictify n tail htail
    · next h =>
        exact List.isChain_cons_cons.mpr
          ⟨⟨lt_of_le_of_ne hnm.1 h, hnm.2⟩, isChain_strictify m tail htail⟩

/-- A real chain with grid starting point yields an admissible integer chain with the same
endpoint, no more edges, and error at most two per original edge. -/
theorem exists_integer_chain_of_real_profile {g : ℕ → ℝ} {N n : ℕ}
    (hN : 0 < N) (hn : n ≤ N) (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    {l : List ℝ} (hc : RealProfileChain ((n : ℝ) / N) l)
    (hend : realProfileChainEnd ((n : ℝ) / N) l = 0) :
    ∃ l' : List ℕ,
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l') ∧
      chainEnd n l' = 0 ∧ l'.length ≤ l.length ∧
      chainCost g n l' ≤
        N * realProfileChainCost (normalizedProfileInterpolation g N) (n / N) l + 2 * l.length := by
  let rounded := l.map (roundProfileScale N)
  have hstart := roundProfileScale_nat_div (n := n) hN
  have hend' : 0 ≤ realProfileChainEnd ((n : ℝ) / N) l := by rw [hend]
  have hchain := realProfileChain_round (N := N) ((n : ℝ) / N) l hc hend'
  rw [hstart] at hchain
  refine ⟨strictifyProfileChain n rounded, isChain_strictify n rounded hchain, ?_, ?_, ?_⟩
  · rw [chainEnd_strictify, ← hstart, chainEnd_roundProfileScale, hend, roundProfileScale_zero]
  · exact (strictifyProfileChain_sublist n rounded).length_le.trans (by simp [rounded])
  · rw [chainCost_strictify]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hn' : (n : ℝ) / N ≤ 1 := (div_le_one hN').mpr (by exact_mod_cast hn)
    simpa only [hstart] using chainCost_roundProfileScale_le hN hlip (n / N) l hc hn' hend'

/-- Compress before rounding to obtain a profile-independent bound on both errors. -/
theorem exists_short_integer_chain_of_real_profile {g : ℕ → ℝ} {N n k : ℕ}
    (hN : 0 < N) (hn : n ≤ N) (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    {l : List ℝ} (hc : RealProfileChain ((n : ℝ) / N) l)
    (hend : realProfileChainEnd ((n : ℝ) / N) l = 0)
    (hscale : 1 ≤ (2 : ℝ) ^ k * (1 - (n : ℝ) / N)) :
    ∃ l' : List ℕ,
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l') ∧
      chainEnd n l' = 0 ∧ l'.length ≤ 2 * k ∧
      chainCost g n l' ≤
        N * realProfileChainCost (normalizedProfileInterpolation g N) (n / N) l + 4 * k := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hn' : (n : ℝ) / N ≤ 1 := (div_le_one hN').mpr (by exact_mod_cast hn)
  obtain ⟨r, _, hr, hrend, hcost, hlength⟩ := exists_compressed_realProfileChain
    (continuous_normalizedProfileInterpolation g N) hn' (by rw [hend]) hc hscale
  obtain ⟨l', hl', hend', hlen', hcost'⟩ :=
    exists_integer_chain_of_real_profile hN hn hlip hr (hrend.trans hend)
  refine ⟨l', hl', hend', hlen'.trans hlength, ?_⟩
  have hlen : (r.length : ℝ) ≤ 2 * k := by exact_mod_cast hlength
  have hcost'' := mul_le_mul_of_nonneg_left hcost hN'.le
  linarith

end FalconerPacking
