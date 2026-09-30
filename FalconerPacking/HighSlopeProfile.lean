/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.ChainCompression

/-!
# The high-slope profile bound

For an upper barrier of slope at least one half, the monotone potential gives a chain to zero
with cost at most `(b - a) * N / (1 + 2 * b) + 1`. The additive one is the cost of crossing
the last unit interval at which the potential changes sign. Compression makes the number of
edges independent of the grid resolution when the initial relative gap is fixed.
-/

noncomputable section

namespace FalconerPacking

private theorem chainEnd_descentChain_ge_aux (N q : ℕ) :
    ∀ (k n : ℕ), q + 1 ≤ n → q + 1 ≤ chainEnd n (descentChain N q k n)
  | 0, _, h => h
  | k + 1, n, h => by
      rw [descentChain]
      split
      · exact chainEnd_descentChain_ge_aux N q k _ (le_max_left _ _)
      · exact h

private theorem exists_potential_crossing_aux {f : ℕ → ℝ} {n : ℕ}
    (hzero : f 0 ≤ 0) (hpos : 0 < f n) :
    ∃ q : ℕ, q + 1 ≤ n ∧ f q ≤ 0 ∧ 0 < f (q + 1) := by
  classical
  have hex : ∃ j, 0 < f j := ⟨n, hpos⟩
  have hfirst := Nat.find_spec hex
  have hle := Nat.find_min' hex hpos
  have hne : Nat.find hex ≠ 0 := by intro h; rw [h] at hfirst; linarith
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨q, by omega, ?_, by simpa [hq] using hfirst⟩
  exact le_of_not_gt (Nat.find_min hex (by omega))

private theorem exists_chain_at_crossing_aux {N n q k : ℕ} {b : ℝ} {g : ℕ → ℝ}
    (hb : 1 / 2 ≤ b) (hlip : ∀ j : ℕ, |g (j + 1) - g j| ≤ 1)
    (hzero : g 0 = 0) (hpos : ∀ j, j ≤ N → 0 ≤ g j)
    (hupper : ∀ j, j ≤ N → g j ≤ b * j) (hn : n < N) (hqn : q + 1 ≤ n)
    (hq : potential b N g q ≤ 0) (hq' : 0 ≤ potential b N g (q + 1))
    (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧ chainCost g n l ≤ potential b N g n / (1 + 2 * b) + 1 := by
  have hden : 0 < 1 + 2 * b := by linarith
  let l₁ := descentChain N q k n
  have hchain₁ := descentChain_chain N q k n hn
  have hend₁ := chainEnd_descentChain_le N q (by omega) k n hn.le
    ((Nat.sub_le N (q + 1)).trans hscale)
  have hcost₁ := chainCost_le_potential (N := N) hb hlip n l₁
    (descentChain_decreasing N q k n hn)
  have hend : chainEnd n l₁ = q + 1 :=
    le_antisymm hend₁ (chainEnd_descentChain_ge_aux N q k n hqn)
  have hmono := potential_mono (N := N) hb hlip
  obtain ⟨l₂, _, hchain₂, hend₂, hcost₂⟩ := exists_free_chain hzero hpos hupper
    (fun j hj ↦ (hmono hj).trans hq) (by omega : q < N)
    (hscale.trans (Nat.mul_le_mul_left _ (by omega : N - n ≤ N - q)))
  refine ⟨l₁ ++ q :: l₂, ?_, ?_, ?_⟩
  · apply chain_append n l₁ (q :: l₂) hchain₁
    rw [hend]
    exact List.isChain_cons_cons.mpr ⟨⟨by omega, by unfold Admissible; omega⟩, hchain₂⟩
  · rw [chainEnd_append, hend]
    exact hend₂
  · rw [chainCost_append]
    change chainCost g n l₁ + (edgeCost g q (chainEnd n l₁) + chainCost g q l₂) ≤ _
    rw [hend, hcost₂, add_zero]
    have hunit := edgeCost_succ_le_one hlip (k := q)
    have hpaid : chainCost g n l₁ ≤ potential b N g n / (1 + 2 * b) := by
      rw [hend] at hcost₁
      exact hcost₁.trans ((div_le_div_iff_of_pos_right hden).mpr (by linarith))
    linarith

private theorem exists_chain_cost_potential_aux {N n k : ℕ} {b : ℝ} {g : ℕ → ℝ}
    (hb : 1 / 2 ≤ b) (hlip : ∀ j : ℕ, |g (j + 1) - g j| ≤ 1)
    (hzero : g 0 = 0) (hpos : ∀ j, j ≤ N → 0 ≤ g j)
    (hupper : ∀ j, j ≤ N → g j ≤ b * j) (hn : n < N)
    (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧
      chainCost g n l ≤ max (potential b N g n) 0 / (1 + 2 * b) + 1 := by
  have hmono := potential_mono (N := N) hb hlip
  by_cases hnonpos : potential b N g n ≤ 0
  · obtain ⟨l, _, hchain, hend, hcost⟩ := exists_free_chain hzero hpos hupper
      (fun j hj ↦ (hmono hj).trans hnonpos) hn hscale
    refine ⟨l, hchain, hend, ?_⟩
    rw [hcost, max_eq_right hnonpos, zero_div, zero_add]
    exact zero_le_one
  · have hstart := lt_of_not_ge hnonpos
    have hLzero : potential b N g 0 ≤ 0 := by
      simp only [potential, Nat.cast_zero, mul_zero, zero_sub, hzero, sub_zero]
      exact neg_nonpos.mpr (mul_nonneg (by linarith) (Nat.cast_nonneg N))
    obtain ⟨q, hqn, hq, hq'⟩ := exists_potential_crossing_aux hLzero hstart
    obtain ⟨l, hchain, hend, hcost⟩ :=
      exists_chain_at_crossing_aux hb hlip hzero hpos hupper hn hqn hq hq'.le hscale
    exact ⟨l, hchain, hend, by simpa [max_eq_left hstart.le] using hcost⟩

/-- The high-slope profile estimate for a sequence that is Lipschitz on the whole grid. -/
theorem exists_high_slope_chain_of_global_lipschitz {N n k : ℕ} {a b : ℝ} {g : ℕ → ℝ}
    (ha : 0 ≤ a) (hb : 1 / 2 ≤ b) (hlip : ∀ j : ℕ, |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    (hn : n < N) (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, l.length ≤ 2 * k ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧ chainCost g n l ≤ (b - a) / (1 + 2 * b) * N + 1 := by
  have hzero : g 0 = 0 := by
    apply le_antisymm
    · simpa using hupper 0 (Nat.zero_le N)
    · simpa using hlower 0 (Nat.zero_le N)
  have hpos : ∀ j, j ≤ N → 0 ≤ g j :=
    fun j hj ↦ (mul_nonneg ha (Nat.cast_nonneg j)).trans (hlower j hj)
  obtain ⟨l, hchain, hend, hcost⟩ :=
    exists_chain_cost_potential_aux hb hlip hzero hpos hupper hn hscale
  have hden : 0 < 1 + 2 * b := by linarith
  have hmax : max (potential b N g n) 0 ≤ (b - a) * N := by
    have hmono := potential_mono (N := N) hb hlip hn.le
    have hlow := hlower N le_rfl
    have hup := hupper N le_rfl
    unfold potential at hmono ⊢
    exact max_le (by nlinarith) (by nlinarith)
  have hbound : chainCost g n l ≤ (b - a) / (1 + 2 * b) * N + 1 :=
    hcost.trans (by
      have hdiv := (div_le_div_iff_of_pos_right hden).mpr hmax
      calc
        max (potential b N g n) 0 / (1 + 2 * b) + 1 ≤
            (b - a) * N / (1 + 2 * b) + 1 := add_le_add hdiv le_rfl
        _ = (b - a) / (1 + 2 * b) * N + 1 := by ring)
  obtain ⟨l', _, hchain', hend', hcost', _, hlength⟩ :=
    exists_compressed_chain g hn.le hscale hchain
  exact ⟨l', hlength, hchain', hend'.trans hend, hcost'.trans hbound⟩

private theorem edgeCost_eq_of_eq_le_aux {N m n : ℕ} {g h : ℕ → ℝ}
    (heq : ∀ j, j ≤ N → g j = h j) (hmn : m ≤ n) (hn : n ≤ N) :
    edgeCost g m n = edgeCost h m n := by
  have hmin : gMin g m n = gMin h m n := by
    apply le_antisymm
    · refine le_gMin hmn fun j hmj hjn ↦ ?_
      rw [← heq j (hjn.trans hn)]
      exact gMin_le hmj hjn
    · refine le_gMin hmn fun j hmj hjn ↦ ?_
      rw [heq j (hjn.trans hn)]
      exact gMin_le hmj hjn
  simp only [edgeCost, heq m (hmn.trans hn), hmin]

/-- A decreasing chain below `N` only depends on the profile values at indices at most `N`. -/
theorem chainCost_eq_of_eq_le {N : ℕ} {g h : ℕ → ℝ} (heq : ∀ j, j ≤ N → g j = h j) :
    ∀ (n : ℕ) (l : List ℕ), n ≤ N → List.IsChain (fun n m ↦ m < n) (n :: l) →
      chainCost g n l = chainCost h n l
  | _, [], _, _ => rfl
  | n, m :: rest, hn, hchain => by
      obtain ⟨hmn, htail⟩ := List.isChain_cons_cons.mp hchain
      simp only [chainCost]
      rw [edgeCost_eq_of_eq_le_aux heq hmn.le hn,
        chainCost_eq_of_eq_le heq m rest (hmn.le.trans hn) htail]

private theorem constant_extension_lipschitz_aux {N : ℕ} {g : ℕ → ℝ}
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1) :
    ∀ j : ℕ, |g (min (j + 1) N) - g (min j N)| ≤ 1 := by
  intro j
  by_cases hj : j < N
  · simpa only [min_eq_left (Nat.succ_le_of_lt hj), min_eq_left hj.le] using hlip j hj
  · have hNj := Nat.le_of_not_gt hj
    simp only [min_eq_right hNj, min_eq_right (hNj.trans (Nat.le_succ j)), sub_self,
      abs_zero, zero_le_one]

/-- The complete finite-grid high-slope estimate. No profile condition outside `[0,N]` is used.
The additive one is the single grid interval crossing the zero of the monotone potential. -/
theorem exists_high_slope_chain {N n k : ℕ} {a b : ℝ} {g : ℕ → ℝ}
    (ha : 0 ≤ a) (hb : 1 / 2 ≤ b) (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    (hn : n < N) (hscale : N ≤ 2 ^ k * (N - n)) :
    ∃ l : List ℕ, l.length ≤ 2 * k ∧
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
      chainEnd n l = 0 ∧ chainCost g n l ≤ (b - a) / (1 + 2 * b) * N + 1 := by
  obtain ⟨l, hlength, hchain, hend, hcost⟩ :=
    exists_high_slope_chain_of_global_lipschitz (g := fun j ↦ g (min j N)) ha hb
      (constant_extension_lipschitz_aux hlip)
      (fun j hj ↦ by simpa only [min_eq_left hj] using hlower j hj)
      (fun j hj ↦ by simpa only [min_eq_left hj] using hupper j hj) hn hscale
  refine ⟨l, hlength, hchain, hend, ?_⟩
  have heq : chainCost g n l = chainCost (fun j ↦ g (min j N)) n l :=
    chainCost_eq_of_eq_le (fun j hj ↦ by rw [min_eq_left hj]) n l hn.le
      (hchain.imp (fun _ _ h ↦ h.1))
  rwa [heq]

/-- The high-slope cost bound has a uniform chain length whenever the starting scale stays a
fixed positive proportion below `N`. -/
theorem exists_uniform_high_slope_chain {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : ℕ, ∀ (N n : ℕ) (a b : ℝ) (g : ℕ → ℝ),
      0 < N → 0 ≤ a → 1 / 2 ≤ b →
      (∀ j, j < N → |g (j + 1) - g j| ≤ 1) →
      (∀ j, j ≤ N → a * j ≤ g j) → (∀ j, j ≤ N → g j ≤ b * j) →
      (n : ℝ) ≤ (1 - ζ) * N →
      ∃ l : List ℕ, l.length ≤ K ∧
        List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n :: l) ∧
        chainEnd n l = 0 ∧ chainCost g n l ≤ (b - a) / (1 + 2 * b) * N + 1 := by
  obtain ⟨K, hK⟩ := exists_uniform_compression_length hζ
  refine ⟨K, fun N n a b g hN ha hb hlip hlower hupper hstart ↦ ?_⟩
  have hnreal : (n : ℝ) < N := by
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    nlinarith [mul_pos hζ hNreal]
  have hn : n < N := by exact_mod_cast hnreal
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt N (by decide : (1 : ℕ) < 2)
  have hscale : N ≤ 2 ^ k * (N - n) :=
    hk.le.trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨l, _, hchain, hend, hcost⟩ :=
    exists_high_slope_chain ha hb hlip hlower hupper hn hscale
  refine ⟨compressChain N n l, hK N n l hstart hchain,
    isChain_compressChain N n l hchain, ?_, ?_⟩
  · exact (chainEnd_compressChain N n l).trans hend
  · exact (chainCost_compressChain_le g N n l (hchain.imp (fun _ _ h ↦ h.1))).trans hcost

end FalconerPacking
