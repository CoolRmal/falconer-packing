/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.HardPointPartition
public import FalconerPacking.HardPointChains
public import FalconerPacking.GapTails

/-!
# Actual profile bounds from the finite hard-point partition

Positive drops are extracted from the ordered partition. Skipped cells are nondecreasing, so
the net increase between consecutive positive gaps follows from the construction. The finite
gap certificates then bound the actual chain budget.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerPacking

/-- The positive-drop cells of a finite consecutive part of an ordered partition. -/
def positiveProfileGaps (g : ℝ → ℝ) (x : ℕ → ℝ) : ℕ → ℕ → List (ℝ × ℝ)
  | 0, _ => []
  | n + 1, start =>
      if g (x (start + 1)) < g (x start) then
        (x start, x (start + 1)) :: positiveProfileGaps g x n (start + 1)
      else positiveProfileGaps g x n (start + 1)

/-- Every retained gap is one original cell with strictly positive drop. -/
theorem mem_positiveProfileGaps {g : ℝ → ℝ} {x : ℕ → ℝ} {e : ℝ × ℝ} :
    ∀ n start, e ∈ positiveProfileGaps g x n start ↔
      ∃ i, start ≤ i ∧ i < start + n ∧ e = (x i, x (i + 1)) ∧
        g (x (i + 1)) < g (x i)
  | 0, start => by
      simp only [positiveProfileGaps, List.not_mem_nil, Nat.add_zero, false_iff, not_exists]
      rintro i ⟨hi, hi', _⟩
      omega
  | n + 1, start => by
      rw [positiveProfileGaps]
      split_ifs with hdrop
      · rw [List.mem_cons, mem_positiveProfileGaps n (start + 1)]
        constructor
        · rintro (rfl | ⟨i, hi, hi', rfl, hd⟩)
          · exact ⟨start, le_rfl, by omega, rfl, hdrop⟩
          · exact ⟨i, by omega, by omega, rfl, hd⟩
        · rintro ⟨i, hi, hi', rfl, hd⟩
          by_cases heq : i = start
          · subst i; exact Or.inl rfl
          · exact Or.inr ⟨i, by omega, by omega, rfl, hd⟩
      · rw [mem_positiveProfileGaps n (start + 1)]
        constructor
        · rintro ⟨i, hi, hi', rfl, hd⟩
          exact ⟨i, by omega, by omega, rfl, hd⟩
        · rintro ⟨i, hi, hi', rfl, hd⟩
          have hne : i ≠ start := by intro heq; subst i; exact hdrop hd
          exact ⟨i, by omega, by omega, rfl, hd⟩

/-- Extracting positive cells preserves the sum of all nonnegative downward increments. -/
theorem positiveProfileGaps_dropSum (g : ℝ → ℝ) (x : ℕ → ℝ) :
    ∀ n start, profileGapDropSum g (positiveProfileGaps g x n start) =
      ∑ i ∈ Finset.range n, max (g (x (start + i)) - g (x (start + i + 1))) 0
  | 0, _ => by simp [positiveProfileGaps]
  | n + 1, start => by
      rw [positiveProfileGaps, Finset.sum_range_succ']
      have hshift :
          (∑ i ∈ Finset.range n, max (g (x (start + 1 + i)) - g (x (start + 1 + i + 1))) 0) =
          ∑ i ∈ Finset.range n,
            max (g (x (start + (i + 1))) - g (x (start + (i + 1) + 1))) 0 := by
        apply Finset.sum_congr rfl
        intro i _
        congr 4 <;> omega
      split_ifs with hdrop
      · rw [profileGapDropSum_cons, positiveProfileGaps_dropSum g x n (start + 1), hshift]
        simp only [Nat.add_zero, max_eq_left (sub_nonneg.mpr hdrop.le)]
        exact add_comm _ _
      · rw [positiveProfileGaps_dropSum g x n (start + 1), hshift]
        simp only [max_eq_right (sub_nonpos.mpr (le_of_not_gt hdrop)), add_zero]

/-- The skipped prefix has nonnegative net increment. -/
theorem positiveProfileGaps_prefix_le (g : ℝ → ℝ) (x : ℕ → ℝ) :
    ∀ n start q p rest, positiveProfileGaps g x n start = (q, p) :: rest →
      g (x start) ≤ g q
  | 0, _, _, _, _, h => by simp [positiveProfileGaps] at h
  | n + 1, start, q, p, rest, h => by
      rw [positiveProfileGaps] at h
      split_ifs at h with hdrop
      · have hq := congrArg (fun l ↦ l.head?) h
        simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hq
        exact (congrArg g hq.1).le
      · exact (le_of_not_gt hdrop).trans
          (positiveProfileGaps_prefix_le g x n (start + 1) q p rest h)

/-- Original cell order is preserved by extraction. -/
theorem positiveProfileGaps_pairwise {g : ℝ → ℝ} {x : ℕ → ℝ} (hx : Monotone x) :
    ∀ n start, (positiveProfileGaps g x n start).Pairwise (fun e f ↦ e.2 ≤ f.1)
  | 0, _ => by simp [positiveProfileGaps]
  | n + 1, start => by
      rw [positiveProfileGaps]
      split_ifs
      · apply List.pairwise_cons.mpr
        refine ⟨?_, positiveProfileGaps_pairwise hx n (start + 1)⟩
        intro e he
        obtain ⟨i, hi, _, rfl, _⟩ := (mem_positiveProfileGaps n (start + 1)).mp he
        exact hx hi
      · exact positiveProfileGaps_pairwise hx n (start + 1)

/-- The profile cannot decrease between two consecutive retained gaps. -/
theorem positiveProfileGaps_isChain (g : ℝ → ℝ) (x : ℕ → ℝ) :
    ∀ n start, List.IsChain (fun e f ↦ g e.2 ≤ g f.1) (positiveProfileGaps g x n start)
  | 0, _ => by simp [positiveProfileGaps]
  | n + 1, start => by
      rw [positiveProfileGaps]
      split_ifs
      · have ht := positiveProfileGaps_isChain g x n (start + 1)
        cases htail : positiveProfileGaps g x n (start + 1) with
        | nil => exact List.IsChain.singleton _
        | cons e rest =>
            apply List.isChain_cons_cons.mpr
            exact ⟨positiveProfileGaps_prefix_le g x n (start + 1) e.1 e.2 rest htail,
              by simpa only [htail] using ht⟩
      · exact positiveProfileGaps_isChain g x n (start + 1)

/-- The prescribed cell budget is exactly the positive part of its downward increment. -/
theorem hardProfileSegment_budget_eq_max {g : ℝ → ℝ} (hg : Continuous g)
    {q p c : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p)
    (hseg : (Icc q p ⊆ hardProfilePoints g ∧ c = 0) ∨
      (p ∈ hardProfilePoints g ∧ (∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) ∧
        c = g q - g p)) : c = max (g q - g p) 0 := by
  rcases hseg with ⟨hhard, rfl⟩ | ⟨hp, hgap, rfl⟩
  · have hle := monotoneOn_of_subset_hardProfilePoints hg hhard
      ⟨le_rfl, hqp⟩ ⟨hqp, le_rfl⟩ hqp
    exact (max_eq_right (sub_nonpos.mpr hle)).symm
  · apply (max_eq_left _).symm
    rcases lt_or_eq_of_le hqp with hlt | rfl
    · exact profile_gap_drop_nonneg hg hq hlt hp hgap
    · simp

/-- Summing the actual cell budgets equals the extracted positive-gap drop sum. -/
theorem hardProfilePartition_budget_eq_dropSum {g : ℝ → ℝ} (hg : Continuous g)
    {x c : ℕ → ℝ} {M : ℕ} (hx : Monotone x)
    (hmem : ∀ i, x i ∈ hardProfilePoints g)
    (hseg : ∀ i < M, (Icc (x i) (x (i + 1)) ⊆ hardProfilePoints g ∧ c i = 0) ∨
      (x (i + 1) ∈ hardProfilePoints g ∧
        (∀ z ∈ Ioo (x i) (x (i + 1)), z ∉ hardProfilePoints g) ∧
        c i = g (x i) - g (x (i + 1)))) :
    (∑ i ∈ Finset.range M, c i) = profileGapDropSum g (positiveProfileGaps g x M 0) := by
  rw [positiveProfileGaps_dropSum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Nat.zero_add] using hardProfileSegment_budget_eq_max hg (hmem i).1.1
    (hx (Nat.le_succ i)) (hseg i (Finset.mem_range.mp hi))

/-- The extracted gaps have the locations, hard left endpoints, and strict drops required
by the finite gap certificates. -/
theorem positiveProfileGaps_geometry {g : ℝ → ℝ} {x : ℕ → ℝ} (hx : Monotone x)
    (hmem : ∀ i, x i ∈ hardProfilePoints g) (M : ℕ) :
    ∀ e ∈ positiveProfileGaps g x M 0,
      0 ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1 ∧
        e.1 ∈ hardProfilePoints g ∧ g e.2 < g e.1 := by
  intro e he
  obtain ⟨i, _, _, rfl, hdrop⟩ := (mem_positiveProfileGaps M 0).mp he
  exact ⟨(hmem i).1.1, hx (Nat.le_succ i), (hmem (i + 1)).1.2, hmem i, hdrop⟩

/-- The low-side algebraic certificate bounds every actual finite ordered positive-gap list. -/
theorem profileGapDropSum_le_twoGapCost {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {a b : ℝ} {gaps : List (ℝ × ℝ)} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : b * (4 + 2 * a) ≤ 1 + 2 * a) (hguard : twoGapGuard a b ≤ 0)
    (hend : g 1 = a) (hlower : ∀ x ∈ Icc (0 : ℝ) 1, a * x ≤ g x)
    (hupper : ∀ x ∈ Icc (0 : ℝ) 1, g x ≤ b * x)
    (horder : gaps.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hdata : ∀ e ∈ gaps, 0 ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1 ∧
      e.1 ∈ hardProfilePoints g ∧ g e.2 < g e.1) :
    profileGapDropSum g gaps ≤ twoGapCost a b := by
  have hb₀ : 0 ≤ b := (ha.trans hab).le
  have hsingle : 0 ≤ singleGapCost a b :=
    div_nonneg (sub_nonneg.mpr hab.le) (by positivity)
  have hcost := singleGapCost_le_twoGapCost (by linarith : a < 1) hab.le hb₀ htransition
  rcases gaps with _ | ⟨⟨q₁, p₁⟩, rest⟩
  · exact hsingle.trans hcost
  rcases rest with _ | ⟨⟨q₂, p₂⟩, tail⟩
  · obtain ⟨hq₀, hqp, hp, hhard, hdrop⟩ := hdata (q₁, p₁) List.mem_cons_self
    have h := profile_single_gap_le_singleGapCost hg ha hab hhard hqp hp hdrop
      (hlower p₁ ⟨hq₀.trans hqp, hp⟩) (hupper q₁ hhard.1)
    simpa only [profileGapDropSum_cons, profileGapDropSum_nil, add_zero] using h.trans hcost
  · obtain ⟨hfirst, horder'⟩ := List.pairwise_cons.mp horder
    obtain ⟨hsecond, htail⟩ := List.pairwise_cons.mp horder'
    have hd₁ := hdata (q₁, p₁) List.mem_cons_self
    have hd₂ := hdata (q₂, p₂) (List.mem_cons_of_mem _ List.mem_cons_self)
    exact finite_gaps_le_twoGapCost hg ha hab hb htransition hguard hend hlower hupper
      hd₁.2.2.2.1 hd₂.2.2.2.1 hd₁.2.1 (hfirst _ List.mem_cons_self)
      hd₂.2.1 hd₂.2.2.1 hd₁.2.2.2.2 hd₂.2.2.2.2 htail
      (fun e he ↦ ⟨hsecond e he,
        (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.1,
        (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.2.1⟩)
      (fun e he ↦ (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.2.2.1)
      (fun e he ↦ (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.2.2.2)

/-- The high-side certificate also uses the proved nonnegative increment between gaps. -/
theorem profileGapDropSum_le_singleGapCost {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {a b : ℝ} {gaps : List (ℝ × ℝ)} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : 1 + 2 * a ≤ b * (4 + 2 * a))
    (hlower : ∀ x ∈ Icc (0 : ℝ) 1, a * x ≤ g x)
    (hupper : ∀ x ∈ Icc (0 : ℝ) 1, g x ≤ b * x)
    (horder : gaps.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hchain : List.IsChain (fun e f ↦ g e.2 ≤ g f.1) gaps)
    (hdata : ∀ e ∈ gaps, 0 ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1 ∧
      e.1 ∈ hardProfilePoints g ∧ g e.2 < g e.1) :
    profileGapDropSum g gaps ≤ singleGapCost a b := by
  rcases gaps with _ | ⟨⟨q₁, p₁⟩, rest⟩
  · exact div_nonneg (sub_nonneg.mpr hab.le) (by have := ha.trans hab; positivity)
  rcases rest with _ | ⟨⟨q₂, p₂⟩, tail⟩
  · obtain ⟨hq₀, hqp, hp, hhard, hdrop⟩ := hdata (q₁, p₁) List.mem_cons_self
    have h := profile_single_gap_le_singleGapCost hg ha hab hhard hqp hp hdrop
      (hlower p₁ ⟨hq₀.trans hqp, hp⟩) (hupper q₁ hhard.1)
    simpa only [profileGapDropSum_cons, profileGapDropSum_nil, add_zero] using h
  · obtain ⟨hfirst, horder'⟩ := List.pairwise_cons.mp horder
    obtain ⟨hsecond, htail⟩ := List.pairwise_cons.mp horder'
    have hd₁ := hdata (q₁, p₁) List.mem_cons_self
    have hd₂ := hdata (q₂, p₂) (List.mem_cons_of_mem _ List.mem_cons_self)
    exact finite_gaps_le_singleGapCost hg ha hab hb htransition hlower hupper
      hd₁.2.2.2.1 hd₂.2.2.2.1 hd₁.2.1 (hfirst _ List.mem_cons_self)
      hd₂.2.1 hd₂.2.2.1 hd₁.2.2.2.2 hd₂.2.2.2.2
      (List.isChain_cons_cons.mp hchain).1 htail
      (fun e he ↦ ⟨hsecond e he,
        (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.1,
        (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.2.1⟩)
      (fun e he ↦ (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.2.2.1)
      (fun e he ↦ (hdata e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2.2.2.2)

private theorem normalizedProfile_initial_aux {g : ℕ → ℝ} {N : ℕ} {a b : ℝ}
    (ha : 0 ≤ a) (hlower : ∀ j, j ≤ N → a * j ≤ g j)
    (hupper : ∀ j, j ≤ N → g j ≤ b * j) :
    g 0 = 0 ∧ ∀ j, j ≤ N → 0 ≤ g j := by
  constructor
  · have hlo := hlower 0 (Nat.zero_le N)
    have hup := hupper 0 (Nat.zero_le N)
    simp only [Nat.cast_zero, mul_zero] at hlo hup
    exact le_antisymm hup hlo
  · intro j hj
    exact (mul_nonneg ha (Nat.cast_nonneg j)).trans (hlower j hj)

private theorem normalizedProfileChain_of_gapBound_aux {g : ℕ → ℝ} {N : ℕ} {C : ℝ}
    (hN : 0 < N) (hzero : g 0 = 0) (hnonneg : ∀ j, j ≤ N → 0 ≤ g j)
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hbound : ∀ gaps : List (ℝ × ℝ),
      gaps.Pairwise (fun e f ↦ e.2 ≤ f.1) →
      List.IsChain (fun e f ↦ normalizedProfileInterpolation g N e.2 ≤
        normalizedProfileInterpolation g N f.1) gaps →
      (∀ e ∈ gaps, 0 ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1 ∧
        e.1 ∈ hardProfilePoints (normalizedProfileInterpolation g N) ∧
        normalizedProfileInterpolation g N e.2 < normalizedProfileInterpolation g N e.1) →
      profileGapDropSum (normalizedProfileInterpolation g N) gaps ≤ C)
    {n ε : ℝ} (hn₀ : 0 ≤ n) (hn : n < 1) (hε : 0 < ε) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = 0 ∧
      realProfileChainCost (normalizedProfileInterpolation g N) n l ≤ C + ε := by
  obtain ⟨x, c, M, _, hx, hxzero, hxone, hmem, hseg⟩ :=
    exists_normalized_hardProfile_partition hN hzero hnonneg
  have hf := lipschitzWith_normalizedProfileInterpolation hN hlip
  have hbudget : (∑ i ∈ Finset.range M, c i) ≤ C := by
    rw [hardProfilePartition_budget_eq_dropSum hf.continuous hx hmem hseg]
    exact hbound _ (positiveProfileGaps_pairwise hx M 0)
      (positiveProfileGaps_isChain _ x M 0) (positiveProfileGaps_geometry hx hmem M)
  obtain ⟨l, hl, he, hc⟩ := exists_realProfileChain_of_finite_hard_partition hf x c M hx
    hxzero hxone hseg hn₀ hn hε
  exact ⟨l, hl, he, hc.trans (add_le_add hbudget le_rfl)⟩

/-- In the low-side region, every actual normalized grid profile has a chain with the
two-gap cost bound, with arbitrary positive accuracy. -/
theorem exists_normalizedProfileChain_twoGapCost {g : ℕ → ℝ} {N : ℕ} {a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : b * (4 + 2 * a) ≤ 1 + 2 * a) (hguard : twoGapGuard a b ≤ 0)
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    (hend : g N = a * N) {n ε : ℝ} (hn₀ : 0 ≤ n) (hn : n < 1) (hε : 0 < ε) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = 0 ∧
      realProfileChainCost (normalizedProfileInterpolation g N) n l ≤ twoGapCost a b + ε := by
  obtain ⟨hzero, hnonneg⟩ := normalizedProfile_initial_aux ha.le hlower hupper
  apply normalizedProfileChain_of_gapBound_aux hN hzero hnonneg hlip _ hn₀ hn hε
  intro gaps horder _ hdata
  have hfend : normalizedProfileInterpolation g N 1 = a := by
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simpa only [div_self hN', hend, mul_div_cancel_right₀ _ hN'] using
      normalizedProfileInterpolation_natCast g hN (le_refl N)
  exact profileGapDropSum_le_twoGapCost (lipschitzWith_normalizedProfileInterpolation hN hlip)
    ha hab hb htransition hguard hfend
    (fun x hx ↦ (normalizedProfileInterpolation_barriers hN hlower hupper hx).1)
    (fun x hx ↦ (normalizedProfileInterpolation_barriers hN hlower hupper hx).2) horder hdata

/-- In the high-side region below slope one half, actual normalized profiles obey the
single-gap chain bound; no endpoint normalization is needed for this branch. -/
theorem exists_normalizedProfileChain_singleGapCost {g : ℕ → ℝ} {N : ℕ} {a b : ℝ}
    (hN : 0 < N) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : 1 + 2 * a ≤ b * (4 + 2 * a))
    (hlip : ∀ j, j < N → |g (j + 1) - g j| ≤ 1)
    (hlower : ∀ j, j ≤ N → a * j ≤ g j) (hupper : ∀ j, j ≤ N → g j ≤ b * j)
    {n ε : ℝ} (hn₀ : 0 ≤ n) (hn : n < 1) (hε : 0 < ε) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = 0 ∧
      realProfileChainCost (normalizedProfileInterpolation g N) n l ≤ singleGapCost a b + ε := by
  obtain ⟨hzero, hnonneg⟩ := normalizedProfile_initial_aux ha.le hlower hupper
  apply normalizedProfileChain_of_gapBound_aux hN hzero hnonneg hlip _ hn₀ hn hε
  intro gaps horder hchain hdata
  exact profileGapDropSum_le_singleGapCost (lipschitzWith_normalizedProfileInterpolation hN hlip)
    ha hab hb htransition
    (fun x hx ↦ (normalizedProfileInterpolation_barriers hN hlower hupper hx).1)
    (fun x hx ↦ (normalizedProfileInterpolation_barriers hN hlower hupper hx).2)
    horder hchain hdata

end FalconerPacking
