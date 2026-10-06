/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.HardPoints
public import FalconerPacking.HardGapAlgebra
public import Mathlib.Data.List.Pairwise

/-!
# Finite gap sums and their tail estimates

The endpoints in this file are explicit finite data. We do not assume that an arbitrary
hard-point set has already been decomposed into these data. A gap is represented by its
ordered endpoint pair, and the ordering hypothesis says that earlier gaps end before later
ones begin. The second tail estimate is proved directly from Lipschitz continuity, without
introducing a total-variation functional.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- The sum of profile drops across a finite list of endpoint pairs. -/
def profileGapDropSum (g : ℝ → ℝ) (gaps : List (ℝ × ℝ)) : ℝ :=
  (gaps.map (fun e ↦ g e.1 - g e.2)).sum

@[simp]
theorem profileGapDropSum_nil (g : ℝ → ℝ) : profileGapDropSum g [] = 0 := rfl

@[simp]
theorem profileGapDropSum_cons (g : ℝ → ℝ) (q p : ℝ) (gaps : List (ℝ × ℝ)) :
    profileGapDropSum g ((q, p) :: gaps) = g q - g p + profileGapDropSum g gaps := rfl

theorem profileGapDropSum_nonneg {g : ℝ → ℝ} {gaps : List (ℝ × ℝ)}
    (hdrop : ∀ e ∈ gaps, 0 ≤ g e.1 - g e.2) : 0 ≤ profileGapDropSum g gaps := by
  induction gaps with
  | nil => simp
  | cons e gaps ih =>
    exact add_nonneg (hdrop e List.mem_cons_self)
      (ih fun e he ↦ hdrop e (List.mem_cons_of_mem _ he))

/-- The forward-midpoint gap bound is at most half the length of the gap. -/
theorem gap_drop_le_half_length {δ q p : ℝ} (hp : p ≤ 1)
    (hgap : δ ≤ p - (1 + q) / 2) : δ ≤ (p - q) / 2 := by
  linarith

/-- Disjoint ordered gaps beyond `p` use at most half of the remaining interval length. -/
theorem profileGapDropSum_le_half {g : ℝ → ℝ} {gaps : List (ℝ × ℝ)} {p : ℝ}
    (hp : p ≤ 1) (horder : gaps.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hwithin : ∀ e ∈ gaps, p ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1)
    (hgap : ∀ e ∈ gaps, g e.1 - g e.2 ≤ e.2 - (1 + e.1) / 2) :
    profileGapDropSum g gaps ≤ (1 - p) / 2 := by
  induction gaps generalizing p with
  | nil => simp only [profileGapDropSum_nil]; linarith
  | cons e gaps ih =>
    obtain ⟨hq, hqp, hr⟩ := hwithin e List.mem_cons_self
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    have hbound := gap_drop_le_half_length hr (hgap e List.mem_cons_self)
    have ht := ih hr htail (fun f hf ↦
      ⟨hhead f hf, (hwithin f (List.mem_cons_of_mem _ hf)).2⟩)
      (fun f hf ↦ hgap f (List.mem_cons_of_mem _ hf))
    change g e.1 - g e.2 + profileGapDropSum g gaps ≤ (1 - p) / 2
    linarith

/-- Ordered real arguments turn the Lipschitz condition into a two-sided increment bound. -/
theorem profile_increment_abs_le {g : ℝ → ℝ} (hg : LipschitzWith 1 g) {x y : ℝ}
    (hxy : x ≤ y) : |g y - g x| ≤ y - x := by
  have h := hg.dist_le_mul y x
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_of_nonneg (sub_nonneg.mpr hxy)]
    using h

/-- Telescoping the Lipschitz increments gives the endpoint-sensitive tail estimate. -/
theorem profileGapDropSum_le_half_net {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {gaps : List (ℝ × ℝ)} {p : ℝ} (hp : p ≤ 1)
    (horder : gaps.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hwithin : ∀ e ∈ gaps, p ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1) :
    profileGapDropSum g gaps ≤ (1 - p + g p - g 1) / 2 := by
  induction gaps generalizing p with
  | nil =>
    simp only [profileGapDropSum_nil]
    have h := (abs_le.mp (profile_increment_abs_le hg hp)).2
    linarith
  | cons e gaps ih =>
    obtain ⟨hq, hqp, hr⟩ := hwithin e List.mem_cons_self
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    have ht := ih hr htail (fun f hf ↦
      ⟨hhead f hf, (hwithin f (List.mem_cons_of_mem _ hf)).2⟩)
    have hbefore := (abs_le.mp (profile_increment_abs_le hg hq)).2
    have hdrop := (abs_le.mp (profile_increment_abs_le hg hqp)).1
    change g e.1 - g e.2 + profileGapDropSum g gaps ≤ (1 - p + g p - g 1) / 2
    linarith

/-- The two tail estimates can be blended with any coefficient between zero and one half. -/
theorem gap_tail_blend {S p v a χ : ℝ} (h₀ : S ≤ (1 - p) / 2)
    (h₁ : S ≤ (1 - p + v - a) / 2) (hχ : 0 ≤ χ) (hχ' : χ ≤ 1 / 2) :
    S ≤ (1 - p) / 2 + χ * (v - a) := by
  have hleft := mul_le_mul_of_nonneg_left h₀ (show 0 ≤ 1 - 2 * χ by linarith)
  have hright := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * χ by positivity)
  nlinarith only [hleft, hright]

/-- The component increments minus the total endpoint increment equal the intervening gap drops. -/
theorem finite_gap_drop_telescope (left right : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, (right i - left (i + 1)) =
      (∑ i ∈ Finset.range (n + 1), (right i - left i)) - (right n - left 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The normalized profile version of the finite telescoping identity. -/
theorem profile_component_gap_telescope (g : ℝ → ℝ) (p q : ℕ → ℝ) (n : ℕ)
    (hp : p 0 = 0) (hq : q n = 1) (hg : g 0 = 0) :
    ∑ i ∈ Finset.range n, (g (q i) - g (p (i + 1))) =
      (∑ i ∈ Finset.range (n + 1), (g (q i) - g (p i))) - g 1 := by
  simpa only [Function.comp_apply, hp, hq, hg, sub_zero] using
    finite_gap_drop_telescope (g ∘ p) (g ∘ q) n

/-- A finite list of positive gaps starting at hard points satisfies both tail bounds. -/
theorem profileGapDropSum_tail_bounds {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {gaps : List (ℝ × ℝ)} {p : ℝ} (hp : p ≤ 1)
    (horder : gaps.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hwithin : ∀ e ∈ gaps, p ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1)
    (hhard : ∀ e ∈ gaps, e.1 ∈ hardProfilePoints g)
    (hdrop : ∀ e ∈ gaps, g e.2 < g e.1) :
    profileGapDropSum g gaps ≤ (1 - p) / 2 ∧
      profileGapDropSum g gaps ≤ (1 - p + g p - g 1) / 2 := by
  refine ⟨profileGapDropSum_le_half hp horder hwithin ?_,
    profileGapDropSum_le_half_net hg hp horder hwithin⟩
  intro e he
  exact profile_gap_drop_le hg (hhard e he) (hwithin e he).2.1 (hdrop e he)

/-- A single positive gap between the two affine barriers obeys the one-gap certificate. -/
theorem profile_single_gap_le_singleGapCost {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {a b q p : ℝ} (ha : 0 < a) (hab : a < b) (hq : q ∈ hardProfilePoints g)
    (hqp : q ≤ p) (hp : p ≤ 1) (hdrop : g p < g q)
    (hlower : a * p ≤ g p) (hupper : g q ≤ b * q) :
    g q - g p ≤ singleGapCost a b := by
  have hb : 0 < b := ha.trans hab
  have hgap := profile_gap_drop_le hg hq hqp hdrop
  have hweighted := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * b by positivity)
  have hend := mul_nonneg (show 0 ≤ 2 * b - a by linarith) (sub_nonneg.mpr hp)
  rw [singleGapCost, le_div_iff₀ (by positivity : 0 < 1 + 2 * b)]
  nlinarith only [hweighted, hlower, hupper, hend]

/-- In the low-barrier region the two-gap certificate includes the one-gap case. -/
theorem singleGapCost_le_twoGapCost {a b : ℝ} (ha : a < 1) (hab : a ≤ b) (hb : 0 ≤ b)
    (htransition : b * (4 + 2 * a) ≤ 1 + 2 * a) :
    singleGapCost a b ≤ twoGapCost a b := by
  have hid := twoGapCost_sub_singleGapCost ha hb
  have hnum : 0 ≤ (b - a) * (1 + 2 * a - 4 * b - 2 * a * b) :=
    mul_nonneg (sub_nonneg.mpr hab) (by nlinarith only [htransition])
  have hdiv : 0 ≤ (b - a) * (1 + 2 * a - 4 * b - 2 * a * b) /
      ((1 - a) * (1 + 2 * b) ^ 2) := by
    exact div_nonneg hnum (mul_nonneg (by linarith) (sq_nonneg _))
  linarith only [hid, hdiv]

/-- The first two positive gaps and their finite tail satisfy the low-side certificate. -/
theorem finite_gaps_le_twoGapCost {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {a b q₁ p₁ q₂ p₂ : ℝ} {tail : List (ℝ × ℝ)}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : b * (4 + 2 * a) ≤ 1 + 2 * a) (hguard : twoGapGuard a b ≤ 0)
    (hend : g 1 = a) (hlower : ∀ x ∈ Set.Icc (0 : ℝ) 1, a * x ≤ g x)
    (hupper : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ b * x)
    (hq₁ : q₁ ∈ hardProfilePoints g) (hq₂ : q₂ ∈ hardProfilePoints g)
    (hqp₁ : q₁ ≤ p₁) (hbetween : p₁ ≤ q₂) (hqp₂ : q₂ ≤ p₂) (hp₂ : p₂ ≤ 1)
    (hdrop₁ : g p₁ < g q₁) (hdrop₂ : g p₂ < g q₂)
    (horder : tail.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hwithin : ∀ e ∈ tail, p₂ ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1)
    (hhard : ∀ e ∈ tail, e.1 ∈ hardProfilePoints g)
    (hdrop : ∀ e ∈ tail, g e.2 < g e.1) :
    profileGapDropSum g ((q₁, p₁) :: (q₂, p₂) :: tail) ≤ twoGapCost a b := by
  have hd₁ := profile_gap_drop_le hg hq₁ hqp₁ hdrop₁
  have hd₂ := profile_gap_drop_le hg hq₂ hqp₂ hdrop₂
  have hlip := (abs_le.mp (profile_increment_abs_le hg hbetween)).2
  obtain ⟨ht₁, ht₂⟩ := profileGapDropSum_tail_bounds hg hp₂ horder hwithin hhard hdrop
  rw [hend] at ht₂
  have hlo₁ := hlower p₁ ⟨hq₁.1.1.trans hqp₁, hbetween.trans hq₂.1.2⟩
  have hhi₁ := hupper q₁ hq₁.1
  have hhi₂ := hupper q₂ hq₂.1
  have h := twoGapCost_bound ha hab hb htransition hguard
    (by linarith : g q₁ - b * q₁ ≤ 0) (by linarith : a * p₁ - g p₁ ≤ 0)
    (by linarith : q₁ - 2 * p₁ + 2 * (g q₁ - g p₁) ≤ -1)
    (by linarith : g q₂ - g p₁ - q₂ + p₁ ≤ 0)
    (by linarith : g q₂ - b * q₂ ≤ 0)
    (by linarith : q₂ - 2 * p₂ + 2 * (g q₂ - g p₂) ≤ -1) hp₂ ht₁ ht₂
  simpa only [profileGapDropSum_cons, add_assoc] using h

/-- The high-side certificate uses, in addition, the net increase between the two gaps. -/
theorem finite_gaps_le_singleGapCost {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {a b q₁ p₁ q₂ p₂ : ℝ} {tail : List (ℝ × ℝ)}
    (ha : 0 < a) (hab : a < b) (hb : b ≤ 1 / 2)
    (htransition : 1 + 2 * a ≤ b * (4 + 2 * a))
    (hlower : ∀ x ∈ Set.Icc (0 : ℝ) 1, a * x ≤ g x)
    (hupper : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≤ b * x)
    (hq₁ : q₁ ∈ hardProfilePoints g) (hq₂ : q₂ ∈ hardProfilePoints g)
    (hqp₁ : q₁ ≤ p₁) (hbetween : p₁ ≤ q₂) (hqp₂ : q₂ ≤ p₂) (hp₂ : p₂ ≤ 1)
    (hdrop₁ : g p₁ < g q₁) (hdrop₂ : g p₂ < g q₂) (hinc : g p₁ ≤ g q₂)
    (horder : tail.Pairwise (fun e f ↦ e.2 ≤ f.1))
    (hwithin : ∀ e ∈ tail, p₂ ≤ e.1 ∧ e.1 ≤ e.2 ∧ e.2 ≤ 1)
    (hhard : ∀ e ∈ tail, e.1 ∈ hardProfilePoints g)
    (hdrop : ∀ e ∈ tail, g e.2 < g e.1) :
    profileGapDropSum g ((q₁, p₁) :: (q₂, p₂) :: tail) ≤ singleGapCost a b := by
  have hd₁ := profile_gap_drop_le hg hq₁ hqp₁ hdrop₁
  have hd₂ := profile_gap_drop_le hg hq₂ hqp₂ hdrop₂
  have hlip := (abs_le.mp (profile_increment_abs_le hg hbetween)).2
  have ht := (profileGapDropSum_tail_bounds hg hp₂ horder hwithin hhard hdrop).1
  have hlo₁ := hlower p₁ ⟨hq₁.1.1.trans hqp₁, hbetween.trans hq₂.1.2⟩
  have hlo₂ := hlower p₂ ⟨hq₂.1.1.trans hqp₂, hp₂⟩
  have hhi₁ := hupper q₁ hq₁.1
  have h := singleGapCost_bound ha hab hb htransition
    (by linarith : g q₁ - b * q₁ ≤ 0)
    (by linarith : g q₁ - g p₁ - p₁ + q₁ / 2 ≤ -1 / 2)
    (by linarith : a * p₁ - g p₁ ≤ 0)
    (by linarith : g q₂ - g p₂ - p₂ + q₂ / 2 ≤ -1 / 2)
    (by linarith : a * p₂ - g p₂ ≤ 0)
    (by linarith : g q₂ - g p₁ - q₂ + p₁ ≤ 0) hp₂ (sub_nonpos.mpr hinc) ht
  simpa only [profileGapDropSum_cons, add_assoc] using h

end FalconerPacking
