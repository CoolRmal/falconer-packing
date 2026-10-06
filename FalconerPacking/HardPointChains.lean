/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.GapTails
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Real-endpoint chains across hard intervals and gaps

These are finite chain constructions, rather than an invocation of a total-drop identity.
All chains start below one, since a strictly descending admissible edge cannot start at one.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerPacking

/-- The minimum of a continuous profile on a real interval. -/
def realProfileMin (g : ℝ → ℝ) (m n : ℝ) : ℝ := sInf (g '' Icc m n)

/-- The downward edge cost, using the value at the lower endpoint. -/
def realProfileEdgeCost (g : ℝ → ℝ) (m n : ℝ) : ℝ := g m - realProfileMin g m n

/-- The sum of costs along a real-endpoint downward chain. -/
def realProfileChainCost (g : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | _, [] => 0
  | n, m :: tail => realProfileEdgeCost g m n + realProfileChainCost g m tail

/-- The final endpoint of a real-endpoint chain. -/
def realProfileChainEnd : ℝ → List ℝ → ℝ
  | n, [] => n
  | _, m :: tail => realProfileChainEnd m tail

/-- Every edge descends strictly and obeys the normalized admissibility inequality. -/
def RealProfileChain (n : ℝ) (tail : List ℝ) : Prop :=
  List.IsChain (fun x y ↦ y < x ∧ 2 * x - y ≤ 1) (n :: tail)

theorem realProfileMin_le {g : ℝ → ℝ} (hg : Continuous g) {m n x : ℝ}
    (hx : x ∈ Icc m n) : realProfileMin g m n ≤ g x :=
  csInf_le (isCompact_Icc.image hg).bddBelow ⟨x, hx, rfl⟩

theorem le_realProfileMin {g : ℝ → ℝ} {m n v : ℝ} (hmn : m ≤ n)
    (hv : ∀ x ∈ Icc m n, v ≤ g x) : v ≤ realProfileMin g m n := by
  apply le_csInf ((nonempty_Icc.mpr hmn).image g)
  rintro _ ⟨x, hx, rfl⟩
  exact hv x hx

theorem realProfileMin_eq {g : ℝ → ℝ} (hg : Continuous g) {m n x : ℝ}
    (hx : x ∈ Icc m n) (hmin : ∀ y ∈ Icc m n, g x ≤ g y) :
    realProfileMin g m n = g x :=
  le_antisymm (realProfileMin_le hg hx) (le_realProfileMin (hx.1.trans hx.2) hmin)

theorem realProfileEdgeCost_nonneg {g : ℝ → ℝ} (hg : Continuous g) {m n : ℝ}
    (hmn : m ≤ n) : 0 ≤ realProfileEdgeCost g m n :=
  sub_nonneg.mpr (realProfileMin_le hg ⟨le_rfl, hmn⟩)

theorem realProfileEdgeCost_le_length {g : ℝ → ℝ} (hg : LipschitzWith 1 g) {m n : ℝ}
    (hmn : m ≤ n) : realProfileEdgeCost g m n ≤ n - m := by
  have hmin : g m - (n - m) ≤ realProfileMin g m n := by
    apply le_realProfileMin hmn
    intro x hx
    have h := (abs_le.mp (profile_increment_abs_le hg hx.1)).1
    linarith [hx.2]
  unfold realProfileEdgeCost
  linarith

theorem realProfileChainEnd_append : ∀ (n : ℝ) (l₁ l₂ : List ℝ),
    realProfileChainEnd n (l₁ ++ l₂) =
      realProfileChainEnd (realProfileChainEnd n l₁) l₂
  | _, [], _ => rfl
  | _, m :: tail, l₂ => by
    simpa only [List.cons_append, realProfileChainEnd] using
      realProfileChainEnd_append m tail l₂

theorem realProfileChainCost_append (g : ℝ → ℝ) : ∀ (n : ℝ) (l₁ l₂ : List ℝ),
    realProfileChainCost g n (l₁ ++ l₂) = realProfileChainCost g n l₁ +
      realProfileChainCost g (realProfileChainEnd n l₁) l₂
  | _, [], _ => by simp [realProfileChainCost, realProfileChainEnd]
  | n, m :: tail, l₂ => by
    simp only [List.cons_append, realProfileChainCost, realProfileChainEnd]
    rw [realProfileChainCost_append g m tail l₂]
    ring

theorem realProfileChain_append : ∀ (n : ℝ) (l₁ l₂ : List ℝ),
    RealProfileChain n l₁ → RealProfileChain (realProfileChainEnd n l₁) l₂ →
      RealProfileChain n (l₁ ++ l₂)
  | _, [], _, _, h₂ => h₂
  | n, m :: tail, l₂, h₁, h₂ => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h₁
    exact List.isChain_cons_cons.mpr
      ⟨hnm, realProfileChain_append m tail l₂ htail h₂⟩

/-- Appending a chain preserves the sum of its two certified cost bounds. -/
theorem realProfileChain_concat_bound {g : ℝ → ℝ} {n x y A B : ℝ} {l₁ l₂ : List ℝ}
    (hc₁ : RealProfileChain n l₁) (he₁ : realProfileChainEnd n l₁ = x)
    (hb₁ : realProfileChainCost g n l₁ ≤ A)
    (hc₂ : RealProfileChain x l₂) (he₂ : realProfileChainEnd x l₂ = y)
    (hb₂ : realProfileChainCost g x l₂ ≤ B) :
    RealProfileChain n (l₁ ++ l₂) ∧ realProfileChainEnd n (l₁ ++ l₂) = y ∧
      realProfileChainCost g n (l₁ ++ l₂) ≤ A + B := by
  refine ⟨realProfileChain_append n l₁ l₂ hc₁ (he₁ ▸ hc₂), ?_, ?_⟩
  · simpa only [realProfileChainEnd_append, he₁] using he₂
  · simpa only [realProfileChainCost_append, he₁] using add_le_add hb₁ hb₂

/-- Equality with the right endpoint at an interior point would itself make that point hard. -/
theorem profile_right_lt_of_no_hardPoint {g : ℝ → ℝ} (hg : Continuous g) {q p x : ℝ}
    (hq : 0 ≤ q) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) (hx : x ∈ Ioo q p) :
    g p < g x := by
  have hle := profile_right_le_of_no_hardPoint hg hq hp hgap hx
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hgap x hx
  refine ⟨⟨hq.trans hx.1.le, hx.2.le.trans hp.1.2⟩, fun z hz ↦ ?_⟩
  rw [← heq]
  rcases lt_or_ge z p with hzp | hzp
  · exact profile_right_le_of_no_hardPoint hg hq hp hgap ⟨hx.1.trans_le hz.1, hzp⟩
  · exact hp.2 z ⟨hzp, by linarith [hz.2, hx.2]⟩

/-- From an interior gap point there is a later strict minimum in its forward admissible window. -/
theorem exists_forward_gap_minimum {g : ℝ → ℝ} (hg : Continuous g) {q p x : ℝ}
    (hq : 0 ≤ q) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) (hx : x ∈ Ioo q p) :
    ∃ y : ℝ, x < y ∧ y ≤ min p ((1 + x) / 2) ∧ g y < g x ∧
      ∀ z ∈ Icc x (min p ((1 + x) / 2)), g y ≤ g z := by
  have hx1 : x < 1 := hx.2.trans_le hp.1.2
  by_cases hpm : p ≤ (1 + x) / 2
  · refine ⟨p, hx.2, by rw [min_eq_left hpm],
      profile_right_lt_of_no_hardPoint hg hq hp hgap hx, ?_⟩
    intro z hz
    rw [min_eq_left hpm] at hz
    rcases lt_or_eq_of_le hz.2 with hzp | rfl
    · exact profile_right_le_of_no_hardPoint hg hq hp hgap ⟨hx.1.trans_le hz.1, hzp⟩
    · exact le_rfl
  · have hnot := hgap x hx
    have hex : ∃ z ∈ Icc x ((1 + x) / 2), g z < g x := by
      by_contra h
      apply hnot
      refine ⟨⟨hq.trans hx.1.le, hx1.le⟩, fun z hz ↦ ?_⟩
      exact le_of_not_gt (fun hz' ↦ h ⟨z, hz, hz'⟩)
    obtain ⟨z, hz, hzx⟩ := hex
    obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.mpr (show x ≤ (1 + x) / 2 by linarith)) hg.continuousOn
    have hyx : g y < g x := (hmin hz).trans_lt hzx
    have hxy : x < y := lt_of_le_of_ne hy.1 (by intro heq; rw [← heq] at hyx; linarith)
    refine ⟨y, hxy, ?_, hyx, ?_⟩
    · simpa only [min_eq_right (le_of_not_ge hpm)] using hy.2
    · intro z hz
      exact hmin (by simpa only [min_eq_right (le_of_not_ge hpm)] using hz)

theorem realProfileEdgeCost_le_sub {g : ℝ → ℝ} {m n v : ℝ} (hmn : m ≤ n)
    (hmin : ∀ z ∈ Icc m n, v ≤ g z) : realProfileEdgeCost g m n ≤ g m - v := by
  have h := le_realProfileMin hmn hmin
  unfold realProfileEdgeCost
  linarith

theorem realProfileEdgeCost_eq_sub {g : ℝ → ℝ} (hg : Continuous g) {m n : ℝ}
    (hmn : m ≤ n) (hmin : ∀ z ∈ Icc m n, g n ≤ g z) :
    realProfileEdgeCost g m n = g m - g n := by
  rw [realProfileEdgeCost, realProfileMin_eq hg ⟨hmn, le_rfl⟩ hmin]

private theorem exists_realProfileChain_progress_aux {g A : ℝ → ℝ} {q n δ : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A n)
    (hstep : ∀ x ∈ Ico q n,
      (∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x ∧
        realProfileChainCost g n l ≤ A x) ∨
      ∃ z l, x + δ ≤ z ∧ z < n ∧ RealProfileChain z l ∧
        realProfileChainEnd z l = x ∧ realProfileChainCost g z l ≤ A x - A z) :
    ∀ (k : ℕ) (x : ℝ), q ≤ x → x ≤ n → n - x ≤ k * δ →
      ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x ∧
        realProfileChainCost g n l ≤ A x
  | 0, x, _, hxn, hk => by
    have hxn' : x = n := by norm_num at hk; linarith
    exact ⟨[], by simp [RealProfileChain], hxn'.symm, by simpa [hxn', realProfileChainCost]⟩
  | k + 1, x, hqx, hxn, hk => by
    rcases eq_or_lt_of_le hxn with rfl | hxn
    · exact ⟨[], by simp [RealProfileChain], rfl, hA⟩
    · rcases hstep x ⟨hqx, hxn⟩ with h | ⟨z, l₂, hxz, hzn, hc₂, he₂, hb₂⟩
      · exact h
      · have hk' : n - z ≤ k * δ := by push_cast at hk; linarith
        obtain ⟨l₁, hc₁, he₁, hb₁⟩ := exists_realProfileChain_progress_aux hδ hA hstep k z
          (by linarith) hzn.le hk'
        obtain ⟨hc, he, hb⟩ := realProfileChain_concat_bound hc₁ he₁ hb₁ hc₂ he₂ hb₂
        exact ⟨l₁ ++ l₂, hc, he, by linarith⟩

/-- Uniform progress of a finite chain extension gives a terminating chain construction. -/
theorem exists_realProfileChain_of_progress {g A : ℝ → ℝ} {q n δ : ℝ}
    (hqn : q ≤ n) (hδ : 0 < δ) (hA : 0 ≤ A n)
    (hstep : ∀ x ∈ Ico q n,
      (∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x ∧
        realProfileChainCost g n l ≤ A x) ∨
      ∃ z l, x + δ ≤ z ∧ z < n ∧ RealProfileChain z l ∧
        realProfileChainEnd z l = x ∧ realProfileChainCost g z l ≤ A x - A z) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = q ∧
      realProfileChainCost g n l ≤ A q := by
  obtain ⟨k, hk⟩ := exists_nat_ge ((n - q) / δ)
  exact exists_realProfileChain_progress_aux hδ hA hstep k q le_rfl hqn
    ((div_le_iff₀ hδ).mp hk)

private theorem profile_gap_minimum_lower_aux {g : ℝ → ℝ} (hg : Continuous g) {q p x : ℝ}
    (hq : 0 ≤ q) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) (hx : x ∈ Ioc q p) : g p ≤ g x := by
  rcases lt_or_eq_of_le hx.2 with hxp | rfl
  · exact profile_right_le_of_no_hardPoint hg hq hp hgap ⟨hx.1, hxp⟩
  · exact le_rfl

private theorem gap_minimum_stop_aux {g : ℝ → ℝ} {p x y n : ℝ}
    (hxn : x < n) (hny : n ≤ y) (hy : y ≤ min p ((1 + x) / 2))
    (hmin : ∀ z ∈ Icc x (min p ((1 + x) / 2)), g y ≤ g z) (hyg : g p ≤ g y) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x ∧
      realProfileChainCost g n l ≤ g x - g p := by
  refine ⟨[x], ?_, rfl, ?_⟩
  · simp only [RealProfileChain, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hxn, by linarith [(le_min_iff.mp hy).2]⟩
  · have hcost := realProfileEdgeCost_le_sub hxn.le (fun z hz ↦
      hmin z ⟨hz.1, hz.2.trans (hny.trans hy)⟩)
    simp only [realProfileChainCost, add_zero]
    linarith

private theorem gap_two_minima_progress_aux {g : ℝ → ℝ} (hg : Continuous g)
    {p x y z n : ℝ} (_hxn : x < n) (hn : n < 1)
    (hyx : x < y) (hy : y ≤ min p ((1 + x) / 2))
    (hminy : ∀ t ∈ Icc x (min p ((1 + x) / 2)), g y ≤ g t)
    (hzy : y < z) (hz : z ≤ min p ((1 + y) / 2))
    (hminz : ∀ t ∈ Icc y (min p ((1 + y) / 2)), g z ≤ g t)
    (hgzy : g z < g y) (hyg : g p ≤ g z) (hyn : y < n) :
    (∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x ∧
      realProfileChainCost g n l ≤ g x - g p) ∨
    ∃ w l, x + (1 - n) / 2 ≤ w ∧ w < n ∧ RealProfileChain w l ∧
      realProfileChainEnd w l = x ∧ realProfileChainCost g w l ≤
        (g x - g p) - (g w - g p) := by
  have hedge : RealProfileChain y [x] := by
    simp only [RealProfileChain, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hyx, by linarith [(le_min_iff.mp hy).2]⟩
  have hecost : realProfileChainCost g y [x] = g x - g y := by
    simp only [realProfileChainCost, add_zero]
    exact realProfileEdgeCost_eq_sub hg hyx.le fun t ht ↦ hminy t ⟨ht.1, ht.2.trans hy⟩
  by_cases hnz : n ≤ z
  · obtain ⟨l, hc, he, hb⟩ := gap_minimum_stop_aux hyn hnz hz hminz hyg
    obtain ⟨hc', he', hb'⟩ := realProfileChain_concat_bound hc he hb hedge rfl hecost.le
    exact Or.inl ⟨l ++ [x], hc', he', by linarith⟩
  · have hzm : (1 + x) / 2 < z := by
      by_contra h
      have hmem : z ∈ Icc x (min p ((1 + x) / 2)) :=
        ⟨hyx.le.trans hzy.le, le_min (le_min_iff.mp hz).1 (le_of_not_gt h)⟩
      exact hgzy.not_ge (hminy z hmem)
    refine Or.inr ⟨z, [y, x], by linarith, lt_of_not_ge hnz, ?_, rfl, ?_⟩
    · apply List.isChain_cons_cons.mpr
      exact ⟨⟨hzy, by linarith [(le_min_iff.mp hz).2]⟩, hedge⟩
    · have hzcost := realProfileEdgeCost_eq_sub hg hzy.le
        (fun t ht ↦ hminz t ⟨ht.1, ht.2.trans hz⟩)
      simp only [realProfileChainCost, add_zero, hzcost] at hecost ⊢
      linarith

/-- Starting inside a soft gap avoids its left boundary and gives the exact telescoping budget. -/
theorem exists_realProfileChain_inside_gap {g : ℝ → ℝ} (hg : Continuous g) {q p x n : ℝ}
    (hq : 0 ≤ q) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g)
    (hqx : q < x) (hxn : x ≤ n) (hnp : n ≤ p) (hn : n < 1) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x ∧
      realProfileChainCost g n l ≤ g x - g p := by
  apply exists_realProfileChain_of_progress (A := fun z ↦ g z - g p)
    (δ := (1 - n) / 2) hxn (by linarith)
    (sub_nonneg.mpr (profile_gap_minimum_lower_aux hg hq hp hgap
      ⟨hqx.trans_le hxn, hnp⟩))
  intro t ht
  have hqt : q < t := hqx.trans_le ht.1
  have htp : t < p := ht.2.trans_le hnp
  obtain ⟨y, hty, hy, hgy, hminy⟩ := exists_forward_gap_minimum hg hq hp hgap ⟨hqt, htp⟩
  by_cases hny : n ≤ y
  · exact Or.inl (gap_minimum_stop_aux ht.2 hny hy hminy
      (profile_gap_minimum_lower_aux hg hq hp hgap ⟨hqt.trans hty, (le_min_iff.mp hy).1⟩))
  · have hyn := lt_of_not_ge hny
    obtain ⟨z, hyz, hz, hgz, hminz⟩ := exists_forward_gap_minimum hg hq hp hgap
      ⟨hqt.trans hty, hyn.trans_le hnp⟩
    exact gap_two_minima_progress_aux hg ht.2 hn hty hy hminy hyz hz hminz hgz
      (profile_gap_minimum_lower_aux hg hq hp hgap
        ⟨(hqt.trans hty).trans hyz, (le_min_iff.mp hz).1⟩) hyn

/-- A whole gap can be crossed with arbitrarily small excess over its endpoint drop. -/
theorem exists_realProfileChain_across_gap {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {q p n ε : ℝ} (hq : 0 ≤ q) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g)
    (hqn : q < n) (hnp : n ≤ p) (hn : n < 1) (hε : 0 < ε) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = q ∧
      realProfileChainCost g n l ≤ g q - g p + ε := by
  have hqmid : q < (1 + q) / 2 := by linarith
  obtain ⟨x, hqx, hx⟩ := exists_between
    (lt_min hqn (lt_min (by linarith : q < q + ε / 2) hqmid))
  have hxn : x < n := hx.trans_le (min_le_left _ _)
  have hxε : x < q + ε / 2 := hx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hxmid : x < (1 + q) / 2 :=
    hx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨l, hc, he, hb⟩ :=
    exists_realProfileChain_inside_gap hg.continuous hq hp hgap hqx hxn.le hnp hn
  have heq : RealProfileChain x [q] := by
    simp only [RealProfileChain, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hqx, by linarith⟩
  have hcost : realProfileChainCost g x [q] ≤ x - q := by
    simpa only [realProfileChainCost, add_zero] using realProfileEdgeCost_le_length hg hqx.le
  obtain ⟨hc', he', hb'⟩ := realProfileChain_concat_bound hc he hb heq rfl hcost
  have hinc := (abs_le.mp (profile_increment_abs_le hg hqx.le)).2
  exact ⟨l ++ [q], hc', he', by linarith⟩

/-- A monotone interval can be traversed by an admissible chain of zero cost. -/
theorem exists_zero_realProfileChain_of_monotone {g : ℝ → ℝ} (hg : Continuous g)
    {q n : ℝ} (hqn : q ≤ n) (hn : n < 1) (hmono : MonotoneOn g (Icc q n)) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = q ∧
      realProfileChainCost g n l ≤ 0 := by
  apply exists_realProfileChain_of_progress (A := fun _ ↦ 0) (δ := (1 - n) / 2)
    hqn (by linarith) le_rfl
  intro x hx
  let y := min n (x + (1 - n) / 2)
  have hxy : x < y := lt_min hx.2 (by linarith)
  have hyn : y ≤ n := min_le_left _ _
  have hyd : y ≤ x + (1 - n) / 2 := min_le_right _ _
  have hc : RealProfileChain y [x] := by
    simp only [RealProfileChain, List.isChain_cons_cons, List.isChain_singleton, and_true]
    exact ⟨hxy, by linarith⟩
  have hcost : realProfileChainCost g y [x] = 0 := by
    simp only [realProfileChainCost, add_zero, realProfileEdgeCost]
    rw [realProfileMin_eq hg ⟨le_rfl, hxy.le⟩]
    · exact sub_self _
    · intro z hz
      exact hmono ⟨hx.1, hx.2.le⟩ ⟨hx.1.trans hz.1, hz.2.trans hyn⟩ hz.1
  rcases lt_or_eq_of_le hyn with hyn | heq
  · refine Or.inr ⟨y, [x], ?_, hyn, hc, rfl, by simpa using hcost.le⟩
    have hdn : x + (1 - n) / 2 ≤ n := by
      by_contra h
      have heq : y = n := min_eq_left (le_of_not_ge h)
      exact hyn.ne heq
    have : y = x + (1 - n) / 2 := min_eq_right hdn
    exact this.ge
  · exact Or.inl ⟨[x], by simpa only [heq] using hc, rfl,
      by simpa only [heq] using hcost.le⟩

/-- In particular, every closed interval of hard points has zero chain cost. -/
theorem exists_zero_realProfileChain_on_hard_interval {g : ℝ → ℝ} (hg : Continuous g)
    {q n : ℝ} (hqn : q ≤ n) (hn : n < 1) (hsub : Icc q n ⊆ hardProfilePoints g) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = q ∧
      realProfileChainCost g n l ≤ 0 :=
  exists_zero_realProfileChain_of_monotone hg hqn hn
    (monotoneOn_of_subset_hardProfilePoints hg hsub)

private theorem hardProfileSegment_budget_nonneg_aux {g : ℝ → ℝ} (hg : Continuous g)
    {q p c : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p)
    (hseg : (Icc q p ⊆ hardProfilePoints g ∧ c = 0) ∨
      (p ∈ hardProfilePoints g ∧ (∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) ∧
        c = g q - g p)) : 0 ≤ c := by
  rcases hseg with ⟨_, rfl⟩ | ⟨hp, hgap, rfl⟩
  · exact le_rfl
  · rcases lt_or_eq_of_le hqp with hqp | rfl
    · exact profile_gap_drop_nonneg hg hq hqp hp hgap
    · exact sub_nonneg.mpr le_rfl

/-- A hard cell costs zero; a soft cell costs its endpoint drop, up to arbitrary positive slack. -/
theorem exists_realProfileChain_on_segment {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    {q p n c ε : ℝ} (hq : 0 ≤ q) (hqn : q ≤ n) (hnp : n ≤ p) (hn : n < 1)
    (hε : 0 < ε)
    (hseg : (Icc q p ⊆ hardProfilePoints g ∧ c = 0) ∨
      (p ∈ hardProfilePoints g ∧ (∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) ∧
        c = g q - g p)) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = q ∧
      realProfileChainCost g n l ≤ c + ε := by
  have hc := hardProfileSegment_budget_nonneg_aux hg.continuous hq (hqn.trans hnp) hseg
  rcases eq_or_lt_of_le hqn with rfl | hqn
  · exact ⟨[], by simp [RealProfileChain], rfl, by simpa [realProfileChainCost] using
      (show 0 ≤ c + ε by linarith)⟩
  · rcases hseg with ⟨hsub, rfl⟩ | ⟨hp, hgap, rfl⟩
    · obtain ⟨l, hchain, hend, hcost⟩ := exists_zero_realProfileChain_on_hard_interval
        hg.continuous hqn.le hn (fun z hz ↦ hsub ⟨hz.1, hz.2.trans hnp⟩)
      exact ⟨l, hchain, hend, by linarith⟩
    · exact exists_realProfileChain_across_gap hg hq hp hgap hqn hnp hn hε

private theorem exists_realProfileChain_partition_aux {g : ℝ → ℝ} (hg : LipschitzWith 1 g)
    (x c : ℕ → ℝ) (hx : Monotone x) (hx₀ : 0 ≤ x 0) :
    ∀ (N : ℕ) (n ε : ℝ), x 0 ≤ n → n ≤ x N → n < 1 → 0 < ε →
      (∀ i < N, (Icc (x i) (x (i + 1)) ⊆ hardProfilePoints g ∧ c i = 0) ∨
        (x (i + 1) ∈ hardProfilePoints g ∧
          (∀ z ∈ Ioo (x i) (x (i + 1)), z ∉ hardProfilePoints g) ∧
          c i = g (x i) - g (x (i + 1)))) →
      ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = x 0 ∧
        realProfileChainCost g n l ≤ (∑ i ∈ Finset.range N, c i) + ε
  | 0, n, ε, h₀, hN, _, hε, _ => by
    have heq : n = x 0 := le_antisymm hN h₀
    exact ⟨[], by simp [RealProfileChain], heq, by simp [realProfileChainCost, hε.le]⟩
  | N + 1, n, ε, h₀, hN, hn, hε, hseg => by
    have hseg' := fun i hi ↦ hseg i (Nat.lt_succ_of_lt hi)
    have hcell := hseg N (Nat.lt_succ_self N)
    have hxc : 0 ≤ x N := hx₀.trans (hx (Nat.zero_le N))
    have hc := hardProfileSegment_budget_nonneg_aux hg.continuous hxc (hx (by omega)) hcell
    by_cases hnx : n ≤ x N
    · obtain ⟨l, hl, he, hb⟩ :=
        exists_realProfileChain_partition_aux hg x c hx hx₀ N n ε h₀ hnx hn hε hseg'
      refine ⟨l, hl, he, ?_⟩
      rw [Finset.sum_range_succ]
      linarith
    · have hxn : x N < n := lt_of_not_ge hnx
      obtain ⟨l₁, hl₁, he₁, hb₁⟩ := exists_realProfileChain_on_segment hg hxc hxn.le hN hn
        (show 0 < ε / 2 by linarith) hcell
      obtain ⟨l₂, hl₂, he₂, hb₂⟩ := exists_realProfileChain_partition_aux hg x c hx hx₀ N
        (x N) (ε / 2) (hx (Nat.zero_le N)) le_rfl (hxn.trans hn) (by linarith) hseg'
      obtain ⟨hl, he, hb⟩ := realProfileChain_concat_bound hl₁ he₁ hb₁ hl₂ he₂ hb₂
      refine ⟨l₁ ++ l₂, hl, he, ?_⟩
      rw [Finset.sum_range_succ]
      linarith

/-- A finite ordered hard/soft interval description gives the total-drop upper bound.
The budgets vanish on hard intervals and equal the endpoint drop on each complementary gap. -/
theorem exists_realProfileChain_of_finite_hard_partition {g : ℝ → ℝ}
    (hg : LipschitzWith 1 g) (x c : ℕ → ℝ) (N : ℕ) (hx : Monotone x)
    (hx₀ : x 0 = 0) (hxN : x N = 1)
    (hseg : ∀ i < N, (Icc (x i) (x (i + 1)) ⊆ hardProfilePoints g ∧ c i = 0) ∨
      (x (i + 1) ∈ hardProfilePoints g ∧
        (∀ z ∈ Ioo (x i) (x (i + 1)), z ∉ hardProfilePoints g) ∧
        c i = g (x i) - g (x (i + 1))))
    {n ε : ℝ} (hn₀ : 0 ≤ n) (hn : n < 1) (hε : 0 < ε) :
    ∃ l, RealProfileChain n l ∧ realProfileChainEnd n l = 0 ∧
      realProfileChainCost g n l ≤ (∑ i ∈ Finset.range N, c i) + ε := by
  simpa only [hx₀] using exists_realProfileChain_partition_aux hg x c hx
    (by simpa only [hx₀] using (le_rfl : (0 : ℝ) ≤ 0)) N n ε
    (by simpa only [hx₀] using hn₀) (by simpa only [hxN] using hn.le) hn hε hseg

end FalconerPacking
