/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.HardPointChains
public import FalconerPacking.ChainCompression

/-!
# Uniformly short real-endpoint chains

Greedy merging removes intermediate scales without increasing the profile cost. In the
remaining chain, every two edges more than double the distance from one. Thus the number
of edges depends only on the initial distance from one, not on the profile.
-/

@[expose] public section

noncomputable section

namespace FalconerPacking

/-- Removing an intermediate real scale cannot increase the edge cost. -/
theorem realProfileEdgeCost_merge_le {g : ℝ → ℝ} (hg : Continuous g) {m p n : ℝ}
    (hmp : m ≤ p) (hpn : p ≤ n) :
    realProfileEdgeCost g m n ≤ realProfileEdgeCost g m p + realProfileEdgeCost g p n := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (hmp.trans hpn)) hg.continuousOn
  have heq := realProfileMin_eq hg hx (fun z hz ↦ hmin hz)
  have hleft := realProfileMin_le hg (show p ∈ Set.Icc m p from ⟨hmp, le_rfl⟩)
  have hright := realProfileMin_le hg (show p ∈ Set.Icc p n from ⟨le_rfl, hpn⟩)
  unfold realProfileEdgeCost
  rw [heq]
  rcases le_total x p with hxp | hpx
  · have h := realProfileMin_le hg (show x ∈ Set.Icc m p from ⟨hx.1, hxp⟩)
    linarith
  · have h := realProfileMin_le hg (show x ∈ Set.Icc p n from ⟨hpx, hx.2⟩)
    linarith

/-- Greedily erase any scale whose two adjacent edges can be merged admissibly. -/
def compressRealProfileChain : ℝ → List ℝ → List ℝ
  | _, [] => []
  | _, [m] => [m]
  | n, m :: k :: tail =>
      if 2 * n - k ≤ 1 then compressRealProfileChain n (k :: tail)
      else m :: compressRealProfileChain m (k :: tail)

/-- In an irreducible chain, no two adjacent edges can be merged. -/
def RealProfileChainIrreducible : ℝ → List ℝ → Prop
  | _, [] => True
  | _, [_] => True
  | n, m :: k :: tail => ¬2 * n - k ≤ 1 ∧ RealProfileChainIrreducible m (k :: tail)

theorem compressRealProfileChain_sublist : ∀ (n : ℝ) (l : List ℝ),
    (compressRealProfileChain n l).Sublist l
  | _, [] => List.Sublist.refl _
  | _, [_] => List.Sublist.refl _
  | n, m :: k :: tail => by
    rw [compressRealProfileChain]
    split
    · exact (compressRealProfileChain_sublist n (k :: tail)).cons m
    · exact (compressRealProfileChain_sublist m (k :: tail)).cons_cons m

theorem realProfileChainEnd_compress : ∀ (n : ℝ) (l : List ℝ),
    realProfileChainEnd n (compressRealProfileChain n l) = realProfileChainEnd n l
  | _, [] => rfl
  | _, [_] => rfl
  | n, m :: k :: tail => by
    rw [compressRealProfileChain]
    split
    · exact realProfileChainEnd_compress n (k :: tail)
    · exact realProfileChainEnd_compress m (k :: tail)

theorem realProfileChain_compress : ∀ (n : ℝ) (l : List ℝ),
    RealProfileChain n l → RealProfileChain n (compressRealProfileChain n l)
  | _, [], h => h
  | _, [_], h => h
  | n, m :: k :: tail, h => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
    obtain ⟨hmk, hrest⟩ := List.isChain_cons_cons.mp htail
    rw [compressRealProfileChain]
    split
    · exact realProfileChain_compress n (k :: tail)
        (List.isChain_cons_cons.mpr ⟨⟨hmk.1.trans hnm.1, by assumption⟩, hrest⟩)
    · exact List.isChain_cons_cons.mpr
        ⟨hnm, realProfileChain_compress m (k :: tail)
          (List.isChain_cons_cons.mpr ⟨hmk, hrest⟩)⟩

theorem realProfileChainCost_compress_le {g : ℝ → ℝ} (hg : Continuous g) :
    ∀ (n : ℝ) (l : List ℝ), List.IsChain (· > ·) (n :: l) →
      realProfileChainCost g n (compressRealProfileChain n l) ≤ realProfileChainCost g n l
  | _, [], _ => le_rfl
  | _, [_], _ => le_rfl
  | n, m :: k :: tail, h => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
    obtain ⟨hmk, hrest⟩ := List.isChain_cons_cons.mp htail
    rw [compressRealProfileChain]
    split
    · have hrec := realProfileChainCost_compress_le hg n (k :: tail)
        (List.isChain_cons_cons.mpr ⟨hmk.trans hnm, hrest⟩)
      have hmerge := realProfileEdgeCost_merge_le hg hmk.le hnm.le
      simp only [realProfileChainCost] at hrec ⊢
      linarith
    · exact add_le_add le_rfl (realProfileChainCost_compress_le hg m (k :: tail)
        (List.isChain_cons_cons.mpr ⟨hmk, hrest⟩))

theorem realProfileChainEnd_le : ∀ (n : ℝ) (l : List ℝ),
    List.IsChain (· > ·) (n :: l) → realProfileChainEnd n l ≤ n
  | _, [], _ => le_rfl
  | n, m :: tail, h => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
    exact (realProfileChainEnd_le m tail htail).trans hnm.le

theorem realProfileChainIrreducible_compress : ∀ (n : ℝ) (l : List ℝ),
    List.IsChain (· > ·) (n :: l) →
      RealProfileChainIrreducible n (compressRealProfileChain n l)
  | _, [], _ => trivial
  | _, [_], _ => trivial
  | n, m :: k :: tail, h => by
    obtain ⟨hnm, htail⟩ := List.isChain_cons_cons.mp h
    obtain ⟨hmk, hrest⟩ := List.isChain_cons_cons.mp htail
    rw [compressRealProfileChain]
    split
    · exact realProfileChainIrreducible_compress n (k :: tail)
        (List.isChain_cons_cons.mpr ⟨hmk.trans hnm, hrest⟩)
    · have hrec := realProfileChainIrreducible_compress m (k :: tail)
        (List.isChain_cons_cons.mpr ⟨hmk, hrest⟩)
      cases heq : compressRealProfileChain m (k :: tail) with
      | nil => trivial
      | cons p rest =>
        refine ⟨?_, by simpa only [heq] using hrec⟩
        have hp : p ∈ k :: tail := (compressRealProfileChain_sublist m (k :: tail)).subset
          (by simp only [heq, List.mem_cons, true_or])
        have hpk : p ≤ k := by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact le_rfl
          · exact (hrest.rel_cons hp).le
        linarith

theorem RealProfileChainIrreducible.tail {n m : ℝ} {l : List ℝ}
    (h : RealProfileChainIrreducible n (m :: l)) : RealProfileChainIrreducible m l := by
  cases l with
  | nil => trivial
  | cons k rest => exact h.2

/-- A fixed number of complementary-gap doublings bounds the compressed length. -/
theorem RealProfileChainIrreducible.length_le_of_pow_gap :
    ∀ (k : ℕ) (n : ℝ) (l : List ℝ), n ≤ 1 → 0 ≤ realProfileChainEnd n l →
      List.IsChain (· > ·) (n :: l) → RealProfileChainIrreducible n l →
      1 ≤ (2 : ℝ) ^ k * (1 - n) → l.length ≤ 2 * k
  | 0, n, l, _, hend, hchain, _, hscale => by
    have hn : n ≤ 0 := by norm_num at hscale; linarith
    cases l with
    | nil => simp
    | cons m tail =>
      have hnm := (List.isChain_cons_cons.mp hchain).1
      have ht := realProfileChainEnd_le m tail hchain.tail
      change 0 ≤ realProfileChainEnd m tail at hend
      linarith
  | k + 1, _, [], _, _, _, _, _ => by simp
  | k + 1, _, [_], _, _, _, _, _ => by simp; omega
  | k + 1, n, m :: p :: tail, hn, hend, hchain, hirr, hscale => by
    have hnm := (List.isChain_cons_cons.mp hchain).1
    have hmp := (List.isChain_cons_cons.mp hchain.tail).1
    have hp : p ≤ 1 := hmp.le.trans (hnm.le.trans hn)
    have hdouble : 2 * (1 - n) ≤ 1 - p := by have h := hirr.1; linarith
    have hscale' : 1 ≤ (2 : ℝ) ^ k * (1 - p) := hscale.trans (by
      calc
        (2 : ℝ) ^ (k + 1) * (1 - n) = (2 : ℝ) ^ k * (2 * (1 - n)) := by ring
        _ ≤ (2 : ℝ) ^ k * (1 - p) := mul_le_mul_of_nonneg_left hdouble (by positivity))
    have hlength := hirr.tail.tail.length_le_of_pow_gap k p tail hp hend
      hchain.tail.tail hscale'
    simp only [List.length_cons] at *
    omega

/-- Compression keeps both endpoints, all admissibility inequalities, and the cost bound. -/
theorem exists_compressed_realProfileChain {g : ℝ → ℝ} (hg : Continuous g)
    {n : ℝ} {l : List ℝ} {k : ℕ} (hn : n ≤ 1) (hend : 0 ≤ realProfileChainEnd n l)
    (hchain : RealProfileChain n l) (hscale : 1 ≤ (2 : ℝ) ^ k * (1 - n)) :
    ∃ l' : List ℝ, l'.Sublist l ∧ RealProfileChain n l' ∧
      realProfileChainEnd n l' = realProfileChainEnd n l ∧
      realProfileChainCost g n l' ≤ realProfileChainCost g n l ∧ l'.length ≤ 2 * k := by
  have hdecr := hchain.imp (fun _ _ h ↦ h.1)
  have hc := realProfileChain_compress n l hchain
  have hi := realProfileChainIrreducible_compress n l hdecr
  refine ⟨compressRealProfileChain n l, compressRealProfileChain_sublist n l, hc,
    realProfileChainEnd_compress n l, realProfileChainCost_compress_le hg n l hdecr, ?_⟩
  exact hi.length_le_of_pow_gap k n _ hn (by simpa only [realProfileChainEnd_compress] using hend)
    (hc.imp (fun _ _ h ↦ h.1)) hscale

/-- The length bound depends only on a positive initial gap from one. -/
theorem exists_uniform_realProfileChain_length {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ K : ℕ, ∀ (n : ℝ) (l : List ℝ), n ≤ 1 - ζ → 0 ≤ realProfileChainEnd n l →
      RealProfileChain n l → (compressRealProfileChain n l).length ≤ K := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ζ) (by norm_num : (1 : ℝ) < 2)
  have hk' : 1 ≤ (2 : ℝ) ^ k * ζ := ((div_lt_iff₀ hζ).mp hk).le
  refine ⟨2 * k, fun n l hn hend hc ↦ ?_⟩
  have hc' := realProfileChain_compress n l hc
  exact (realProfileChainIrreducible_compress n l (hc.imp (fun _ _ h ↦ h.1))).length_le_of_pow_gap
    k n _ (by linarith) (by simpa only [realProfileChainEnd_compress] using hend)
    (hc'.imp (fun _ _ h ↦ h.1))
    (hk'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)))

end FalconerPacking
