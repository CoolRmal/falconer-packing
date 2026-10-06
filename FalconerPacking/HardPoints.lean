/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Hard points and the geometry of a profile gap

These are the geometric inequalities in Lemma A.2 of the focused proof. A hard point minimizes
the profile on the forward interval ending halfway between that point and one. Between two hard
points with no intervening hard point, the profile stays above its value at the right endpoint.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerPacking

/-- The forward hard-point set of a real profile on the unit interval. -/
def hardProfilePoints (g : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ Icc 0 1 ∧ ∀ z ∈ Icc x ((1 + x) / 2), g x ≤ g z}

private theorem hardProfilePoints_eq_aux (g : ℝ → ℝ) :
    hardProfilePoints g = Icc 0 1 ∩
      ⋂ t : Icc (0 : ℝ) 1, {x | g x ≤ g (x + (1 - x) * t / 2)} := by
  ext x
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨hx, mem_iInter.mpr fun t ↦ hg _ ⟨?_, ?_⟩⟩
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) t.property.1]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr t.property.2)]
  · rintro ⟨hx, hg⟩
    refine ⟨hx, fun z hz ↦ ?_⟩
    by_cases hx1 : x = 1
    · have hzx : z = x := by linarith [hz.1, hz.2]
      simp [hzx]
    · have hden : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hx1)
      let t : Icc (0 : ℝ) 1 := ⟨2 * (z - x) / (1 - x),
        div_nonneg (by linarith [hz.1]) hden.le,
        (div_le_one hden).mpr (by linarith [hz.2])⟩
      have ht : x + (1 - x) * (t : ℝ) / 2 = z := by
        dsimp [t]
        field_simp
        ring
      simpa only [mem_setOf_eq, ht] using mem_iInter.mp hg t

/-- The hard-point set of a continuous profile is closed. -/
theorem isClosed_hardProfilePoints {g : ℝ → ℝ} (hg : Continuous g) :
    IsClosed (hardProfilePoints g) := by
  rw [hardProfilePoints_eq_aux]
  refine isClosed_Icc.inter (isClosed_iInter fun t ↦ ?_)
  apply isClosed_le hg
  exact hg.comp (continuous_id.add
    (((continuous_const.sub continuous_id).mul continuous_const).div_const 2))

/-- The hard-point set of a continuous profile is compact. -/
theorem isCompact_hardProfilePoints {g : ℝ → ℝ} (hg : Continuous g) :
    IsCompact (hardProfilePoints g) :=
  isCompact_Icc.of_isClosed_subset (isClosed_hardProfilePoints hg) fun _ hx ↦ hx.1

/-- The right endpoint is always hard. -/
theorem one_mem_hardProfilePoints (g : ℝ → ℝ) : 1 ∈ hardProfilePoints g := by
  refine ⟨by norm_num, fun z hz ↦ ?_⟩
  have : z = 1 := by rcases hz with ⟨h₁, h₂⟩; linarith
  simp [this]

/-- A nonnegative profile vanishing at zero has a hard left endpoint. -/
theorem zero_mem_hardProfilePoints {g : ℝ → ℝ} (hzero : g 0 = 0)
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x) : 0 ∈ hardProfilePoints g := by
  refine ⟨by norm_num, fun z hz ↦ ?_⟩
  rw [hzero]
  exact hnonneg z ⟨hz.1, by linarith [hz.2]⟩

/-- A continuous profile is nondecreasing on every interval consisting of hard points. -/
theorem monotoneOn_of_subset_hardProfilePoints {g : ℝ → ℝ} (hg : Continuous g) {p q : ℝ}
    (hsub : Icc p q ⊆ hardProfilePoints g) : MonotoneOn g (Icc p q) := by
  intro x hx y hy hxy
  by_contra h
  have hdrop : g y < g x := lt_of_not_ge h
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hxy)
    hg.continuousOn
  let M : Set ℝ := Icc x y ∩ {z | g z = g v}
  have hM : IsCompact M := isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  obtain ⟨z, hz, hzmax⟩ := hM.exists_isMaxOn ⟨v, hv, rfl⟩ continuous_id.continuousOn
  have hzval : g z = g v := hz.2
  have hzx : g x ≤ g v := hmax ⟨le_rfl, hxy⟩
  have hzy : z < y := lt_of_le_of_ne hz.1.2 (by
    intro heq
    rw [heq] at hzval
    linarith)
  have hzhard := hsub ⟨hx.1.trans hz.1.1, hz.1.2.trans hy.2⟩
  have hyone : y ≤ 1 := (hsub hy).1.2
  let w : ℝ := min y ((1 + z) / 2)
  have hzw : z < w := lt_min hzy (by linarith)
  have hw : w ∈ Icc x y := ⟨hz.1.1.trans hzw.le, min_le_left _ _⟩
  have hzwval : g z ≤ g w := hzhard.2 w ⟨hzw.le, min_le_right _ _⟩
  have hwval : g w = g v := le_antisymm (hmax hw) (hzval ▸ hzwval)
  have hwz : w ≤ z := hzmax ⟨hw, hwval⟩
  exact hzw.not_ge hwz

/-- Inside a gap with hard right endpoint, the profile cannot go below that endpoint. -/
theorem profile_right_le_of_no_hardPoint {g : ℝ → ℝ} (hg : Continuous g) {q p x : ℝ}
    (hq : 0 ≤ q) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) (hx : x ∈ Ioo q p) :
    g p ≤ g x := by
  by_contra h
  have hxp : g x < g p := lt_of_not_ge h
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hx.2.le)
    hg.continuousOn
  have hzval : g z ≤ g x := hmin ⟨le_rfl, hx.2.le⟩
  have hzp : z < p := lt_of_le_of_ne hz.2 (by
    intro heq
    rw [heq] at hzval
    exact (not_le_of_gt hxp) hzval)
  apply hgap z ⟨hx.1.trans_le hz.1, hzp⟩
  refine ⟨⟨hq.trans (hx.1.le.trans hz.1), hzp.le.trans hp.1.2⟩, fun u hu ↦ ?_⟩
  by_cases hup : u ≤ p
  · exact hmin ⟨hz.1.trans hu.1, hup⟩
  · have hpu : g p ≤ g u := hp.2 u ⟨(lt_of_not_ge hup).le, by linarith [hu.2]⟩
    exact hzval.trans (hxp.le.trans hpu)

/-- A continuous profile has a nonnegative drop across a gap of the hard-point set. -/
theorem profile_gap_drop_nonneg {g : ℝ → ℝ} (hg : Continuous g) {q p : ℝ}
    (hq : 0 ≤ q) (hqp : q < p) (hp : p ∈ hardProfilePoints g)
    (hgap : ∀ z ∈ Ioo q p, z ∉ hardProfilePoints g) : 0 ≤ g q - g p := by
  have hsub : Ioo q p ⊆ {x | g p ≤ g x} :=
    fun _ hx ↦ profile_right_le_of_no_hardPoint hg hq hp hgap hx
  have hclosed : IsClosed {x | g p ≤ g x} := isClosed_le continuous_const hg
  have hqmem : q ∈ closure (Ioo q p) := by
    rw [closure_Ioo hqp.ne]
    exact ⟨le_rfl, hqp.le⟩
  exact sub_nonneg.mpr ((closure_minimal hsub hclosed) hqmem)

/-- A positive drop after a hard point forces the next endpoint beyond the forward midpoint. -/
theorem midpoint_lt_of_hardPoint_drop {g : ℝ → ℝ} {q p : ℝ}
    (hq : q ∈ hardProfilePoints g) (hqp : q ≤ p) (hdrop : g p < g q) :
    (1 + q) / 2 < p := by
  by_contra h
  exact (not_le_of_gt hdrop) (hq.2 p ⟨hqp, le_of_not_gt h⟩)

/-- The positive gap drop is bounded by the distance beyond its forward midpoint. -/
theorem profile_gap_drop_le {g : ℝ → ℝ} (hg : LipschitzWith 1 g) {q p : ℝ}
    (hq : q ∈ hardProfilePoints g) (hqp : q ≤ p) (hdrop : g p < g q) :
    g q - g p ≤ p - (1 + q) / 2 := by
  have hmid := midpoint_lt_of_hardPoint_drop hq hqp hdrop
  have hhard : g q ≤ g ((1 + q) / 2) := hq.2 _ ⟨by linarith [hq.1.2], le_rfl⟩
  have hlip := hg.dist_le_mul ((1 + q) / 2) p
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hlip
  rw [abs_of_nonpos (by linarith : (1 + q) / 2 - p ≤ 0)] at hlip
  have := (abs_le.mp hlip).2
  linarith

end FalconerPacking
