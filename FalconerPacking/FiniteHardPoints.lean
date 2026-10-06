/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.ProfileInterpolation
public import FalconerPacking.HardPoints
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Finite interval geometry of interpolated hard-point sets

For a finite linear interpolant, lower bounds on an interval can be checked at its endpoints
and intervening grid nodes. Slicing by the cells containing a point and its forward midpoint
then expresses its hard-point set as a finite union of closed intervals.
-/

@[expose] public section

noncomputable section

open Set

namespace FalconerPacking

private theorem affine_lower_between_aux {a b c x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z) (hx : c ≤ a * x + b) (hz : c ≤ a * z + b) :
    c ≤ a * y + b := by
  by_cases ha : 0 ≤ a
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxy)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge ha)) (sub_nonneg.mpr hyz)]

/-- A bound at the real endpoints and intervening nodes bounds the entire interpolant. -/
theorem profileInterpolation_lower_of_endpoints_and_knots {g : ℕ → ℝ} {N : ℕ}
    {c x y z : ℝ} (hx : x ∈ Icc (0 : ℝ) N) (hy : y ∈ Icc (0 : ℝ) N)
    (hleft : c ≤ profileInterpolation g N x) (hright : c ≤ profileInterpolation g N y)
    (hknots : ∀ j : ℕ, j ≤ N → (j : ℝ) ∈ Icc x y → c ≤ g j)
    (hz : z ∈ Icc x y) : c ≤ profileInterpolation g N z := by
  have hz₀ : 0 ≤ z := hx.1.trans hz.1
  have hzN : z ≤ N := hz.2.trans hy.2
  rcases lt_or_eq_of_le hzN with hzN | rfl
  · let j := ⌊z⌋₊
    have hjz : (j : ℝ) ≤ z := Nat.floor_le hz₀
    have hzj : z ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one z).le
    have hjN : j < N := by exact_mod_cast hjz.trans_lt hzN
    let l := max x (j : ℝ)
    let r := min y ((j : ℝ) + 1)
    have hlz : l ≤ z := max_le hz.1 hjz
    have hzr : z ≤ r := le_min hz.2 hzj
    have hl : l ∈ Icc (j : ℝ) (j + 1) := ⟨le_max_right _ _, hlz.trans hzj⟩
    have hr : r ∈ Icc (j : ℝ) (j + 1) := ⟨hjz.trans hzr, min_le_right _ _⟩
    have hlower : c ≤ profileInterpolation g N l := by
      rcases le_total x (j : ℝ) with h | h
      · rw [show l = j from max_eq_right h, profileInterpolation_natCast g hjN.le]
        exact hknots j hjN.le ⟨h, hjz.trans hz.2⟩
      · simpa only [l, max_eq_left h] using hleft
    have hupper : c ≤ profileInterpolation g N r := by
      rcases le_total y ((j : ℝ) + 1) with h | h
      · simpa only [r, min_eq_left h] using hright
      · have hrj : r = ((j + 1 : ℕ) : ℝ) := by simp [r, min_eq_right h]
        rw [hrj, profileInterpolation_natCast g hjN]
        exact hknots (j + 1) hjN ⟨by push_cast; exact hz.1.trans hzj, by simpa using h⟩
    rw [profileInterpolation_on_cell g N j hjN l hl.1 hl.2] at hlower
    rw [profileInterpolation_on_cell g N j hjN r hr.1 hr.2] at hupper
    rw [profileInterpolation_on_cell g N j hjN z hjz hzj]
    have h := affine_lower_between_aux hlz hzr
      (by nlinarith [hlower] : c ≤ (g (j + 1) - g j) * l +
        (g j - j * (g (j + 1) - g j)))
      (by nlinarith [hupper] : c ≤ (g (j + 1) - g j) * r +
        (g j - j * (g (j + 1) - g j)))
    nlinarith [h]
  · have hyN : y = N := le_antisymm hy.2 hz.2
    simpa only [hyN] using hright

/-- The normalized profile is affine on each of its grid cells. -/
theorem normalizedProfileInterpolation_on_cell {g : ℕ → ℝ} {N j : ℕ}
    (hN : 0 < N) (hj : j < N) {x : ℝ}
    (hx : x ∈ Icc (j / N : ℝ) (((j : ℝ) + 1) / N)) :
    normalizedProfileInterpolation g N x = (g (j + 1) - g j) * x +
      (g j - j * (g (j + 1) - g j)) / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hleft : (j : ℝ) ≤ N * x := by nlinarith [(div_le_iff₀ hN').mp hx.1]
  have hright : (N : ℝ) * x ≤ j + 1 := by nlinarith [(le_div_iff₀ hN').mp hx.2]
  rw [normalizedProfileInterpolation, profileInterpolation_on_cell g N j hj _ hleft hright]
  field_simp
  ring

/-- The endpoint-and-knot bound is unchanged by normalizing both coordinates. -/
theorem normalizedProfileInterpolation_lower_of_endpoints_and_knots
    {g : ℕ → ℝ} {N : ℕ} (hN : 0 < N) {c x y z : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hleft : c ≤ normalizedProfileInterpolation g N x)
    (hright : c ≤ normalizedProfileInterpolation g N y)
    (hknots : ∀ j : ℕ, j ≤ N → (j / N : ℝ) ∈ Icc x y → c ≤ g j / N)
    (hz : z ∈ Icc x y) : c ≤ normalizedProfileInterpolation g N z := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hN').mpr
  apply profileInterpolation_lower_of_endpoints_and_knots
    (x := N * x) (y := N * y)
  · exact ⟨mul_nonneg hN'.le hx.1, by nlinarith [hx.2]⟩
  · exact ⟨mul_nonneg hN'.le hy.1, by nlinarith [hy.2]⟩
  · exact (le_div_iff₀ hN').mp hleft
  · exact (le_div_iff₀ hN').mp hright
  · intro j hj hjxy
    apply (le_div_iff₀ hN').mp (hknots j hj ?_)
    exact ⟨(le_div_iff₀ hN').mpr (by nlinarith [hjxy.1]),
      (div_le_iff₀ hN').mpr (by nlinarith [hjxy.2])⟩
  · exact ⟨mul_le_mul_of_nonneg_left hz.1 hN'.le,
      mul_le_mul_of_nonneg_left hz.2 hN'.le⟩

/-- On fixed cells for a point and its midpoint, hardness is a finite list of inequalities. -/
theorem mem_hardProfilePoints_normalized_iff {g : ℕ → ℝ} {N j k : ℕ}
    (hN : 0 < N) (hk : k < N) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1)
    (hxj : x ∈ Icc (j / N : ℝ) (((j : ℝ) + 1) / N))
    (hxk : (1 + x) / 2 ∈ Icc (k / N : ℝ) (((k : ℝ) + 1) / N)) :
    x ∈ hardProfilePoints (normalizedProfileInterpolation g N) ↔
      normalizedProfileInterpolation g N x ≤
        normalizedProfileInterpolation g N ((1 + x) / 2) ∧
      ∀ l : ℕ, j + 1 ≤ l → l ≤ k →
        normalizedProfileInterpolation g N x ≤ g l / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro h
    refine ⟨h.2 _ ⟨by linarith [hx.2], le_rfl⟩, fun l hjl hlk ↦ ?_⟩
    rw [← normalizedProfileInterpolation_natCast g hN (hlk.trans hk.le)]
    apply h.2
    constructor
    · apply hxj.2.trans
      apply (div_le_div_iff_of_pos_right hN').mpr
      exact_mod_cast hjl
    · apply le_trans _ hxk.1
      exact (div_le_div_iff_of_pos_right hN').mpr (by exact_mod_cast hlk)
  · rintro ⟨hmid, hknots⟩
    refine ⟨hx, fun z hz ↦ ?_⟩
    apply normalizedProfileInterpolation_lower_of_endpoints_and_knots hN hx
      ⟨by linarith [hx.1], by linarith [hx.2]⟩ le_rfl hmid _ hz
    intro l hl hlx
    by_cases hjl : j + 1 ≤ l
    · by_cases hlk : l ≤ k
      · exact hknots l hjl hlk
      · have hkl : k + 1 ≤ l := by omega
        have hmidl : (1 + x) / 2 = (l / N : ℝ) := by
          apply le_antisymm _ hlx.2
          apply hxk.2.trans
          apply (div_le_div_iff_of_pos_right hN').mpr
          exact_mod_cast hkl
        simpa only [hmidl, normalizedProfileInterpolation_natCast g hN hl] using hmid
    · have hlj : l ≤ j := by omega
      have hxl : x = (l / N : ℝ) := by
        apply le_antisymm hlx.1
        apply le_trans _ hxj.1
        exact (div_le_div_iff_of_pos_right hN').mpr (by exact_mod_cast hlj)
      rw [hxl, normalizedProfileInterpolation_natCast g hN hl]

/-- Hard points with specified cells for the point and its forward midpoint. -/
def hardProfileSlice (g : ℕ → ℝ) (N j k : ℕ) : Set ℝ :=
  hardProfilePoints (normalizedProfileInterpolation g N) ∩
    (Icc (j / N : ℝ) (((j : ℝ) + 1) / N) ∩
      {x | (1 + x) / 2 ∈ Icc (k / N : ℝ) (((k : ℝ) + 1) / N)})

/-- Each hard-point cell slice is compact. -/
theorem isCompact_hardProfileSlice (g : ℕ → ℝ) (N j k : ℕ) :
    IsCompact (hardProfileSlice g N j k) := by
  apply (isCompact_hardProfilePoints (continuous_normalizedProfileInterpolation g N)).inter_right
  exact isClosed_Icc.inter (isClosed_Icc.preimage (by fun_prop))

private theorem affine_le_between_aux {a b c d x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z) (hx : a * x + b ≤ c * x + d)
    (hz : a * z + b ≤ c * z + d) : a * y + b ≤ c * y + d := by
  have h := affine_lower_between_aux hxy hyz
    (by nlinarith [hx] : 0 ≤ (c - a) * x + (d - b))
    (by nlinarith [hz] : 0 ≤ (c - a) * z + (d - b))
  nlinarith [h]

private theorem hardProfileSlice_midpoint_aux {g : ℕ → ℝ} {N j k : ℕ}
    (hN : 0 < N) (hj : j < N) (hk : k < N) {x y z : ℝ}
    (hx : x ∈ hardProfileSlice g N j k) (hz : z ∈ hardProfileSlice g N j k)
    (hy : y ∈ Icc x z)
    (hyj : y ∈ Icc (j / N : ℝ) (((j : ℝ) + 1) / N))
    (hyk : (1 + y) / 2 ∈ Icc (k / N : ℝ) (((k : ℝ) + 1) / N)) :
    normalizedProfileInterpolation g N y ≤
      normalizedProfileInterpolation g N ((1 + y) / 2) := by
  have hmidₓ := hx.1.2 ((1 + x) / 2) ⟨by linarith [hx.1.1.2], le_rfl⟩
  have hmidᵤ := hz.1.2 ((1 + z) / 2) ⟨by linarith [hz.1.1.2], le_rfl⟩
  rw [normalizedProfileInterpolation_on_cell hN hj hx.2.1,
    normalizedProfileInterpolation_on_cell hN hk hx.2.2] at hmidₓ
  rw [normalizedProfileInterpolation_on_cell hN hj hz.2.1,
    normalizedProfileInterpolation_on_cell hN hk hz.2.2] at hmidᵤ
  rw [normalizedProfileInterpolation_on_cell hN hj hyj,
    normalizedProfileInterpolation_on_cell hN hk hyk]
  have h := affine_le_between_aux hy.1 hy.2
    (by nlinarith [hmidₓ] : (g (j + 1) - g j) * x +
      (g j - j * (g (j + 1) - g j)) / N ≤
      ((g (k + 1) - g k) / 2) * x + ((g (k + 1) - g k) / 2 +
        (g k - k * (g (k + 1) - g k)) / N))
    (by nlinarith [hmidᵤ] : (g (j + 1) - g j) * z +
      (g j - j * (g (j + 1) - g j)) / N ≤
      ((g (k + 1) - g k) / 2) * z + ((g (k + 1) - g k) / 2 +
        (g k - k * (g (k + 1) - g k)) / N))
  nlinarith [h]

/-- A hard-point slice contains every point between two of its members. -/
theorem ordConnected_hardProfileSlice {g : ℕ → ℝ} {N j k : ℕ}
    (hN : 0 < N) (hj : j < N) (hk : k < N) :
    OrdConnected (hardProfileSlice g N j k) := by
  refine ⟨fun x hx z hz y hy ↦ ?_⟩
  have hyunit : y ∈ Icc (0 : ℝ) 1 := ⟨hx.1.1.1.trans hy.1, hy.2.trans hz.1.1.2⟩
  have hyj : y ∈ Icc (j / N : ℝ) (((j : ℝ) + 1) / N) :=
    ⟨hx.2.1.1.trans hy.1, hy.2.trans hz.2.1.2⟩
  have hyk : (1 + y) / 2 ∈ Icc (k / N : ℝ) (((k : ℝ) + 1) / N) :=
    ⟨by linarith [hx.2.2.1, hy.1], by linarith [hz.2.2.2, hy.2]⟩
  refine ⟨(mem_hardProfilePoints_normalized_iff hN hk hyunit hyj hyk).mpr ?_, hyj, hyk⟩
  refine ⟨hardProfileSlice_midpoint_aux hN hj hk hx hz hy hyj hyk, fun l hjl hlk ↦ ?_⟩
  have hleft := ((mem_hardProfilePoints_normalized_iff hN hk hx.1.1
    hx.2.1 hx.2.2).mp hx.1).2 l hjl hlk
  have hright := ((mem_hardProfilePoints_normalized_iff hN hk hz.1.1
    hz.2.1 hz.2.2).mp hz.1).2 l hjl hlk
  rw [normalizedProfileInterpolation_on_cell hN hj hx.2.1] at hleft
  rw [normalizedProfileInterpolation_on_cell hN hj hz.2.1] at hright
  rw [normalizedProfileInterpolation_on_cell hN hj hyj]
  simpa using affine_le_between_aux hy.1 hy.2
    (by simpa using hleft : (g (j + 1) - g j) * x +
      (g j - j * (g (j + 1) - g j)) / N ≤ 0 * x + g l / N)
    (by simpa using hright : (g (j + 1) - g j) * z +
      (g j - j * (g (j + 1) - g j)) / N ≤ 0 * z + g l / N)

/-- The closed normalized grid cells cover the unit interval, including its right endpoint. -/
theorem exists_normalized_profile_cell {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ j : Fin N, x ∈ Icc ((j : ℕ) / N : ℝ) ((((j : ℕ) : ℝ) + 1) / N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le hx.2 with hx1 | rfl
  · let j := ⌊(N : ℝ) * x⌋₊
    have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg hN'.le hx.1
    have hjx : (j : ℝ) ≤ N * x := Nat.floor_le hNx
    have hxj : (N : ℝ) * x < j + 1 := Nat.lt_floor_add_one _
    have hjN : j < N := by exact_mod_cast (hjx.trans_lt (by nlinarith : (N : ℝ) * x < N))
    refine ⟨⟨j, hjN⟩, (div_le_iff₀ hN').mpr ?_, (le_div_iff₀ hN').mpr ?_⟩
    · simpa only [mul_comm] using hjx
    · simpa only [mul_comm] using hxj.le
  · have hpred : N - 1 + 1 = N := by omega
    refine ⟨⟨N - 1, by omega⟩, (div_le_iff₀ hN').mpr ?_, (le_div_iff₀ hN').mpr ?_⟩
    · simp only [one_mul]
      exact_mod_cast Nat.sub_le N 1
    · have hcast : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hpred
      simp only [one_mul, hcast, le_refl]

/-- The finite family of cell slices covers every hard point. -/
theorem hardProfilePoints_normalized_eq_iUnion_slices {g : ℕ → ℝ} {N : ℕ}
    (hN : 0 < N) :
    hardProfilePoints (normalizedProfileInterpolation g N) =
      ⋃ j : Fin N, ⋃ k : Fin N, hardProfileSlice g N j k := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := exists_normalized_profile_cell hN hx.1
    obtain ⟨k, hk⟩ := exists_normalized_profile_cell hN
      (show (1 + x) / 2 ∈ Icc (0 : ℝ) 1 from
        ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩)
    exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨k, hx, hj, hk⟩⟩
  · intro hx
    obtain ⟨j, k, hk⟩ := mem_iUnion.mp hx |>.imp fun _ h ↦ mem_iUnion.mp h
    exact hk.1

/-- Each hard-point slice is a closed interval, possibly empty. -/
theorem hardProfileSlice_eq_Icc {g : ℕ → ℝ} {N j k : ℕ}
    (hN : 0 < N) (hj : j < N) (hk : k < N) :
    ∃ a b : ℝ, hardProfileSlice g N j k = Icc a b := by
  by_cases hne : (hardProfileSlice g N j k).Nonempty
  · obtain ⟨a, ha⟩ := (isCompact_hardProfileSlice g N j k).exists_isLeast hne
    obtain ⟨b, hb⟩ := (isCompact_hardProfileSlice g N j k).exists_isGreatest hne
    refine ⟨a, b, subset_antisymm (fun x hx ↦ ⟨ha.2 hx, hb.2 hx⟩) ?_⟩
    exact (ordConnected_hardProfileSlice hN hj hk).out ha.1 hb.1
  · exact ⟨1, 0, by rw [not_nonempty_iff_eq_empty.mp hne]; norm_num⟩

/-- An interpolated profile has a hard-point set that is a finite union of closed intervals. -/
theorem hardProfilePoints_normalized_finite_intervals {g : ℕ → ℝ} {N : ℕ}
    (hN : 0 < N) :
    ∃ intervals : Finset (ℝ × ℝ),
      hardProfilePoints (normalizedProfileInterpolation g N) =
        ⋃ p ∈ intervals, Icc p.1 p.2 := by
  classical
  have hrepr : ∀ p : Fin N × Fin N,
      ∃ a b : ℝ, hardProfileSlice g N p.1 p.2 = Icc a b :=
    fun p ↦ hardProfileSlice_eq_Icc hN p.1.isLt p.2.isLt
  choose a b hab using hrepr
  refine ⟨Finset.univ.image (fun p : Fin N × Fin N ↦ (a p, b p)), ?_⟩
  rw [hardProfilePoints_normalized_eq_iUnion_slices hN]
  ext x
  simp only [mem_iUnion, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, k, hx⟩
    exact ⟨(a (j, k), b (j, k)), ⟨(j, k), rfl⟩, (hab (j, k)) ▸ hx⟩
  · rintro ⟨p, ⟨⟨j, k⟩, rfl⟩, hx⟩
    exact ⟨j, k, (hab (j, k)).symm ▸ hx⟩

end FalconerPacking
