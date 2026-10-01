/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.RegularRetainedRemainder
import FalconerPacking.RegularShellParameters

/-!
# The full circle-chain coefficient for the actual regular-component thresholds

The geometric prefactor, finite conditional-energy estimate, and heavy threshold are
the same literal factors used by the proved retained-remainder theorem.
-/

noncomputable section

open Filter
open scoped ENNReal

namespace FalconerPacking

/-- The actual conditional-energy prefactor has the uniform upper bound required by the
finite-chain product theorem. Its dependence on the current profile depth is retained. -/
theorem regular_threshold_upper_bound {G h D₂ c : ℝ} (hG : 0 ≤ G)
    (K T N a : ℕ) (ha : a ≤ N) :
    let L := (2 : ℝ) ^ (h * T * N)
    ENNReal.ofReal (G * L ^ (20 * K + 100)) *
        (4 * (a + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
          (3 * (N : ℝ) + 3 * T + T * c)) * (ENNReal.ofReal L) ^ D₂ ≤
      ENNReal.ofReal (max 1 (4 * G) * (N + 1)) *
        ENNReal.ofReal (L ^ (20 * K + 100)) *
        (2 : ℝ≥0∞) ^ ((D₂ * h) * T * N + 3 * N + 3 * T + T * c) := by
  dsimp only
  have hcount : ENNReal.ofReal G * 4 * (a + 1 : ℝ≥0∞) ≤
      ENNReal.ofReal (max 1 (4 * G) * (N + 1)) := by
    have hc : G * 4 * ((a : ℝ) + 1) ≤ max 1 (4 * G) * ((N : ℝ) + 1) := by
      have ha' : (a : ℝ) ≤ N := by exact_mod_cast ha
      calc
        _ ≤ (4 * G) * ((N : ℝ) + 1) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    have hh := ENNReal.ofReal_le_ofReal hc
    simpa only [ENNReal.ofReal_mul hG, ENNReal.ofReal_mul (by positivity : 0 ≤ G * 4),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_add (Nat.cast_nonneg a) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using hh
  rw [ENNReal.ofReal_mul hG]
  have hinflate : (ENNReal.ofReal ((2 : ℝ) ^ (h * T * N))) ^ D₂ =
      (2 : ℝ≥0∞) ^ ((D₂ * h) * T * N) := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [hinflate]
  calc
    _ = (ENNReal.ofReal G * 4 * (a + 1 : ℝ≥0∞)) *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (20 * K + 100)) *
        ((2 : ℝ≥0∞) ^ ((D₂ * h) * T * N) *
          (2 : ℝ≥0∞) ^ (3 * (N : ℝ) + 3 * T + T * c)) := by ring
    _ ≤ _ := by
      rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
      have he : (D₂ * h) * (T : ℝ) * N + (3 * N + 3 * T + T * c) =
          (D₂ * h) * T * N + 3 * N + 3 * T + T * c := by ring
      rw [he]
      exact mul_le_mul_left (mul_le_mul_left hcount _) _

/-- The actual regular thresholds give the full strict circle-chain coefficient on every
sufficiently large shell. There is no assumed threshold bound or global energy bound. -/
theorem eventually_regular_chain_coefficient_le
    {C G D₂ s η ζ : ℝ} (hC : 0 < C) (hG : 0 < G) (hD₂ : 0 ≤ D₂)
    (hη : 0 < η) (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1)
    {J T : ℕ} (hJ : 0 < J) (hT : 0 < T) (K pwr : ℕ)
    (hloss : (K : ℝ) * ((28 * K + 114) * (1 / (4 * J)) +
        D₂ * (1 / (4 * J))) * T + 3 * K ≤ η * T / 4)
    (horder : 2 + (1 / (4 * (J : ℝ))) * ((4 * K + 8 : ℕ) - (pwr : ℝ)) < 0) :
    ∀ᶠ k : ℕ in atTop, ∀ (er : ℕ → ℕ) (l : List ℕ),
      let N := 4 * J * k
      let n₀ := Nat.floor ((1 - ζ) * N)
      let g := regularBlockProfile T N er
      l.length ≤ K → List.IsChain (fun n m ↦ m < n) (n₀ :: l) → chainEnd n₀ l = 0 →
      chainCost g n₀ l ≤ (s - 1 - η) * N →
      let ℓ := profileChainDepth n₀ l
      let d := fun j ↦ T * ℓ j
      let L := ((2 : ℝ) ^ k) ^ T
      let H := fun j ↦ ENNReal.ofReal (G * L ^ (20 * K + 100)) *
        (4 * (ℓ j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
          (3 * (N : ℝ) + 3 * T + T * edgeCost g (ℓ (j + 1)) (ℓ j))) *
        (ENNReal.ofReal L) ^ D₂
      let A := fun j ↦ ENNReal.ofReal C * ENNReal.ofReal (L ^ (8 * j + 14)) * H j
      (∏ j ∈ Finset.range K, A j) * ENNReal.ofReal (49 * ((2 : ℝ) ^ d K) ^ 2) +
        (∑ j ∈ Finset.range K, (∏ i ∈ Finset.range j, A i) *
          (ENNReal.ofReal C * ENNReal.ofReal ((((2 : ℝ) ^ d j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
            ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))) ≤
          50 * (2 : ℝ≥0∞) ^ ((s - 1 - η / 2) * T * N) := by
  let h : ℝ := 1 / (4 * J)
  have hh : 0 ≤ h := by dsimp [h]; positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_padded_chain_coefficient_le
    (s := s) (le_max_left 1 C) (le_max_left 1 (4 * G)) hh (mul_nonneg hD₂ hh)
    hη K pwr hT hloss horder)
  filter_upwards [eventually_ge_atTop N₀,
    eventually_regular_threshold_ge_one hG hD₂ hT K] with k hk hHlower
  intro er l
  dsimp only
  intro hlen hl hend hcost
  let N := 4 * J * k
  let n₀ := Nat.floor ((1 - ζ) * N)
  have hn₀ : n₀ ≤ N := (initial_profile_depth_bounds hζ hζ₁ N T).2.1
  have hℓ : Antitone (profileChainDepth n₀ l) := antitone_profileChainDepth hl
  have hL : ((2 : ℝ) ^ k) ^ T = (2 : ℝ) ^ (h * T * N) := by
    rw [← pow_mul, Nat.mul_comm k T, annular_enlargement_eq hJ]
  let H := fun j ↦ ENNReal.ofReal (G * (((2 : ℝ) ^ k) ^ T) ^ (20 * K + 100)) *
    (4 * (profileChainDepth n₀ l j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
      (3 * (N : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T N er)
        (profileChainDepth n₀ l (j + 1)) (profileChainDepth n₀ l j))) *
    (ENNReal.ofReal (((2 : ℝ) ^ k) ^ T)) ^ D₂
  have hlow (j : ℕ) (_hj : j < K) : 1 ≤ H j := by
    exact hHlower _ (regular_profile_energy_one_le_and_ne_top hT er
      (hℓ (Nat.le_succ j))).1
  have hupp (j : ℕ) (_hj : j < K) : H j ≤
      ENNReal.ofReal (max 1 (4 * G) * (N + 1)) *
        ENNReal.ofReal (((2 : ℝ) ^ (h * T * N)) ^ (20 * K + 100)) *
        (2 : ℝ≥0∞) ^ ((D₂ * h) * T * N + 3 * N + 3 * T + T *
          edgeCost (regularBlockProfile T N er)
            (profileChainDepth n₀ l (j + 1)) (profileChainDepth n₀ l j)) := by
    dsimp only [H]
    rw [hL]
    exact regular_threshold_upper_bound hG.le K T N _
      ((profileChainDepth_le_initial hl j).trans hn₀)
  have hkN : N₀ ≤ N := hk.trans (Nat.le_mul_of_pos_left k (by omega : 0 < 4 * J))
  have hb := hN₀ N hkN n₀ (regularBlockProfile T N er) l hn₀ hlen hl hend hcost H hlow hupp
  have hb' := hb
  simp only [← hL] at hb'
  apply le_trans ?_ hb'
  dsimp only [H]
  gcongr <;> exact le_max_right 1 C

/-- Canonical auxiliary labels use the upper edge of the full annulus, while their
standard-cap comparison uses its lower frequency. Every geometric premise of the actual
circle-chain theorem is discharged, including padded edges after the list has ended. -/
theorem regular_packet_circle_chain_scales {J T k n : ℕ} (hn : n ≤ 4 * J * k)
    {l : List ℕ}
    (hl : List.IsChain (fun n m ↦ m < n ∧ Admissible (4 * J * k) m n) (n :: l))
    (hend : chainEnd n l = 0) :
    let N := 4 * J * k
    let F := T * N + 4 * (J * T) + 2
    let d := fun j ↦ T * profileChainDepth n l j
    let e := blockProfileChainAngle F T n l
    let s := 6 + 2 * (J * T) * k
    let U := (2 : ℝ) ^ (4 * (J * T) + 2) * 2 ^ (4 * (J * T) * k)
    Antitone d ∧ Monotone e ∧ e 0 = 0 ∧ (∀ j, e j ≤ F) ∧
      ∀ j : ℕ,
        let a := ((2 : ℝ) ^ d j)⁻¹
        let b := ((2 : ℝ) ^ d (j + 1))⁻¹
        b ≤ U * a ^ 2 ∧ U * a ≤ (2 : ℝ) ^ e (j + 1) ∧
          (2 : ℝ) ^ e (j + 1) ≤ 2 * (U * a) ∧
          ((2 : ℝ) ^ s)⁻¹ ≤ a / b := by
  dsimp only
  let N := 4 * J * k
  let F := T * N + 4 * (J * T) + 2
  let s := 6 + 2 * (J * T) * k
  have hNF : T * N ≤ F := by dsimp [F]; omega
  have hs : Real.sqrt ((2 : ℝ) ^ (T * N)) ≤ (2 : ℝ) ^ s := by
    have h := (standard_fourfold_angular_grid_bounds (J * T) k).2.1
    rw [annular_profile_depth_eq] at h
    convert h using 1
    dsimp [s]
    rw [pow_add]
    norm_num
  have hU : (2 : ℝ) ^ F = (2 : ℝ) ^ (4 * (J * T) + 2) *
      2 ^ (4 * (J * T) * k) := by
    dsimp [F, N]
    rw [show T * (4 * J * k) + 4 * (J * T) + 2 =
      (4 * (J * T) + 2) + 4 * (J * T) * k by ring, pow_add]
  obtain ⟨hd, he, _, _, he₀, hbound, _⟩ := blockProfileChain_scales hNF hn hl hend hs
  refine ⟨hd, he, he₀, fun j ↦ (hbound j).2, fun j ↦ ?_⟩
  obtain ⟨_, _, _, hcurv, heq, hframe⟩ :=
    blockProfileChain_scales_all_edges hNF hn hl hend hs j
  rw [hU] at hcurv heq
  refine ⟨hcurv, heq.ge, ?_, hframe⟩
  rw [heq]
  exact le_mul_of_one_le_left (by positivity) (by norm_num)

end FalconerPacking
