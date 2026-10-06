/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RetainedScalarEnergy
public import FalconerPacking.RegularChainCoefficient

/-!
# Actual good-distance energy on every regularized shell

The literal retained packet family, with the same inherited thresholds as the bad-part
estimate, has geometrically decaying joint squared norm. Every annulus is included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Classical SchwartzMap FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Uniform good-density decay for every actual regular-component chain. All analytic,
threshold, Fourier-tail and padded-chain estimates are discharged by their constructions. -/
theorem exists_regular_retained_distance_energy_decay
    (χ : SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ) (hχ : HasCompactSupport χ)
    (hχone : ∀ x, |χ x| ≤ 1)
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    {M : ℝ} (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ M) {δ : ℝ} (hδ : 0 < δ)
    (hnear : ∀ᵐ z ∂μ, ∀ x, ‖x - z‖ < δ → χ x = 1)
    {B s C₀ η ζ G D₂ : ℝ} (hB : 0 ≤ B)
    (hs : 0 ≤ s) (hs₂ : s ≤ 2) (hfr : IsFrostman μ s C₀)
    (hη : 0 < η) (hζ : 0 ≤ ζ) (hζ₁ : ζ ≤ 1) (hG : 0 < G) (hD₂ : 0 ≤ D₂)
    {J T : ℕ} (hJ : 0 < J) (hT : 0 < T) (K pwr m q : ℕ)
    (hloss : (K : ℝ) * ((28 * K + 114) * (1 / (4 * J)) +
        D₂ * (1 / (4 * J))) * T + 3 * K ≤ η * T / 4)
    (horder : 2 + (1 / (4 * (J : ℝ))) * ((4 * K + 8 : ℕ) - (pwr : ℝ)) < 0)
    (hmain : 4 * (1 / (4 * (J : ℝ))) + 2 * ζ - η / 2 ≤ -η / 8)
    (hloc : 3 - s - m * (2 * (1 / (4 * (J : ℝ))) + ζ) ≤ -1)
    (hrec : (8 * (J * T) : ℝ) - 2 * q ≤ -1) (hq : 1 ≤ q) :
    ∃ A α : ℝ, 0 < A ∧ 0 < α ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure σ]
        (er : ℕ → ℕ) (l : List ℕ) (I : Finset (Fin 2 → ℤ)),
      let N := 4 * J * k
      let n₀ := Nat.floor ((1 - ζ) * N)
      (∀ᵐ y ∂σ, ‖y‖ ≤ B) → l.length ≤ K →
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n₀ :: l) →
      chainEnd n₀ l = 0 →
      chainCost (regularBlockProfile T N er) n₀ l ≤ (s - 1 - η) * N →
      let ℓ := profileChainDepth n₀ l
      let d := fun j ↦ T * ℓ j
      let F := T * N + 4 * (J * T) + 2
      let e := blockProfileChainAngle F T n₀ l
      let std := 6 + 2 * (J * T) * k
      let x := (2 : ℝ) ^ k
      let L := x ^ T
      let w := x / x ^ (2 * (J * T))
      let profile := fun j ↦ 4 * (ℓ j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
        (3 * (N : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T N er) (ℓ (j + 1)) (ℓ j))
      let H := fun j ↦ ENNReal.ofReal (G * L ^ (20 * K + 100)) * profile j *
        (ENNReal.ofReal L) ^ D₂
      let ψ := 𝓕 (dyadicAnnularKernel (4 * (J * T)) k)
      let f := retainedPinSource μ hμ ψ
        (hasCompactSupport_fourier_dyadicAnnularKernel (4 * (J * T)) k)
        (fourier_dyadicAnnularKernel_eventually_zero (4 * (J * T)) k)
        χ hχ σ d e std F K L H I w
      (∫⁻ p, ‖complexDistanceDensity (f p.1) p.1 p.2‖ₑ ^ 2 ∂σ.prod volume) ≤
        ENNReal.ofReal A * (2 : ℝ≥0∞) ^ (-α * k) := by
  obtain ⟨C₁, C₂, C₃, C₅, C, hC₁, hC₂, hC₃, hC₅, hC, k₀, hfull⟩ :=
    exists_retainedChain_four_term_bound χ hχ hχone (Nat.mul_pos hJ hT) hB hδ
      q m pwr K μ hs hs₂ hfr
  obtain ⟨A, α, hA, hα, hrate⟩ := exists_retained_four_term_rate
    (C₁ := C₁) hη hζ hζ₁
    (show (1 : ℝ) ≤ 2 ^ (4 * (J * T) + 2) from one_le_pow₀ (by norm_num))
    hC₂.le hC₅.le (zero_le_one.trans hC) hJ hT hmain hloc hrec hq
  have hcoeff := eventually_regular_chain_coefficient_le
    (s := s) hC₃ hG hD₂ hη hζ hζ₁ hJ hT K pwr hloss horder
  refine ⟨A, α, hA, hα, ?_⟩
  filter_upwards [hcoeff, eventually_ge_atTop k₀, eventually_ge_atTop 9] with k hck hk hk₉
  intro σ _ er l I
  dsimp only
  intro hball hlen hl hend hcost
  let N := 4 * J * k
  let n₀ := Nat.floor ((1 - ζ) * N)
  let ℓ := profileChainDepth n₀ l
  let d := fun j ↦ T * ℓ j
  let F := T * N + 4 * (J * T) + 2
  let e := blockProfileChainAngle F T n₀ l
  let L := ((2 : ℝ) ^ k) ^ T
  let H := fun j ↦ ENNReal.ofReal (G * L ^ (20 * K + 100)) *
    (4 * (ℓ j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
      (3 * (N : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T N er) (ℓ (j + 1)) (ℓ j))) *
    (ENNReal.ofReal L) ^ D₂
  have hn₀ : n₀ ≤ N := (initial_profile_depth_bounds hζ hζ₁ N T).2.1
  obtain ⟨hd, he, he₀, heF, hscales⟩ := regular_packet_circle_chain_scales hn₀ hl hend
  have hLlarge : 346 ≤ L := by
    have hx : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hb : (346 : ℝ) ≤ 2 ^ k := le_trans (by norm_num : (346 : ℝ) ≤ 2 ^ 9)
      (pow_le_pow_right₀ (by norm_num) hk₉)
    exact hb.trans (by simpa only [pow_one, L] using pow_le_pow_right₀ hx (by omega : 1 ≤ T))
  have hf := hfull M hμ hnear σ hball k hk d e hd he he₀ F (heF K) L hLlarge H I
    (fun j _ ↦ (hscales j).1) (fun j _ ↦ (hscales j).2.1)
    (fun j _ ↦ (hscales j).2.2.1) (fun j _ _ ↦ (hscales j).2.2.2)
  dsimp only at hf
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at hf
  have hl' : List.IsChain (fun n m ↦ m < n) (n₀ :: l) := hl.imp (fun _ _ h ↦ h.1)
  have hE := hck er l hlen hl' hend hcost
  let E := (∏ j ∈ Finset.range K, ENNReal.ofReal C₃ * ENNReal.ofReal (L ^ (8 * j + 14)) * H j) *
    ENNReal.ofReal (49 * ((2 : ℝ) ^ d K) ^ 2) +
    ∑ j ∈ Finset.range K,
      (∏ i ∈ Finset.range j, ENNReal.ofReal C₃ * ENNReal.ofReal (L ^ (8 * i + 14)) * H i) *
      (ENNReal.ofReal C₃ * ENNReal.ofReal ((((2 : ℝ) ^ d j)⁻¹ ^ 2)⁻¹ * (L ^ pwr)⁻¹) *
        ENNReal.ofReal (49 * (L ^ (2 * (j + 1) + 2)) ^ 2))
  have hL : L = (2 : ℝ) ^ ((1 / (4 * (J : ℝ))) * T * N) := by
    dsimp [L, N]
    rw [← pow_mul, Nat.mul_comm k T, annular_enlargement_eq hJ]
  have hr := hrate k E (by rw [← hL]; linarith) hE
  apply (show _ ≤ _ from hf).trans
  simpa only [d, ℓ, profileChainDepth_zero, N, n₀,
    annular_profile_depth_eq, ← hL] using hr

end FalconerPacking
