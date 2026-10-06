/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.RegularRetainedRemainder
public import FalconerPacking.RegularRetainedEnergy
public import FalconerPacking.RegularShellParameters
public import FalconerPacking.ComponentAnnularCriterion
public import FalconerPacking.DyadicPositiveCubes
public import FalconerPacking.RegularDiscardedPins

/-!
# Compact regular components and actual annular density convergence

The strict profile parameters are chosen before regularization. Each actual regular pin
component supplies its own admissible chain and positive initial cubes. The same threshold
and retained source occur in the good estimate and in the exact annular remainder.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped ENNReal

namespace FalconerPacking

/-- Compact separated Frostman probabilities satisfy the hard-gap pinned-distance conclusion.
Every annular component and retained source is constructed from the original measures. -/
theorem pinnedDistance_absolutelyContinuous_of_compact_regular_shells
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    {X Y : Set (EuclideanSpace ℝ (Fin 2))} {q₀ : Fin 2 → ℤ}
    {s u Cμ Cν δ R q : ℝ}
    (hs : 1 < s) (hs' : s ≤ 5 / 4) (hu : 2 * s - 1 ≤ u)
    (hu' : u < hausdorffPackingBound s)
    (hX : IsCompact X) (hY : IsCompact Y)
    (hroot : Y ⊆ dyadicCube 0 q₀) (hbox : HasUpperBoxBound Y u)
    (hμX : (μ : Measure (EuclideanSpace ℝ (Fin 2))) Xᶜ = 0)
    (hνY : (ν : Measure (EuclideanSpace ℝ (Fin 2))) Yᶜ = 0)
    (_hCμ : 1 ≤ Cμ) (hCν : 1 ≤ Cν)
    (hfrμ : IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ)
    (hfrν : IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) s Cν)
    (hδ : 0 < δ) (hR : 1 ≤ R)
    (hXR : ∀ x ∈ X, ‖x‖ ≤ R) (hYR : ∀ y ∈ Y, ‖y‖ ≤ R)
    (hsep : ∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0)
    (hq : 1 < q)
    (hac : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))),
      (μ : Measure (EuclideanSpace ℝ (Fin 2))).map (radialAngle y) ≪
        radialAngularMeasure)
    (hmoment : (∫⁻ y, ∫⁻ θ,
      radialProjectionDensity (μ : Measure (EuclideanSpace ℝ (Fin 2))) y θ ^ q
        ∂radialAngularMeasure ∂(ν : Measure (EuclideanSpace ℝ (Fin 2)))) < ∞) :
    jointPinnedDistanceMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2)))
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) ≪
        (ν : Measure (EuclideanSpace ℝ (Fin 2))).prod volume ∧
      ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))),
        pinnedDistanceMeasure (μ : Measure (EuclideanSpace ℝ (Fin 2))) y ≪ volume := by
  classical
  have hμ : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))), ‖x‖ ≤ R :=
    (ae_iff.mpr hμX).mono fun x hx ↦ hXR x hx
  have hν : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))), ‖y‖ ≤ R :=
    (ae_iff.mpr hνY).mono fun y hy ↦ hYR y hy
  obtain ⟨η, ζ, ε, hη, hζ, hζ₄, hζloss, hε, K, hK, hpartition⟩ :=
    exists_compact_regular_partition_with_initial_loss hs hs' hu hu'
      (show (0 : ℝ) ≤ 2 by norm_num) (by linarith : 0 ≤ Cν) hfrν
      hY hνY hroot hbox
  obtain ⟨J, D₁, D₂, h, ρ, T₀, hJ, hhdef, hD₁, hD₂, hh, hhsmall, hρ,
    hρε, hρη, hρh, hhη, hbad₁, hbad₂, hnorm₁, hnorm₂, hT₀, hchainloss, hfinalloss⟩ :=
    exists_regular_shell_parameters hη hq hε K
  obtain ⟨θ, hθ, hθρ, T, N₀, hT₀T, hT, hN₀, hparts⟩ :=
    hpartition ρ hρ hρε T₀
  let χ := sourceBallCutoff (R + 1) (by linarith : 0 < R + 1)
  have hχ : HasCompactSupport χ := hasCompactSupport_sourceBallCutoff _ _
  have hχnorm : ∀ x, |χ x| ≤ 1 := abs_sourceBallCutoff_le_one _ _
  have hmark₁ : (4 * K + 9 : ℝ) - (q - 1) * D₁ ≤ -1 := by
    have : 0 ≤ (28 * K + 114 : ℝ) * ρ / h := by positivity
    linarith [Nat.cast_nonneg (α := ℝ) K]
  have hmark₂ : (4 * K + 9 : ℝ) + D₁ - D₂ ≤ -1 := by
    have : 0 ≤ (28 * K + 114 : ℝ) * ρ / h := by positivity
    linarith [Nat.cast_nonneg (α := ℝ) K]
  obtain ⟨G, B, C, hG, hB, hC, hremainder⟩ :=
    exists_regular_retained_remainder_decay (by omega : 0 < J) (by omega : 0 < T)
      K hζ.le hζ₄.le hq.le hD₂.le hmark₁ hmark₂
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) (by linarith : 0 < R) hδ hμ
      χ hχ hχnorm hX.measurableSet hY.measurableSet hμX hXR hYR hsep

  let χC := χ.postcompCLM Complex.ofRealCLM
  have hχC : HasCompactSupport χC := hasCompactSupport_complex_source_cutoff χ hχ
  have hχCone : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))), χC x = 1 := by
    filter_upwards [hμ] with x hx
    have hx' : x ∈ Metric.closedBall 0 (R + 1) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖x‖ ≤ R + 1 by linarith)
    have h := sourceBallCutoff_eq_one (R + 1) (by linarith) hx'
    simpa [χC, χ] using congrArg Complex.ofReal h
  have hχCnorm : ∀ x, ‖χC x‖ ≤ 1 := by
    intro x
    simpa [χC] using hχnorm x
  have hχradius : ∀ x ∈ Function.support χC, ‖x‖ ≤ 2 * (R + 1) := by
    intro x hx
    have hx' : x ∈ Function.support χ := by
      intro hz
      apply hx
      change (χ x : ℂ) = 0
      simp [hz]
    rw [show Function.support χ = Metric.ball 0 (2 * (R + 1)) from
      support_sourceBallCutoff _ _] at hx'
    have hxnorm : ‖x‖ < 2 * (R + 1) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hx'
    exact hxnorm.le
  have hdist : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))),
      ∀ x ∈ Function.support χC, dist x y ≤ 2 * (R + 1) + R := by
    filter_upwards [hν] with y hy
    intro x hx
    rw [dist_eq_norm]
    exact (norm_sub_le x y).trans (add_le_add (hχradius x hx) hy)
  have hlarge : ∀ᶠ k : ℕ in atTop, N₀ ≤ 4 * J * k := by
    filter_upwards [eventually_ge_atTop N₀] with k hk
    exact hk.trans (Nat.le_mul_of_pos_left k (by omega))
  have hcomponentY (n : ℕ) (A : Finset (Fin 2 → ℤ)) :
      normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2)))
        (finiteDyadicUnion n A) Yᶜ = 0 := by
    exact ae_iff.mp (ae_normalizedRestrict_of_ae
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) (finiteDyadicUnion n A) (ae_iff.mpr hνY))
  have hcomponentAC (n : ℕ) (A : Finset (Fin 2 → ℤ)) :
      ∀ᵐ y ∂normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2)))
        (finiteDyadicUnion n A),
      (μ : Measure (EuclideanSpace ℝ (Fin 2))).map (radialAngle y) ≪
        radialAngularMeasure :=
    ae_normalizedRestrict_of_ae (ν : Measure (EuclideanSpace ℝ (Fin 2))) _ hac
  have hinitial (n m : ℕ) (A : Finset (Fin 2 → ℤ)) :
      ∃ I : Finset (Fin 2 → ℤ),
        (∀ Q ∈ I, 0 < normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2)))
          (finiteDyadicUnion n A) (dyadicCube m Q)) ∧
        normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2)))
          (finiteDyadicUnion n A) (finiteDyadicUnion m I)ᶜ = 0 := by
    obtain ⟨c, I, hc, hI, hcard, hae⟩ := exists_positive_mass_cube_family
      (normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2)))
        (finiteDyadicUnion n A)) (hcomponentY n A) hbox
    refine ⟨I m, fun Q hQ ↦ (hI m Q).mp hQ, ?_⟩
    exact ae_iff.mp ((hae m).mono fun y hy ↦ mem_finiteDyadicUnion_iff.mpr hy)

  let density (k : ℕ) (σ : Measure (EuclideanSpace ℝ (Fin 2)))
      (er : ℕ → ℕ) (l : List ℕ) (I : Finset (Fin 2 → ℤ))
      (p : EuclideanSpace ℝ (Fin 2) × ℝ) : ℂ :=
    let N := 4 * J * k
    let n₀ := Nat.floor ((1 - ζ) * N)
    let ℓ := profileChainDepth n₀ l
    let d := fun j ↦ T * ℓ j
    let F := T * N + 4 * (J * T) + 2
    let e := blockProfileChainAngle F T n₀ l
    let s := 6 + 2 * (J * T) * k
    let x := (2 : ℝ) ^ k
    let L := x ^ T
    let w := x / x ^ (2 * (J * T))
    let profile := fun j ↦ 4 * (ℓ j + 1 : ℝ≥0∞) * (2 : ℝ≥0∞) ^
      (3 * (N : ℝ) + 3 * T + T * edgeCost (regularBlockProfile T N er) (ℓ (j + 1)) (ℓ j))
    let H := fun j ↦ ENNReal.ofReal (G * L ^ (20 * K + 100)) * profile j *
      (ENNReal.ofReal L) ^ D₂
    let ψ := 𝓕 (dyadicAnnularKernel (4 * (J * T)) k)
    complexDistanceDensity (retainedPinSource
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) hμ ψ
      (hasCompactSupport_fourier_dyadicAnnularKernel (4 * (J * T)) k)
      (fourier_dyadicAnnularKernel_eventually_zero (4 * (J * T)) k)
      χ hχ σ d e s F K L H I w p.1) p.1 p.2
  have hdensity (k : ℕ) (σ : Measure (EuclideanSpace ℝ (Fin 2)))
      (er : ℕ → ℕ) (l : List ℕ) (I : Finset (Fin 2 → ℤ)) :
      Measurable (density k σ er l I) :=
    measurable_retainedPinDistanceDensity _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  suffices hgood : ∃ A α : ℝ, 0 < A ∧ 0 < α ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (σ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure σ]
        (er : ℕ → ℕ) (l : List ℕ) (I : Finset (Fin 2 → ℤ)),
      let N := 4 * J * k
      let n₀ := Nat.floor ((1 - ζ) * N)
      (∀ᵐ y ∂σ, ‖y‖ ≤ R) → (∀ j < N, er j ≤ 2 * T) → l.length ≤ K →
      List.IsChain (fun n m ↦ m < n ∧ Admissible N m n) (n₀ :: l) →
      chainEnd n₀ l = 0 →
      chainCost (regularBlockProfile T N er) n₀ l ≤ (s - 1 - η) * N →
      (∫⁻ p, ‖density k σ er l I p‖ₑ ^ 2 ∂σ.prod volume) ≤
        ENNReal.ofReal A * (2 : ℝ≥0∞) ^ (-α * k) by
    obtain ⟨Cgood, α, hCgood, hα, hgood⟩ := hgood
    apply pinnedDistance_absolutelyContinuous_of_eventual_component_decay
      (ι := Finset (Fin 2 → ℤ))
      (μ : Measure (EuclideanSpace ℝ (Fin 2)))
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) hμ χC hχC hχCone hχCnorm
      (show 0 < 4 * (J * T) by positivity) hdist
      (fun y ↦ ∫⁻ θ, radialProjectionDensity
        (μ : Measure (EuclideanSpace ℝ (Fin 2))) y θ ^ q ∂radialAngularMeasure)
      hmoment.ne (A := ENNReal.ofReal Cgood) (B := ENNReal.ofReal B)
      (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top hα (b := 4 * (J * T : ℕ) * θ) (by positivity)
    filter_upwards [hremainder, hgood, hlarge] with k hbadk hgoodk hk
    let N := 4 * J * k
    let n₀ := Nat.floor ((1 - ζ) * N)
    let U := finiteDyadicUnion (T * N)
    obtain ⟨F, hdis, hF, hrem, hcard⟩ := hparts N n₀ hk
      (Nat.floor_le (mul_nonneg (by linarith : 0 ≤ 1 - ζ) (Nat.cast_nonneg N)))
    have hex (A : Finset (Fin 2 → ℤ)) (hAF : A ∈ F) :
        ∃ g : EuclideanSpace ℝ (Fin 2) × ℝ → ℂ, Measurable g ∧
          (∫⁻ p, ‖g p‖ₑ ^ 2 ∂(normalizedRestrict
              (ν : Measure (EuclideanSpace ℝ (Fin 2))) (U A)).prod volume) ≤
            ENNReal.ofReal Cgood * (2 : ℝ≥0∞) ^ (-α * k) ∧
          (∫⁻ p, ‖complexDistanceDensity
              (compactAnnularSource (μ : Measure (EuclideanSpace ℝ (Fin 2))) hμ χC hχC
                (4 * (J * T)) (k + 1)) p.1 p.2 - g p‖ₑ
            ∂(normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2))) (U A)).prod volume) ≤
            (ENNReal.ofReal B * (∫⁻ y, ∫⁻ θ,
              radialProjectionDensity (μ : Measure (EuclideanSpace ℝ (Fin 2))) y θ ^ q
                ∂radialAngularMeasure
                  ∂normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2))) (U A)) +
              ENNReal.ofReal C) * (2 : ℝ≥0∞) ^ (-(k : ℝ)) := by
      obtain ⟨hmass, hprob, hrootA, er, he, hreg, l, hlen, hl, hend, hcost⟩ := hF A hAF
      let σ := normalizedRestrict (ν : Measure (EuclideanSpace ℝ (Fin 2))) (U A)
      letI : IsProbabilityMeasure σ := hprob
      have hσR : ∀ᵐ y ∂σ, ‖y‖ ≤ R :=
        ae_normalizedRestrict_of_ae (ν : Measure (EuclideanSpace ℝ (Fin 2))) (U A) hν
      obtain ⟨I, hI, hcover⟩ := hinitial (T * N) (T * n₀) A
      have hmass₀ : (ν : Measure (EuclideanSpace ℝ (Fin 2))) (U A) ≠ 0 := by
        intro hz
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(ρ * T * N)) := by positivity
        simpa [MeasureTheory.measureReal_def, U, hz] using hpos.trans_le hmass
      refine ⟨density k σ er l I, hdensity _ _ _ _ _,
        hgoodk σ er l I hσR he hlen hl hend hcost, ?_⟩
      have hbound := hbadk (ν : Measure (EuclideanSpace ℝ (Fin 2))) A er
        hmass₀ he hreg (fun a ha a' ha' ↦ (hrootA a ha).trans (hrootA a' ha').symm)
        l hlen hl hend I (T * N + 4 * (J * T) + 2) (by dsimp [N]; omega)
        (hcomponentY (T * N) A) (hcomponentAC (T * N) A) hI hcover
      have hfull := measurable_joint_complexDistanceDensity
        (compactAnnularSource (μ : Measure (EuclideanSpace ℝ (Fin 2))) hμ χC hχC
          (4 * (J * T)) (k + 1)).continuous.measurable
      calc
        _ = ∫⁻ y, ∫⁻ r, ‖complexDistanceDensity
              (compactAnnularSource (μ : Measure (EuclideanSpace ℝ (Fin 2))) hμ χC hχC
                (4 * (J * T)) (k + 1)) y r - density k σ er l I (y, r)‖ₑ
              ∂volume ∂σ :=
          lintegral_prod _ (hfull.sub (hdensity k σ er l I)).enorm.aemeasurable
        _ ≤ _ := hbound
    choose! g hg hgg hgb using hex
    refine ⟨F, U, g, fun A _ ↦ measurableSet_finiteDyadicUnion _ _, hg, hdis, hgg, hgb, ?_⟩
    simpa only [U, N, Nat.cast_mul] using regular_partition_discarded_mass_le
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) F J T k θ hrem

  obtain ⟨pwr, m, tail, _, _, htail, _, _, horder, _, hloc, hrec⟩ :=
    exists_regular_shell_decay_orders (ρ := ρ) (A := 28 * K + 114)
      (D₂ := D₂) (P := 0) hh K J T 0 0 1
  have hnear : ∀ᵐ z ∂(μ : Measure (EuclideanSpace ℝ (Fin 2))),
      ∀ x, ‖x - z‖ < 1 → χ x = 1 :=
    sourceBallCutoff_one_near_measure _ (by linarith) hμ
  have hloss := hchainloss T hT₀T
  have hmain : 4 * h + 2 * ζ - η / 2 ≤ -η / 8 := by
    linarith [hfinalloss ζ hζloss]
  have hlocal := hloc s ζ hs.le hζ.le
  rw [hhdef] at hloss horder hmain hlocal
  obtain ⟨A, α, hA, hα, hactual⟩ := exists_regular_retained_distance_energy_decay
    χ hχ hχnorm (μ : Measure (EuclideanSpace ℝ (Fin 2))) hμ
    (show (0 : ℝ) < 1 by norm_num) hnear (by linarith : 0 ≤ R)
    (by linarith : 0 ≤ s) (by linarith : s ≤ 2) hfrμ hη hζ.le
    (by linarith : ζ ≤ 1) hG hD₂.le (by omega : 0 < J) (by omega : 0 < T)
    K pwr m tail hloss horder hmain hlocal hrec htail
  refine ⟨A, α, hA, hα, ?_⟩
  filter_upwards [hactual] with k hk
  intro σ _ er l I
  dsimp only
  intro hσ _he hlen hl hend hcost
  exact hk σ er l I hσ hlen hl hend hcost

end FalconerPacking
