/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import FalconerPacking.SeparatedDyadicData
public import FalconerPacking.RadialProjectionTheorem

/-!
# Actual compact data beyond the coherent cutoff

Outside the already proved coherent range, strict exponent extraction automatically puts
both exponents in the hard-gap range. The original Borel set then supplies bounded separated
Frostman probabilities, a rooted pin support, and the finite radial moment used in deletion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace FalconerPacking

/-- Strict exponents remain beyond the coherent range when the original set does. -/
theorem exists_strict_hardGap_exponents_of_not_coherent
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ}
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd' : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (hausdorffPackingBound d))
    (hnot : ¬packingDim E < ENNReal.ofReal (2 * d - 1)) :
    ∃ s u : ℝ, 1 < s ∧ s < d ∧ s ≤ 5 / 4 ∧ 2 * s - 1 ≤ u ∧
      ENNReal.ofReal s < dimH E ∧ packingDim E < ENNReal.ofReal u ∧
      u < hausdorffPackingBound s := by
  obtain ⟨s, u, hs, hsd, hsu, hs', hsdim, hpacku, hu⟩ :=
    exists_strict_exponents_of_hardGap_cutoff hdim hd hd' hpack
  have hdu : 2 * d - 1 < u :=
    ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mp ((le_of_not_gt hnot).trans_lt hpacku)
  exact ⟨s, u, hs, hsd, hs', by linarith, hsdim, hpacku, hu⟩

/-- All compact geometric and radial-moment data are constructed from the Borel hypothesis.
The common isometry records how a pin obtained in these coordinates returns to the set. -/
theorem exists_hardGap_borel_measure_data
    {E : Set (EuclideanSpace ℝ (Fin 2))} {d : ℝ} (hE : MeasurableSet E)
    (hdim : dimH E = ENNReal.ofReal d) (hd : 1 < d) (hd' : d ≤ 5 / 4)
    (hpack : packingDim E < ENNReal.ofReal (hausdorffPackingBound d))
    (hnot : ¬packingDim E < ENNReal.ofReal (2 * d - 1)) :
    ∃ (s u : ℝ) (X Y : Set (EuclideanSpace ℝ (Fin 2)))
      (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
      (f : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))
      (q₀ : Fin 2 → ℤ) (Cμ Cν δ R q : ℝ),
      1 < s ∧ s ≤ 5 / 4 ∧ 2 * s - 1 ≤ u ∧ u < hausdorffPackingBound s ∧
      IsCompact X ∧ IsCompact Y ∧ X ⊆ f '' E ∧ Y ⊆ f '' E ∧
      Y ⊆ dyadicCube 0 q₀ ∧ HasUpperBoxBound Y u ∧
      (μ : Measure (EuclideanSpace ℝ (Fin 2))) Xᶜ = 0 ∧
      (ν : Measure (EuclideanSpace ℝ (Fin 2))) Yᶜ = 0 ∧
      1 ≤ Cμ ∧ 1 ≤ Cν ∧
      IsFrostman (μ : Measure (EuclideanSpace ℝ (Fin 2))) s Cμ ∧
      IsFrostman (ν : Measure (EuclideanSpace ℝ (Fin 2))) s Cν ∧
      0 < δ ∧ 1 ≤ R ∧
      (∀ x ∈ X, ‖x‖ ≤ R) ∧ (∀ y ∈ Y, ‖y‖ ≤ R) ∧
      (∀ y ∈ Y, ∀ x ∈ X, δ ≤ (y - x) 0) ∧ 1 < q ∧
      (∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin 2))),
        (μ : Measure (EuclideanSpace ℝ (Fin 2))).map (radialAngle y) ≪ radialAngularMeasure) ∧
      (∫⁻ y, ∫⁻ θ,
        radialProjectionDensity (μ : Measure (EuclideanSpace ℝ (Fin 2))) y θ ^ q
          ∂radialAngularMeasure ∂(ν : Measure (EuclideanSpace ℝ (Fin 2)))) < ∞ := by
  obtain ⟨s, u, hs, _, hs', hsu, hsdim, hpacku, hu⟩ :=
    exists_strict_hardGap_exponents_of_not_coherent hdim hd hd' hpack hnot
  obtain ⟨K, L, μ, ν, Cμ, Cν, δ, hK, hL, hKE, hLE, _, hbox,
    hμK, hνL, hμ, hν, hδ, hsep⟩ :=
    exists_separated_frostman_probabilities_of_measurableSet hE hs
      (by linarith) hsdim hpacku
  obtain ⟨X, Y, μ', ν', f, q₀, Cμ', Cν', δ', R, hX, hY, hXK, hYL,
    hYroot, hYbox, hμX, hνY, hCμ, hCν, hμ', hν', hδ', hR, hXR, hYR, hgap⟩ :=
    exists_separated_dyadic_frostman_data μ ν hK hL hμK hνL hμ hν hbox hδ hsep
  obtain ⟨q, hq, _, hac, hmoment⟩ := exists_radialProjection_density_moment ν' μ' hs hs
    (by linarith) (by linarith) hμ' hν'
    ((ae_iff.mpr hμX).mono fun x hx ↦ hXR x hx)
    ((ae_iff.mpr hνY).mono fun y hy ↦ hYR y hy)
  exact ⟨s, u, X, Y, μ', ν', f, q₀, Cμ', Cν', δ', R, q, hs, hs', hsu, hu,
    hX, hY, hXK.trans (image_mono hKE), hYL.trans (image_mono hLE), hYroot, hYbox,
    hμX, hνY, hCμ, hCν, hμ', hν', hδ', hR, hXR, hYR, hgap, hq, hac, hmoment⟩

end FalconerPacking
