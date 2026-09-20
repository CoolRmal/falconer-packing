/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
import FalconerPacking.PinnedL2
import FalconerPacking.FrostmanLimit
import FalconerPacking.Extraction
import FalconerPacking.Restriction

/-!
# The reduction to a single analytic hypothesis

`PinnedL2.lean` turns an averaged hyperbolic-tube bound into a pin with a positive-length pinned
distance set.  This file supplies the measures that bound is about, so that the whole route runs
from a dimension hypothesis on a compact set to the conclusion of Theorem 1.1, with exactly one
analytic input left.

That input is `HypTubeBound d`: for a separated pair of `d`-Frostman probability measures, the
`μ × μ`-mass of the pairs whose distances to the pin differ by less than `δ`, averaged over the
pin measure `ν`, is `O(δ)` at some sequence of scales tending to zero.

`exists_pin_of_hypTubeBound` then reads: a compact planar set of Hausdorff dimension above `d`
carries a pin whose pinned distance set has positive length.  The chain is

* Frostman's lemma on the compact set (`FrostmanLimit.lean`);
* the separation step, splitting it into two compact pieces of positive mass at positive
  distance (`Extraction.lean`);
* normalized restrictions, which keep the Frostman exponent (`Restriction.lean`);
* the hypothesis, applied to that pair;
* Fatou over the pins and the `L²` criterion (`PinnedL2.lean`);
* monotonicity of the pinned distance set in the source.

Every step but the hypothesis is proved here.  Both analytic branches of Theorem 1.1 assert
something of this shape, so `HypTubeBound` is a single concrete replacement for the two of them
— concrete in the sense that it is an inequality between explicit integrals, with no reference
to projections, packets, or profiles.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FalconerPacking

/-- **The averaged hyperbolic-tube estimate**, as an explicit analytic hypothesis: for a
separated pair of `d`-Frostman probability measures, the mass of the hyperbolic tube around the
pin, averaged over the pin measure, is `O(δ)` at some sequence of scales tending to zero.

This is the single analytic input that the whole `L²` route needs.  Everything downstream of it
— Fatou over the pins, the overlap identity, Cauchy–Schwarz, absolute continuity, positive
length, and the Borel reduction — is proved unconditionally in this development. -/
def HypTubeBound (d : ℝ) : Prop :=
  ∀ (μ ν : Measure Plane) (Cμ Cν sep : ℝ),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    IsFrostman μ d Cμ → IsFrostman ν d Cν →
    0 < sep → (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, sep ≤ dist x y) →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n, (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ n)) ∂ν) ≤ ENNReal.ofReal (2 * δ n) * C

theorem normalizedRestrict_compl_eq_zero (σ : Measure Plane) {Q : Set Plane}
    (hQ : MeasurableSet Q) : normalizedRestrict σ Q Qᶜ = 0 := by
  rw [normalizedRestrict_apply σ Q _ hQ.compl, Set.compl_inter_self, measure_empty, mul_zero]

theorem normalizedRestrict_self (σ : Measure Plane) {Q : Set Plane} (hQ : MeasurableSet Q)
    (h0 : σ Q ≠ 0) (hfin : σ Q ≠ ⊤) : normalizedRestrict σ Q Q = 1 := by
  rw [normalizedRestrict_apply σ Q _ hQ, Set.inter_self, ENNReal.inv_mul_cancel h0 hfin]

/-- **The Borel reduction and the endpoint, in one step.**  A compact planar set whose Hausdorff
dimension exceeds `d` carries a separated pair of `d`-Frostman probability measures, and the
hyperbolic-tube estimate for that pair produces a pin inside the set whose pinned distance set
has positive length. -/
theorem exists_pin_of_hypTubeBound {K E : Set Plane} (hK : IsCompact K) (hKE : K ⊆ E)
    {d : ℝ} (hd : 0 < d) (hdim : ENNReal.ofReal d < dimH K) (hbound : HypTubeBound d) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  obtain ⟨θ, C, hθK, hθfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH hK hd hdim
  set σ : Measure Plane := (θ : Measure Plane) with hσ
  haveI hσprob : IsProbabilityMeasure σ := θ.2
  have hσKc : σ Kᶜ = 0 := hθK
  have hσK : σ K = 1 := by
    have h1 : σ univ ≤ σ K + σ Kᶜ := by
      rw [← Set.union_compl_self K]; exact measure_union_le _ _
    rw [hσKc, add_zero, measure_univ] at h1
    refine le_antisymm ?_ h1
    rw [← measure_univ (μ := σ)]
    exact measure_mono (Set.subset_univ K)
  obtain ⟨K₁, K₂, sep, hK₁, hK₂, hK₁K, hK₂K, hσ1, hσ2, hsep, hdist⟩ :=
    exists_separated_compacts hd hθfr hK (by rw [hσK]; norm_num)
  have hfin1 : σ K₁ ≠ ⊤ := measure_ne_top _ _
  have hfin2 : σ K₂ ≠ ⊤ := measure_ne_top _ _
  set μ : Measure Plane := normalizedRestrict σ K₁ with hμ
  set ν : Measure Plane := normalizedRestrict σ K₂ with hν
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedRestrict hK₁.measurableSet hσ1.ne' hfin1
  haveI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_normalizedRestrict hK₂.measurableSet hσ2.ne' hfin2
  have hμfr : IsFrostman μ d (C / (σ K₁).toReal) :=
    isFrostman_normalizedRestrict hθfr hσ1.ne' hfin1
  have hνfr : IsFrostman ν d (C / (σ K₂).toReal) :=
    isFrostman_normalizedRestrict hθfr hσ2.ne' hfin2
  have hμc : μ K₁ᶜ = 0 := normalizedRestrict_compl_eq_zero σ hK₁.measurableSet
  have hνc : ν K₂ᶜ = 0 := normalizedRestrict_compl_eq_zero σ hK₂.measurableSet
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, sep ≤ dist x y := by
    filter_upwards [hμc] with x hx
    filter_upwards [hνc] with y hy
    exact hdist x hx y hy
  obtain ⟨Cb, hCb, δ, hpos, hto, hb⟩ :=
    hbound μ ν _ _ sep ‹IsProbabilityMeasure μ› ‹IsProbabilityMeasure ν› hμfr hνfr hsep hae
  have hμK₁ : (0 : ℝ≥0∞) < μ K₁ := by
    rw [normalizedRestrict_self σ hK₁.measurableSet hσ1.ne' hfin1]; norm_num
  obtain ⟨y, hyK₂, hy⟩ := exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube μ ν
    hμK₁ hνc (by rw [measure_univ]; norm_num) hCb hpos hto hb
  refine ⟨y, hKE (hK₂K hyK₂), lt_of_lt_of_le hy (measure_mono ?_)⟩
  exact Set.image_mono (hK₁K.trans hKE)

end FalconerPacking
