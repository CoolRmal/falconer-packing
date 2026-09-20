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

/-- **The reduction, in its general form.**  Any set carrying a compactly supported `d`-Frostman
probability measure has a pin inside it whose pinned distance set has positive length, given the
hyperbolic-tube estimate.

No compactness or Borel hypothesis on `E` is needed: only that `E` carries the measure.  The pin
is produced inside `E` because the pin measure inherits `θ Eᶜ = 0`. -/
theorem exists_pin_of_hypTubeBound_of_frostman {E K : Set Plane} {d : ℝ} (hd : 0 < d)
    (θ : Measure Plane) (C : ℝ) (hθprob : IsProbabilityMeasure θ)
    (hθE : θ Eᶜ = 0) (hK : IsCompact K) (hθK : θ Kᶜ = 0) (hθfr : IsFrostman θ d C)
    (hbound : HypTubeBound d) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  haveI := hθprob
  have hθKpos : 0 < θ K := by
    have h1 : θ univ ≤ θ K + θ Kᶜ := by
      rw [← Set.union_compl_self K]; exact measure_union_le _ _
    rw [hθK, add_zero, measure_univ] at h1
    exact lt_of_lt_of_le (by norm_num) h1
  obtain ⟨K₁, K₂, sep, hK₁, hK₂, hK₁K, hK₂K, hθ1, hθ2, hsep, hdist⟩ :=
    exists_separated_compacts hd hθfr hK hθKpos
  have hfin1 : θ K₁ ≠ ⊤ := measure_ne_top _ _
  have hfin2 : θ K₂ ≠ ⊤ := measure_ne_top _ _
  set μ : Measure Plane := normalizedRestrict θ K₁ with hμ
  set ν : Measure Plane := normalizedRestrict θ K₂ with hν
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedRestrict hK₁.measurableSet hθ1.ne' hfin1
  haveI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_normalizedRestrict hK₂.measurableSet hθ2.ne' hfin2
  have hμfr : IsFrostman μ d (C / (θ K₁).toReal) :=
    isFrostman_normalizedRestrict hθfr hθ1.ne' hfin1
  have hνfr : IsFrostman ν d (C / (θ K₂).toReal) :=
    isFrostman_normalizedRestrict hθfr hθ2.ne' hfin2
  have hμc : μ K₁ᶜ = 0 := normalizedRestrict_compl_eq_zero θ hK₁.measurableSet
  have hνc : ν K₂ᶜ = 0 := normalizedRestrict_compl_eq_zero θ hK₂.measurableSet
  -- the restrictions inherit the carrier `E`
  have hrestrict_null : ∀ (Q : Set Plane), MeasurableSet Q → θ Q ≠ 0 →
      normalizedRestrict θ Q Eᶜ = 0 := by
    intro Q hQ h0
    rw [normalizedRestrict, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hQ,
      measure_mono_null Set.inter_subset_left hθE, mul_zero]
  have hμE : μ Eᶜ = 0 := hrestrict_null K₁ hK₁.measurableSet hθ1.ne'
  have hνE : ν Eᶜ = 0 := hrestrict_null K₂ hK₂.measurableSet hθ2.ne'
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, sep ≤ dist x y := by
    filter_upwards [hμc] with x hx
    filter_upwards [hνc] with y hy
    exact hdist x hx y hy
  obtain ⟨Cb, hCb, δ, hpos, hto, hb⟩ :=
    hbound μ ν _ _ sep ‹IsProbabilityMeasure μ› ‹IsProbabilityMeasure ν› hμfr hνfr hsep hae
  have hμEpos : (0 : ℝ≥0∞) < μ E := by
    have h1 : μ univ ≤ μ E + μ Eᶜ := by
      rw [← Set.union_compl_self E]; exact measure_union_le _ _
    rw [hμE, add_zero, measure_univ] at h1
    exact lt_of_lt_of_le (by norm_num) h1
  have hFc : ν (K₂ ∩ E)ᶜ = 0 := by
    rw [Set.compl_inter]
    exact measure_union_null hνc hνE
  obtain ⟨y, hyF, hy⟩ := exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube μ ν
    hμEpos hFc (by rw [measure_univ]; norm_num) hCb hpos hto hb
  exact ⟨y, hyF.2, hy⟩

/-- **The compact case.**  A compact planar set whose Hausdorff dimension exceeds `d` carries a
`d`-Frostman probability measure by Frostman's lemma, so the reduction applies to any set
containing it. -/
theorem exists_pin_of_hypTubeBound {K E : Set Plane} (hK : IsCompact K) (hKE : K ⊆ E)
    {d : ℝ} (hd : 0 < d) (hdim : ENNReal.ofReal d < dimH K) (hbound : HypTubeBound d) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  obtain ⟨θ, C, hθK, hθfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH hK hd hdim
  refine exists_pin_of_hypTubeBound_of_frostman hd (θ : Measure Plane) C θ.2 ?_ hK hθK hθfr hbound
  exact measure_mono_null (Set.compl_subset_compl.2 hKE) hθK

/-! ### Closed sets

A closed set is exhausted by compact pieces and Hausdorff dimension is countably stable, so one
piece already has dimension above `d` and Frostman's lemma applies to it.  For a general Borel
set the same argument needs a compact subset of dimension above `d` — the Besicovitch–Davies
subset theorem, which is not in Mathlib and is not proved here.
-/

/-- **Theorem 1.1's conclusion for closed sets, from the tube estimate alone.**  A closed planar
set of Hausdorff dimension above `d` has a pin inside itself whose pinned distance set has
positive length, given `HypTubeBound d`.

Closed sets are exhausted by compact pieces, and Hausdorff dimension is countably stable, so one
piece already has dimension above `d`; Frostman's lemma applies to it.

For a general Borel set the same statement needs a compact subset of dimension above `d`, which
is the Besicovitch–Davies subset theorem and is not in Mathlib. -/
theorem exists_pin_of_hypTubeBound_of_isClosed {E : Set Plane} (hE : IsClosed E)
    {d : ℝ} (hd : 0 < d) (hdim : ENNReal.ofReal d < dimH E) (hbound : HypTubeBound d) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  have hcover : E = ⋃ n : ℕ, (E ∩ Metric.closedBall (0 : Plane) n) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (dist x 0)
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, -⟩
      exact hx
  have hsup : dimH E = ⨆ n : ℕ, dimH (E ∩ Metric.closedBall (0 : Plane) n) := by
    calc dimH E = dimH (⋃ n : ℕ, (E ∩ Metric.closedBall (0 : Plane) n)) := by rw [← hcover]
      _ = ⨆ n : ℕ, dimH (E ∩ Metric.closedBall (0 : Plane) n) :=
          dimH_iUnion (ι := ℕ) fun n => E ∩ Metric.closedBall (0 : Plane) n
  rw [hsup] at hdim
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hdim
  have hKcomp : IsCompact (E ∩ Metric.closedBall (0 : Plane) n) :=
    (isCompact_closedBall (0 : Plane) n).inter_left hE
  exact exists_pin_of_hypTubeBound hKcomp Set.inter_subset_left hd hn hbound

end FalconerPacking
