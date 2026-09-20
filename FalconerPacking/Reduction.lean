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

/-! ### Letting the packing hypothesis enter

`HypTubeBound d` as stated above has no covering hypothesis on the source, and in that
generality it would imply far more than is known — Theorem 1.1 asserts its conclusion only below
the curve `B(d)`.  The honest interface carries the covering bound that the manuscript's
criterion needs: `HypTubeBoundC d u` asks for the same estimate when the source is carried by a
set of upper box dimension at most `u`, and the manuscript proves its analogue exactly when
`u < 2 d - 1`.

The packing hypothesis then enters where the manuscript puts it.  The countable-cover
characterization of packing dimension produces a piece of positive mass whose covering exponent
is below `u`; passing to its closure keeps the covering bound, intersecting with the compact
carrier makes it compact, and the source measure is restricted there before the analytic
estimate is invoked.
-/

/-- Below the packing dimension threshold there is a bounded piece of positive mass with a
covering bound: the countable-cover characterization, applied to a measure carried by the set. -/
theorem exists_piece_hasUpperBoxBound {E : Set Plane} {θ : Measure Plane}
    [IsProbabilityMeasure θ] (hθE : θ Eᶜ = 0) {u : ℝ}
    (hpack : packingDim E < ENNReal.ofReal u) :
    ∃ (S : Set Plane) (s : ℝ), 0 < θ S ∧ 0 ≤ s ∧ s < u ∧ HasUpperBoxBound S s := by
  obtain ⟨K, hK⟩ := iInf_lt_iff.1 hpack
  obtain ⟨hcov, hK'⟩ := iInf_lt_iff.1 hK
  obtain ⟨hbdd, hlt⟩ := iInf_lt_iff.1 hK'
  -- some member of the cover carries mass
  have hexn : ∃ n, 0 < θ (K n) := by
    by_contra hcon
    push_neg at hcon
    simp only [nonpos_iff_eq_zero] at hcon
    have hnull : θ (⋃ n, K n) = 0 := measure_iUnion_null hcon
    have h1 : θ E ≤ 0 := by rw [← hnull]; exact measure_mono hcov
    have h2 : (0 : ℝ≥0∞) < θ E := by
      have hle : θ univ ≤ θ E + θ Eᶜ := by
        rw [← Set.union_compl_self E]; exact measure_union_le _ _
      rw [hθE, add_zero, measure_univ] at hle
      exact lt_of_lt_of_le (by norm_num) hle
    exact absurd h1 (not_le.2 h2)
  obtain ⟨n, hn⟩ := hexn
  have hboxlt : upperBoxDim (K n) < ENNReal.ofReal u :=
    lt_of_le_of_lt (le_iSup (fun m => upperBoxDim (K m)) n) hlt
  obtain ⟨s, hs⟩ := iInf_lt_iff.1 hboxlt
  obtain ⟨hs0, hs'⟩ := iInf_lt_iff.1 hs
  obtain ⟨hbox, hslt⟩ := iInf_lt_iff.1 hs'
  exact ⟨K n, s, hn, hs0, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs0).1 hslt, hbox⟩



/-- A covering bound passes to the closure, at the cost of a constant. -/
theorem hasUpperBoxBound_closure {S : Set Plane} {s : ℝ} (hs : 0 ≤ s)
    (h : HasUpperBoxBound S s) : HasUpperBoxBound (closure S) s := by
  obtain ⟨C, hC, hcov⟩ := h
  refine ⟨C * 2 ^ s, by positivity, fun n => ?_⟩
  obtain ⟨pts, hpts, hcard⟩ := hcov (n + 1)
  have hr : ((2 : ℝ) ^ (-((n : ℕ) + 1 : ℕ) : ℝ)) < (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)]
    push_cast
    linarith
  refine ⟨pts, ?_, ?_⟩
  · have hclosed : IsClosed (⋃ x ∈ pts, Metric.closedBall x ((2 : ℝ) ^ (-((n : ℕ) + 1 : ℕ) : ℝ))) :=
      Set.Finite.isClosed_biUnion pts.finite_toSet fun x _ => Metric.isClosed_closedBall
    have hsub : S ⊆ ⋃ x ∈ pts, Metric.closedBall x ((2 : ℝ) ^ (-((n : ℕ) + 1 : ℕ) : ℝ)) :=
      hpts.trans (Set.iUnion₂_mono fun x _ => Metric.ball_subset_closedBall)
    refine (closure_minimal hsub hclosed).trans (Set.iUnion₂_mono fun x _ => ?_)
    exact fun y hy => Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy) hr)
  · refine hcard.trans (le_of_eq ?_)
    have hcast : (((n : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, show ((n : ℝ) + 1) * s = (n : ℝ) * s + s from by ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    ring



/-- **The covering-aware analytic hypothesis.**  The same averaged hyperbolic-tube estimate, but
with the source additionally carried by a set obeying a polynomial covering bound of exponent
`u`.  This is the form the manuscript's criterion takes: the estimate is expected only when `u`
is small relative to the Frostman exponent, and without such a restriction the hypothesis would
imply far more than is known. -/
def HypTubeBoundC (d u : ℝ) : Prop :=
  ∀ (μ ν : Measure Plane) (S : Set Plane) (Cμ Cν sep : ℝ),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    IsFrostman μ d Cμ → IsFrostman ν d Cν →
    μ Sᶜ = 0 → HasUpperBoxBound S u →
    0 < sep → (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, sep ≤ dist x y) →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧ Tendsto δ atTop (𝓝 0) ∧
      ∀ n, (∫⁻ y, (μ.prod μ) (hypTube y (2 * δ n)) ∂ν) ≤ ENNReal.ofReal (2 * δ n) * C

/-- **Theorem 1.1's conclusion for closed sets, with the packing hypothesis used.**  A closed
planar set of Hausdorff dimension above `d` and packing dimension below `u` has a pin inside
itself whose pinned distance set has positive length, given `HypTubeBoundC d u`.

The packing hypothesis enters exactly where the manuscript puts it: the countable-cover
characterization produces a piece of positive mass with a covering bound of exponent below `u`,
and the source measure is restricted to that piece before the analytic estimate is invoked. -/
theorem exists_pin_of_hypTubeBoundC_of_isClosed {E : Set Plane} (hE : IsClosed E)
    {d u : ℝ} (hd : 0 < d) (hdim : ENNReal.ofReal d < dimH E)
    (hpack : packingDim E < ENNReal.ofReal u) (hbound : HypTubeBoundC d u) :
    ∃ y ∈ E, 0 < volume (pinnedDistances E y) := by
  -- a compact piece of full dimension
  have hcover : E = ⋃ n : ℕ, (E ∩ Metric.closedBall (0 : Plane) n) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge (dist x 0)
      exact ⟨n, hx, hn⟩
    · rintro ⟨n, hx, -⟩; exact hx
  have hsup : dimH E = ⨆ n : ℕ, dimH (E ∩ Metric.closedBall (0 : Plane) n) := by
    calc dimH E = dimH (⋃ n : ℕ, (E ∩ Metric.closedBall (0 : Plane) n)) := by rw [← hcover]
      _ = ⨆ n : ℕ, dimH (E ∩ Metric.closedBall (0 : Plane) n) :=
          dimH_iUnion (ι := ℕ) fun n => E ∩ Metric.closedBall (0 : Plane) n
  rw [hsup] at hdim
  obtain ⟨m, hm⟩ := lt_iSup_iff.1 hdim
  set K : Set Plane := E ∩ Metric.closedBall (0 : Plane) m with hKdef
  have hKcomp : IsCompact K := (isCompact_closedBall (0 : Plane) m).inter_left hE
  have hKE : K ⊆ E := Set.inter_subset_left
  obtain ⟨θ', C, hθK, hθfr⟩ := exists_isFrostman_probabilityMeasure_of_lt_dimH hKcomp hd hm
  set θ : Measure Plane := (θ' : Measure Plane) with hθ
  haveI : IsProbabilityMeasure θ := θ'.2
  have hθE : θ Eᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 hKE) hθK
  -- the covering piece
  obtain ⟨S, s, hSpos, hs0, hsu, hSbox⟩ := exists_piece_hasUpperBoxBound hθE hpack
  set K' : Set Plane := closure S ∩ K with hK'def
  have hK'comp : IsCompact K' := hKcomp.inter_left isClosed_closure
  have hK'box : HasUpperBoxBound K' u :=
    (((hasUpperBoxBound_closure hs0 hSbox).mono Set.inter_subset_left).mono_exponent hsu.le)
  have hK'pos : 0 < θ K' := by
    have hsplit : θ (S ∩ K) + θ (S \ K) = θ S := measure_inter_add_diff S hKcomp.measurableSet
    have hdiff : θ (S \ K) = 0 := measure_mono_null (Set.diff_subset_compl S K) hθK
    rw [hdiff, add_zero] at hsplit
    refine lt_of_lt_of_le (hsplit ▸ hSpos) (measure_mono ?_)
    exact Set.inter_subset_inter_left K subset_closure
  -- separation and the analytic input
  obtain ⟨K₁, K₂, sep, hK₁, hK₂, hK₁K, hK₂K, hθ1, hθ2, hsep, hdist⟩ :=
    exists_separated_compacts hd hθfr hK'comp hK'pos
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
  have hμK' : μ K'ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 hK₁K) hμc
  have hrestrict_null : ∀ (Q : Set Plane), MeasurableSet Q → normalizedRestrict θ Q Eᶜ = 0 := by
    intro Q hQ
    rw [normalizedRestrict, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hQ,
      measure_mono_null Set.inter_subset_left hθE, mul_zero]
  have hμE : μ Eᶜ = 0 := hrestrict_null K₁ hK₁.measurableSet
  have hνE : ν Eᶜ = 0 := hrestrict_null K₂ hK₂.measurableSet
  have hae : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, sep ≤ dist x y := by
    filter_upwards [hμc] with x hx
    filter_upwards [hνc] with y hy
    exact hdist x hx y hy
  obtain ⟨Cb, hCb, δ, hpos, hto, hb⟩ :=
    hbound μ ν K' _ _ sep ‹IsProbabilityMeasure μ› ‹IsProbabilityMeasure ν› hμfr hνfr
      hμK' hK'box hsep hae
  have hμEpos : (0 : ℝ≥0∞) < μ E := by
    have h1 : μ univ ≤ μ E + μ Eᶜ := by
      rw [← Set.union_compl_self E]; exact measure_union_le _ _
    rw [hμE, add_zero, measure_univ] at h1
    exact lt_of_lt_of_le (by norm_num) h1
  have hFc : ν (K₂ ∩ E)ᶜ = 0 := by
    rw [Set.compl_inter]; exact measure_union_null hνc hνE
  obtain ⟨y, hyF, hy⟩ := exists_mem_volume_pinnedDistances_pos_of_averaged_hypTube μ ν
    hμEpos hFc (by rw [measure_univ]; norm_num) hCb hpos hto hb
  exact ⟨y, hyF.2, hy⟩

end FalconerPacking
