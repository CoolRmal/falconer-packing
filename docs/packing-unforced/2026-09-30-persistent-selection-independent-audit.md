# Independent audit of persistent selection and the half-order potential

Date: 2026-09-30. Audited source: `research/2026-09-30-persistent-selection-and-half-potential.md`. The finite-model estimates, weak-compactness criteria, and fixed-measure obstruction pass the mathematical audit. One overstrong sentence about the necessity of persistence was reported for correction; it is a wording issue distinct from the valid propositions.

## The half-order potential

The per-track first norm is its source mass. Its supremum estimate follows from the earlier cell and slat counts for every offset much larger than track width, not only beyond the larger deletion window: the product of offset and width then already dominates the mollification scale, so the microscopic vertical error is absorbed. The number of visible slats remains bounded by one plus that product divided by the slat spacing. No assumption that the product exceeds the slat spacing is needed before the final simplification.

Bounding the squared norm by first norm times supremum and applying Minkowski gives the displayed half-order potential, including all positive cross-track terms. The dyadic-annulus bound for that potential has exactly the three stated regimes. The discrete counting correction is absorbed because the cutoff is at least a fixed multiple of the center spacing.

Deleting only the own track leaves all offsets comparable to or larger than center spacing. For an exponent between one third and one half, substitution in the potential gives the nonnegative power asserted in the note. At one third the power is zero and no logarithm occurs. At one half the logarithm is dominated by the positive power of the scale; above one half the potential is bounded. This proves the positive half of the exact own-track transition. The previously established neighbor-track obstruction proves its negative half.

Below one third, the proposed larger cutoff is much larger than center spacing. Its exponent makes the half-order potential contribution constant, and the center-counting estimate gives the improved deletion bound. The exponent arithmetic is correct.

## The stronger necessary deletion budget

For a radius much larger than center spacing, the total mass of tracks between a constant multiple of center spacing and that radius is comparable to the radius to the transverse dimension. Ahlfors regularity and maximal-net coverage give the lower count; removing finitely many innermost net neighbors costs only a constant times the spacing to that dimension. The pin's displacement inside its own track is negligible, so shifting the center of the window to the actual pin preserves these estimates.

The radial image of one such track has measure at most a constant times its offset times width divided by slat spacing. Thus Cauchy--Schwarz bounds the retained track's squared norm below by the reciprocal of its offset times the slat-spacing-to-width ratio and the square of its retained mass. All densities are nonnegative, so summing their squared norms gives a valid lower bound for the full squared norm.

Weighted Cauchy--Schwarz then uses the sum of offsets in the denominator. There are at most a constant times the radius to the transverse dimension divided by one track mass such offsets, each at most the radius. This gives the displayed power in equation (7). Jensen across pins correctly replaces pointwise deleted masses by their average.

Taking the radius to be a sufficiently small fixed multiple of the product of track mass and slat-spacing-to-width ratio raised to the reciprocal of one minus the transverse dimension forces the desired contradiction whenever the proposed deletion is smaller. This radius remains much larger than center spacing precisely in the stated regime below one third. The necessary exponent is therefore correct. It is smaller than the own-track exponent and larger than the sufficient exponent in that regime, so the stated gap between upper and lower deletion bounds is consistent.

## Vanishing loss and fixed-measure obstruction

The vanishing-loss lemma is valid along any sequence of scales tending to zero. Positive mollified sublaws have bounded radial support and uniform quadratic norm. Their weak quadratic subsequential limit exists. Their total-variation difference from the full mollified law is bounded by the deleted mass and tends to zero. Continuous test functions therefore identify the weak quadratic limit with the original joint law.

The original fixed train-track glued measure has no quadratic joint density, because convolution of any such density by the probability mollifier would keep every smoothing norm bounded. The proved divergence contradicts that. Hence the same fixed pair defeats every vanishing total-deletion rate, even when uniform retained estimates are requested only along an arbitrary sequence. The argument does not depend on selecting the designated divergence scales. The finite-critical-energy variant preserves this conclusion under that additional hypothesis.

## Positive retained mass and the correct persistence scope

A fixed positive lower bound for the retained mass, together with bounded quadratic norms, yields a nonzero quadratic subdensity of the original law. Positivity passes to a weak quadratic limit; the indicator of a fixed region containing all radial supports verifies its retained mass. Domination by full mollifications passes to the limit on nonnegative continuous tests. Disintegration gives a nonzero absolutely continuous pinned component for a positive-measure set of pins, hence positive-length compact distance sets.

This proposition does not require the selections to be nested. The introduction's statement that a valid method must preserve earlier deletions was therefore too strong. Persistent deletion with summable costs is one sufficient implementation; arbitrary nonnested selections meeting the same mass and norm hypotheses also work. The author was asked to make this distinction explicit.

The final equivalence with a nonzero absolutely continuous component is correct. A positive bounded part of that component can be chosen away from a null set carrying the singular measure, then lifted through the source-pin distance map. Its pullback is a positive source-pin restriction with a bounded joint density. Requiring such restrictions with arbitrarily small fixed loss is equivalent to absolute continuity of the full joint law, since the singular mass must then vanish. None of these generic measure-theoretic facts produces the required geometric selections by itself.

## Assembled TeX and fixed-exponent extension

The assembled `output/pdf/packing-unforced-positive-selection.tex` preserves the audited proofs. Its generalization of the compactness proposition to each fixed exponent strictly between one and infinity is valid. Reflexivity supplies the weak subsequence; bounded mass and continuous domination tests belong to the dual space on the fixed finite product support. The limit has the same fixed exponent, and positivity, domination, disintegration, and the retained-mass argument are unchanged.

The vanishing-loss consequence is correctly combined with the independently proved weak-norm obstruction only for exponents larger than the train-track threshold. Strong membership at such an exponent would imply weak membership and is therefore impossible for the counterexample. No obstruction is asserted for exponents sufficiently close to one.

The half-potential, exact own-track transition, and stronger necessary deletion cost are faithfully transcribed. The previously reported persistence overstatement has been removed, and the one-track proof now explicitly covers the case where offset times width is smaller than slat spacing.
