# Independent audit of the curvature-matched hybrid obstruction

Date: 2026-09-30. Audited source: `output/pdf/packing-unforced-hybrid-obstruction.tex`. The fragment passes the mathematical audit for its stated scope: the same realized profiles defeat the existing strict chain-cost test and the existing coherent summability certificate when their indices are matched by curvature. It does not assert a counterexample to the distance theorem or prove failure of a new estimate that combines the methods differently.

## Conditional-energy lower bound

For a homogeneous measure, every occupied parent has the same number of terminal descendants, with equal conditional masses. The same-descendant pair probability is exactly the reciprocal of that number. Such a pair has separation at most the square diameter at terminal depth, so the Riesz kernel gives the claimed lower bound, including its dimensional constant. Summing over parents with their probability weights introduces no count factor.

At terminal depth twice the coherent depth, the energy-exponent terms cancel to leave precisely the coherent depth. Monotonicity of the cumulative branching exponent permits replacement of the child depth by the parent depth in the lower bound. Thus equation `hybrid:midpoint` has the correct sign and scaling. Finiteness of the conditional energies follows from the realized exact Frostman bound when the energy exponent is strictly below that dimension; normalization on a fixed positive-mass cube preserves finiteness.

Uniform template convergence then gives the displayed lower exponential rate in terms of the midpoint profile value minus its terminal value. For a strictly positive rate, fixed rounding and additive depth changes are immaterial.

## Matching-profile midpoint values

The single-collapse profile's first affine piece always extends past the midpoint in the stated domain. Its limiting cost is at least the lower slope exactly in the indicated high-side range, which is strictly above the coherent dimension line. Both conclusions are therefore simultaneous.

The midpoint identity for the two-collapse profile is not valid on its entire abstract parameter domain. The fragment correctly restricts it to the dimension-relevant middle branch and separately treats the low boundary. I independently recomputed both displayed formulas for the first affine endpoint minus one half. The middle-branch expression is positive at the transition because the relevant numerator is increasing and its value at the lower endpoint is strictly positive by the stated integer-square comparison. Monotonicity in the upper slope then gives positivity throughout the specified range.

At the low boundary, substituting the upper slope equal to twice the lower slope gives the second displayed formula, positive throughout the stated interval. This witness lies inside the two-collapse domain. Its limiting chain cost is at least the lower slope by the previously proved exact cost formula. No unsupported universal midpoint identity is being used.

## The zero-exponent boundary construction

The new construction with the minimum of the rescaled template and a slope-two catch-up line is valid. At the start of a block the catch-up line has the required joining value. Both functions are nondecreasing and 2-Lipschitz; both majorize the lower linear barrier on that block, and their minimum lies below the upper barrier.

The first intersection is in the initial linear part when the next endpoint is sufficiently large. After that intersection, the slope-two line stays above the template: the difference is nondecreasing because the template is 2-Lipschitz. Hence the construction agrees exactly with the template at the midpoint and endpoint. Uniform approximation on the full prefix follows because the discrepancy is confined to an initial interval of length bounded by a constant times the preceding block depth; the previous prefix has the same bounded-length error after normalization.

Rounding half the continuous cumulative function down gives a legitimate product-digit measure, with bounded rounding error and the same exact Frostman and dimension conclusions. At the matched midpoint and endpoint, the rounded difference in `hybrid:midpoint` is bounded below by minus two. Therefore the coherent quantity has a fixed positive lower bound along infinitely many blocks. This establishes actual failure of its summability criterion at the boundary, rather than merely a zero exponential rate.

Fixed positive-mass cylinder conditioning subtracts the same cumulative constant at both later depths. It cancels in the midpoint bound. Two separated such cylinders therefore preserve the calculation and the profile recurrence needed for the example.

## Scope of synchronization

The synchronized quantities proved here are the limiting chain-profile cost at terminal depth and the coherent certificate at half that depth. The prior Gaussian argument locates a raw source-energy lower bound in a nearby annulus; this fragment does not make the additional claim that this third quantity is saturated at exactly every displayed terminal frequency. In the positive-rate cases, the coherent obstruction is stable under sufficiently small relative depth perturbations. The zero-rate boundary would require an additional synchronization calculation if exact raw-energy saturation there were asserted. No such assertion is needed for, or made by, the present two-certificate obstruction.
