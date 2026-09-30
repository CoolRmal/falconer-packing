# Independent audit of the profile realization and sparsity argument

Date: 2026-09-30. Audited source: `research/2026-09-30-profile-realizability.md`. The audit checks the construction, exact Frostman exponent, Hausdorff and packing dimensions, stability under finite regularization, limiting chain-cost continuity, and the single-collapse sparsity estimate. It establishes no distance-set counterexample.

## Verdict

All these mathematical claims pass the audit. Two LaTeX transcription defects in the initial version were reported to the author: `left` and `inf` lacked their leading backslashes in the set definition and the packing characterization. Neither changes the intended mathematics.

## Cumulative branching and the dyadic product

The template assumptions make the two entries defining the cumulative branching function nondecreasing and 2-Lipschitz. At the beginning of each new block the initial linear part of the template is available, because the ratio of consecutive endpoint scales is smaller than its length. Both entries then equal the required joining value. At the right endpoint the floor entry wins. The resulting global function is continuous, nondecreasing and 2-Lipschitz.

Both linear barriers hold on every block. The claimed uniform comparison with the rescaled template also holds on the entire prefix, not merely the newest block: on the earlier prefix the new template is linear with slope equal to the upper dimension, and the global lower barrier bounds its difference from the old branching function by the asserted error.

Rounding half the cumulative function down gives increments zero or one. Thus simultaneous free digits in both coordinates realize the rounded exponents exactly. The accumulated rounding error is bounded rather than proportional to the depth. There are infinitely many free digits, so individual infinite digit tails have probability zero. There are also infinitely many forced digits because the lower endpoint dimension is strictly below two. Binary ambiguities therefore cause no failure of the stated positive-mass half-open cube formula or of the support covers by the associated closed dyadic squares.

## Exact Frostman estimate and Hausdorff dimension

The rounded exponent is at least the lower dimension times the depth minus two. A ball at a dyadic radius meets only boundedly many dyadic squares of that same scale, each of precisely known mass. This gives the exact lower-dimensional Frostman estimate, with one fixed multiplicative constant, at all centers and radii. No loss of the exponent is incurred.

The Frostman bound supplies the lower Hausdorff dimension. At the chosen endpoint scales the number of occupied squares is bounded by the exponential of the lower dimension times the depth. The corresponding covering sums tend to zero at every strictly larger exponent. This proves equality of the Hausdorff dimension.

## Upper box and packing dimensions

The global upper barrier bounds the upper box dimension by the prescribed upper dimension. At the template's initial linear scales the branching ratio tends to that dimension. The ball-mass bound before imposing the lower barrier forces any covering to use a constant times the full branching count, and proves the matching lower bound for upper box dimension.

The packing argument correctly uses outer measure, so no measurability of arbitrary pieces in a countable upper-box cover is being assumed. At least one piece has positive outer measure. Covering that piece by balls and applying outer subadditivity shows its upper box dimension is at least the same upper dimension. The modified-upper-box characterization of packing dimension then supplies the lower packing bound.

The argument is slightly stronger than the version needed for the full set: every subset of positive outer measure has upper box dimension equal to the upper dimension. Applying the same countable-cover argument to any such subset proves that its packing dimension also equals that upper dimension. For positive measurable subsets, the restricted probability additionally preserves the lower Frostman exponent, so their Hausdorff dimension remains the lower dimension.

No separation between neighboring dyadic cylinders beyond their grid geometry was used, and none is needed.

## Limiting profile costs

The monotonicity in the starting endpoint follows by truncating the crossing edge of a chain; admissibility is preserved and the edge minimum can only rise. The complementary-depth doubling bridge is finite and its cost is at most negative variation. The resulting difference of optimal costs is bounded by the distance between the starting endpoints.

Merging adjacent admissible edges does not increase their total cost. If no further merger is possible, every two edges more than double the complementary depth. This bounds the number of edges independently of the number of linear pieces in the profile. An error in the uniform norm changes every edge cost by at most twice that error, giving the claimed continuity of the limiting cost. The rounded normalized profiles are indeed 1-Lipschitz because their slopes are plus or minus one. Exact linear barriers after rounding are unnecessary for this stability argument.

## Restriction and finite regularization

For a normalized restriction of weight $w$, each occupied coarser cube has mass at most its old mass divided by $w$. Combining this with the lower regular mass bound gives

$$
f(k)\ge F_{\rm dyad}(k)+\log_2w-eN.
$$

The number of occupied coarser cubes cannot increase after restriction. Their masses sum to one and are each at most the upper regular mass bound, giving

$$
f(k)\le F_{\rm dyad}(k).
$$

Both signs are correct. A weight bounded below by an exponential with small exponent therefore changes the normalized profile by at most that exponent plus the regularization error. The claim is quantitative closeness when those losses are small; it does not incorrectly assert convergence with fixed nonzero losses.

These inequalities only need the restriction's domination by the old probability and its occupied-cube count, so their reasoning also applies to restrictions to other measurable sets whenever the stated regularized mass bounds hold.

## Single-collapse logarithmic sparsity

For two near occurrences at scale ratio $r$, the endpoint value of the smaller prefix equals the value of the larger prefix at $r$, after multiplication by $r$. The combined error is exactly at most $(1+r)$ times the approximation tolerance. Evaluating the two affine pieces of the template gives the claimed alternatives: the ratio is small or close to one.

Taking logarithms converts this into a forbidden interval of pairwise separations. Within any interval shorter than the larger forbidden separation, every pair of occurrences must have separation at most the smaller one. Thus the occurrence set has bounded diameter there even if it is disconnected. Its Lebesgue measure is bounded by that diameter. Partitioning a long interval and then letting the interval length approach the forbidden separation proves the upper-density estimate. Continuity of the global profile ensures measurability of the occurrence set.

The stated order of the density bound follows because the short separation is of the order of the tolerance, while the long separation is of the order of the logarithm of its reciprocal. The argument supplies no summable frequency estimate: isolated positive-power losses still need not tend to zero. The note correctly keeps that limitation explicit.

## Audit of the assembled TeX fragments

The subsequently assembled `output/pdf/packing-unforced-realizability.tex` faithfully states and proves the results audited above. The additional remark about two separated cylinder restrictions is valid. A fixed cylinder changes the cumulative mass exponent by at most a fixed constant on the whole prefix; rescaling its support changes depths by a fixed integer and adds another bounded error. Both disappear after normalization. Choosing cylinder diameters small relative to two distinct support points gives compact closures a positive distance apart. Their exact dimensions persist.

The simultaneously reviewed `output/pdf/packing-unforced-finite-start.tex` faithfully transcribes the variation proof from `research/2026-09-30-critical-profile-endpoint.md`, including the exact initial mass-profile correction. Its null-length example has the stated masses, norms, orthogonal increments, and dimension. No substantive discrepancy was found. For the orthogonality explanation, the immediately preceding-stage intervals suffice: the new increment has zero integral on each, and all earlier increments are constant there.
