# Independent audit of synchronized profiles and source Fourier energy

Date: 2026-09-30. This audit covers `research/2026-09-30-profile-fourier-saturation.md` and `research/2026-09-30-synchronized-profile-energy-obstruction.md`. Both concern limitations of the raw source-energy input, not sharpness of the actual distance theorem.

## General-template near-saturation: passed

The first note uses the already audited homogeneous dyadic realization. The two fixed separated restrictions can be chosen at one common depth, giving equal restriction weights and exactly equal conditional branching exponents at every subsequent depth. Before that depth the exponent is zero; afterward it is the original exponent minus its value at the conditioning depth. Thus its uniform difference from the original branching exponent is bounded independently of the Fourier scale. The support dimensions and Frostman bounds persist.

The Gaussian identity has the correct two-dimensional scaling. Equal terminal-cube pairs alone have squared distance at most twice the reciprocal squared frequency, giving the factor exponential of minus two pi and the asserted lower bound. The terminal exponent is at most the lower dimension times the terminal depth, so the lower bound has the full Frostman upper-bound power with a fixed positive constant.

The upper Gaussian estimate follows by summing spatial annuli using the Frostman estimate. Its conversion to a sharp frequency-ball estimate has the correct factor exponential of pi. The frequency region below the terminal frequency to the power one minus the tolerance is negligible because the exponent two minus the dimension is strictly positive. The upper region has the exact stated planar Gaussian tail and is negligible even using only the trivial bound on the Fourier transform.

The remaining frequency window is covered by a number of dyadic annuli linear in the terminal depth. Pigeonholing therefore loses only that linear factor. The index of the selected annulus lies in the stated multiplicative-depth window. The chosen error parameter makes the resulting frequency exponent at least the desired one; the remaining polynomial loss is absorbed by a strictly positive linear-in-depth margin.

The moving-prefix comparison uses only the 1-Lipschitz property and the zero initial value. Both argument variation and denominator variation contribute at most the depth difference divided by the new depth. The simplified bound by four times the window parameter plus four divided by the terminal depth is valid once their sum is below one half. The three vanishing profile errors and this fixed small error fit the prescribed tolerance. The same supports work for all tolerances and exponent losses; only the selected annuli change.

No annular lower bound is asserted at an arbitrarily prescribed frequency. No positivity of an annular spatial kernel is assumed. The Gaussian argument locates an annulus and preserves the template by quantitative continuity, exactly as needed.

## Finite critical energy and exact annular saturation for single collapse: passed

The second note is a separate construction and supplies an additional property: finite energy at the exact lower dimension. It adds twice the binary logarithm of the depth to the terminal branching exponent. The maximality defining each terminal depth bounds the rounding remainder uniformly. Long growth blocks followed by constant blocks preserve the global upper branching barrier and the lower barrier with this logarithmic excess, up to one fixed additive constant.

The lower logarithmic excess implies the stated ball bound and makes the critical energy sum converge. It does not conflict with the exact Hausdorff dimension: the terminal covers prove vanishing covering sums only at strictly larger exponents. The upper box estimate follows from the upper branching barrier. The countable upper-box cover argument correctly proves the lower packing dimension.

The branch increments zero, one, or two have the claimed homogeneous dyadic realization. Increments one allow only the horizontal digit to vary, while increments two allow both. Since the upper dimension is strictly greater than one and the growth blocks become arbitrarily long, both coordinates have infinitely many free digits. Boundary ambiguities therefore have measure zero.

Unlike the general realization's floor-clipped endpoint, this construction has an exact constant branching block all the way to its selected terminal depth. Consequently the decomposition into equal-mass translated microscopic copies is exact. The corner spacing is at least the reciprocal growth-endpoint frequency. Choosing a fixed small dyadic factor in the Fourier scale makes the Fourier transform of every microscopic probability uniformly close to one on the support of the annular cutoff.

All fixed-order derivatives of that microscopic Fourier transform are uniformly bounded by compact support. Hence the effective annular functions have uniform Schwartz bounds after inverse transformation. The diagonal in the Fourier expansion is positive and comparable to the frequency squared divided by the number of copies. The crude absolute estimate for all off-diagonal terms is sufficient: choose the Schwartz exponent large enough that the long constant block beats the copy count. The logarithmic terminal excess then gives exactly the claimed annular energy divided by the squared logarithm of the frequency.

This proves the failure of any fixed positive power saving in this raw annular energy, even with finite energy at the critical exponent and synchronized single-collapse source and pin profiles. It says nothing comparable about the modified good-packet energy.

## Positive collision identity and conditional criterion

The collision kernel identity is correct for a nonnegative compactly supported smooth probability mollifier. The same-part contribution is bounded by its supremum times the reciprocal smoothing scale and the sum of squared part masses. For the microscopic copies in the construction, every within-copy distance difference is bounded by the copy diameter, so continuity and positivity of the kernel at zero give the matching lower bound uniformly in the pin.

The full positive collision integral decomposes exactly into same-part and different-part contributions. Uniform bounds on both yield a bounded sequence in the joint quadratic space. Weak compactness and weak convergence of the positive mollified measures identify the actual joint distance law with the limiting density; disintegration then gives the claimed almost-everywhere pinned quadratic density. This is a conditional criterion, not a proved bound for the different-part term.

The original note said only “nonnegative smooth mollifier.” I reported the need to specify a member of the compactly supported smooth class with integral one. That standard choice makes the kernel bounded and continuous and gives the fixed bounded radial support used later. No other issue was found.

Finally, the caution about signed off-diagonal Fourier terms is necessary and correctly stated. Those terms cannot replace the nonnegative different-part collision integral without an additional argument.
