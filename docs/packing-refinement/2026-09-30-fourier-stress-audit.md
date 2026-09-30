# Fresh stress audit of the Fourier transfer

Date: 30 September 2026.

Audited file: `output/pdf/packing-refinement-finite-profile.tex`.

This is a fresh adversarial mathematical audit of the analytic transfer, not an
external referee report or a computer-checked proof. The profile optimization
and the independent coherent-source argument are outside its scope.

## Finding

I found no counterexample or fatal gap in the finite-profile Fourier transfer as
currently written. In particular, the proof retains the two features that are
essential for its use of wave packets: a bounded number of chain edges, and the
mandatory terminal depth $$N/2.$$ The conclusion of this audit is limited to
the transfer from the stated regular-profile chain estimate to the pinned
absolute-continuity assertion. It does not establish optimality of the chain
estimate or of the dimension inequality.

The one minor omission found is a harmless fixed constant: when estimating
conditional energy over **all** integer dyadic annuli, the regularization only
directly controls the block depths. Passing from a block depth to an intermediate
depth costs at most $$2^{2T}.$$ The manuscript's convention allowing constants to
depend on the fixed block size covers this, but stating it would make the energy
calculation more literal.

## Primary source comparison

I opened [Liu's version 3](https://arxiv.org/pdf/2603.15328v3), and checked the
local text against the PDF's identity and inflation argument. Its Section 2 and
Lemmas 3.1, 4.2–4.4 provide the relevant localization principles, packet-to-cap
replacement and inherited-cap algebra. The variable-scale calculation below is
an independent check of which geometric hypotheses that argument uses, rather
than an application of Liu's final theorem outside its hypotheses.

I also opened [Keleti–Shmerkin](https://arxiv.org/pdf/1801.08745). The use made of
finite regularization here must preserve the original coarse cube masses and
the component weight bound. Applying its finite decomposition to terminal-cube
mass data, then returning to the original restrictions, does precisely that;
no replacement limiting pin measure is needed.

## 1. Enlarged conditional parents do not require lower mass on boundary slivers

For an active block-depth parent $$Q$$ at depth $$m$$, its enlargement contains
the entire active parent. Consequently

$$
\sigma(Q^+)\geq\sigma(Q)\geq2^{-f(m)-N/T}.
$$

A ball of radius $$2^{-k}$$ at block depth $$k$$ intersects boundedly many
depth-$$k$$ cubes. Each has mass at most $$2^{-f(k)}$$, even when it is outside
the original parent but inside its enlargement. Thus the normalized restriction
satisfies

$$
\sigma_{Q^+}(B(z,2^{-k}))
\lesssim2^{N/T+f(m)-f(k)}.
$$

At a non-block depth, choose the preceding block depth. Since the interpolated
profile has slopes in $$[0,2]$$, this introduces at most $$2^{2T}$$. The resulting
truncated one-energy is bounded by

$$
C_T(N+1)R^{C\Gamma}
2^{\max_{m\leq k\leq n}\{g(m)-g(k)\}}.
$$

The diagonal is included in the innermost truncated ball. Distances larger than
the parent side contribute at most one. All of this remains valid for an
arbitrarily thin intersection of the enlarged parent with the support because
the denominator is never the mass of that intersection alone.

## 2. Tube counting survives the stated enlargements

For the underlying child-to-parent ratio $$\rho$$, a direction net of spacing
$$\rho$$ has order $$\rho^{-1}$$ directions. For two pins at separation $$d$$,
the number of directions that can put them in a tube of width $$\rho b$$ is
bounded by

$$
C\min\{\rho^{-1},b/d\}.
$$

Integrating this elementary multiplicity bound gives the sum of squared tube
masses. Increasing the width by a factor $$W\geq1$$ changes the directional
multiplicity by at most a factor $$CW$$. A fixed spatial tube grid can introduce
another polynomial factor in $$W$$. Enlarging the support or the parent by
$$R^{C_Kh}$$ therefore incurs only another $$R^{C_Kh}$$ factor; it does not
change the exponent represented by the profile cost.

For a heavy pin tube, all associated source points lie in a unit-scale source
tube of angular width $$O(W\rho)$$ from any pin of a retained pair in that tube.
The maximal-density cutoff bounds its source mass by $$CLW\rho$$. This includes
the case $$W\rho\gtrsim1$$, where the same inequality follows from the probability
bound. Hence a threshold $$H\rho$$ gives the required retained bad-pair estimate
with a polynomial enlargement factor times $$LJ/H$$.

Crucially, the source-heavy set is used only to estimate the mass of removed
pairs. The actual Fourier selection still depends solely on the inherited pin
cap marks. Treating source-heavy directions as an additional arbitrary cap
selection would not be justified; the current manuscript explicitly avoids it.

## 3. The packet-to-pair multiplicity has no fixed positive exponent loss

The finest angular caps have width $$R^{-1/2}$$ and packet tubes have width
$$R^{-1/2+h}$$. Source and pin are separated by a fixed positive distance. The
direction of any tube containing both must therefore lie in an angular interval
of length $$O(R^{-1/2+h})$$ about their connecting line. There are only
$$R^{O(h)}$$ finest labels in that interval, and a bounded number of spatial
tube labels for each direction. Enlarged packets add only $$R^{O(h)}$$.

At every intermediate edge,

$$
R^{-1/2}\leq r_j^{-1}\leq r_j/r_{j+1}.
$$

Thus both finest packet uncertainty and intermediate cap uncertainty fit inside
the enlarged conditional test tube. The removal convention uses enlarged
packet tubes meeting the initial cube, which is required for rapid decay away
from that cube. The initial cube is also much narrower than a finest packet.

If the terminal condition were removed, the displayed comparison need not hold
and the multiplicity could acquire a fixed positive power of frequency. This
audit does not justify an unforced terminal chain.

## 4. Exact cap inheritance remains valid for variable scales

Assign every finest multiplier label a unique parent at every angular scale.
Smooth supports may overlap, but labels themselves form a partition tree.
Survival of a label depends on its inherited marks. For a fixed parent cube
$$P$$, its surviving function for a cap $$\theta$$ is independent of the child
cube. Hence the identity used before orthogonality is exact:

$$
F_{Q,\alpha}
=\sum_{\substack{\theta\subset\alpha\\\theta\text{ good at }Q}}
F_{P,\theta}.
$$

This remains true for an arbitrary nested sequence of angular scales. No fixed
ratio between consecutive scales enters this algebraic identity.

For a given initial pin cube, a discarded full cap and the discarded packets
of that cap have the same circular extension there up to rapid errors: packets
whose enlarged tubes miss the cube have rapid extension there. Including a
fixed spatial source cutoff is also harmless. Outside a fixed neighborhood of
the source, each cap multiplier applied to the source probability has all
required derivatives rapidly small, so its removed tail has negligible
circular extension. All selected functions and all their error terms have
polynomial global bounds, allowing rapid errors to survive the finite sums.

## 5. One inflation step costs one tube threshold

At the child scale, the different cap supports lie in frequency balls of radius
$$O_T(R/r_j)$$ with bounded overlap. Local quadratic orthogonality consequently
applies on cubes of side $$r_j/R$$, with only the allowed enlargement powers.

For a fixed cap, the circular arc and the fixed frequency smoothing lie in a
rectangle with widths

$$
O_T(R/r_j),\qquad O_T(R/r_j^2)+O(1).
$$

The chain inequality $$r_{j+1}\leq r_j^2$$ and $$r_{j+1}\leq R$$ place this
inside a rectangle of widths $$O_T(R/r_j)$$ and $$O_T(R/r_{j+1})$$. Therefore
the corresponding function admits local-constancy estimates on the exact
child-width, parent-length tubes used by the good-tube test.

For all enlarged children contributing to one such tube, the sum of their
weights is at most

$$
R^{C_Kh}H_j\frac{r_j}{r_{j+1}}\sigma(P^+).
$$

To see this, select a good child touching the tube. Its test dilation contains
the contributing child enlargements; those enlargements lie inside the same
normalized parent, and their multiplicity is a polynomial dilation loss.

Local constancy introduces the reciprocal area of an enlarged dual tube.
Relative to the enlarged parent's area this contributes
$$R^{O_K(h)}r_{j+1}/r_j$$. The scale ratio cancels the displayed ratio in the
good-mass bound. Summing the covering tubes contributes only their enlargement
overlap. Thus there is one factor $$H_j$$, rather than a squared threshold or
a factor counting all children. This is the critical exponent check.

The parent dilation grows by $$R^{2h}$$ at each step. It therefore contains all
child dilations and their extra localization neighborhoods for sufficiently
large frequency, even if two selected scales are relatively close. Constants
may depend on the fixed chain-length bound.

## 6. Parameter dependence does not make the exponent budget circular

The order is essential and is consistent in the current proof:

1. Fix the strict margin in the desired inequality and then the starting-scale
   exponent. This fixes a uniform finite chain-length bound.
2. Choose the angular pruning and tube threshold constants large enough in
   terms of the radial integrability exponent and that length bound.
3. Make the geometric enlargement exponent sufficiently small to absorb every
   resulting threshold and overlap loss in the strict margin.
4. Choose the block size large and the regularization error small, fixing them
   thereafter, so the component exponent is much smaller still.

The annular ratio then depends on the block size. It changes curvature,
orthogonality and localization constants by possibly large **fixed** factors.
For instance a fixed factor multiplying the normal frequency width changes the
dual-rectangle estimate by a fixed factor; it does not require a stronger
power inequality than $$r_{j+1}\leq r_j^2$$. No exponent depending on the block
size must be paid before choosing the block size.

The component weights recombine linearly after the quadratic estimate. Rapid
errors can be chosen to absorb the polynomial number of components and cubes.
The discarded pin remainder must be estimated using the first norm of the
whole annular multiplier; the manuscript correctly uses that estimate instead
of summing absolute packet norms there.

## 7. Shell summation identifies the actual pinned law

The circle estimate carries the factor $$R^{-1+C(s,u)+\eta}$$. Multiplication
by the radial Plancherel weight and integration over the annulus give

$$
R^{-1+C(s,u)+\eta}
\int_{|\xi|\asymp_T R}|\widehat\mu(\xi)|^2\,d\xi
\lesssim_T R^{1-s+C(s,u)+\eta}I_s(\mu).
$$

The exponent is negative by construction, so the **norms**, not merely their
squares, are summable over the fixed-ratio annuli. Bad-shell first norms are
summable independently. All radial densities have support in one bounded
interval because of the common compact source cutoff, so the quadratic good
sum also belongs to the joint first-norm space.

For a smooth joint test function, separation makes

$$
x\longmapsto\chi(x)\int\Phi(y,|x-y|)\,d\nu(y)
$$

a smooth compactly supported source test. The distributional reconstruction
of the source therefore identifies the convergent joint density with the
original joint distance law. This addresses the possible error of obtaining
densities only for frequency-dependent source probabilities: the source here
never changes. Uniqueness of disintegration then gives absolute continuity
for almost every pin under the fixed pin probability.

## Audit limitation

The checks above substantiate the analytic transfer, but they are still a
mathematical argument relying on established Fourier tools. They do not replace
the proofs of those tools in Lean, certify the separate profile estimate, or
justify calling any resulting sufficient inequality the weakest possible one.
