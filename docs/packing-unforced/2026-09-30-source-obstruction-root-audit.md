# Audit of the fixed source-measure obstruction

30 September 2026. This is an internal proof audit of the recursive construction
in `2026-09-30-nonremovable-bisector-source-obstruction.md`. It is not external
refereeing. The audit checks the fixed measure, the dimensional assertions,
the collision calculation, and the stronger weak-norm statement.

## The construction has uniform estimates at each stage

The finite block has

$$
s=11/10,\quad u=13/11,\quad \beta=1/20,\quad
\delta=2^{-40L},\quad a=2^{-11L},\quad
w=2^{-20L},\quad h=2^{-22L}.
$$

The four center digits in base 2048 give exactly the stated center dimension
and counting bounds. The horizontal microscopic spacing is larger than each
child square. Different tracks and different vertical slats are even farther
apart. Consequently descendants in distinct stage squares remain separated,
and all assignments to parents, tracks, and slats are unambiguous.

The block's four mass bounds follow by counting its horizontal and vertical
indices. No independence of the final measure inside a microscopic square is
needed. At the two internal transitions the important equalities are

$$
\delta^\beta w^{1-s}=1,
\qquad
\delta^{1/2-\beta}=h^{2-u},
\qquad
\delta^{1-s}=h^{1-u}.
$$

They verify the asserted Frostman and covering exponents throughout the
intermediate scales, not only at the finest resolution. At radii between the
child side and the microscopic spacing, the fixed factor in the child side
changes only the constant.

## The estimates pass to one fixed measure

At generation j the parent mass and side are denoted by p and lambda. A ball
with radius between two successive child sides meets only a bounded number of
the previous parents. The normalized one-block estimate therefore gives the
stated global mass estimate. Its coefficient grows by a fixed factor at each
generation. For every exponent strictly below s, the factor is absorbed by the
old parent side, because the total depth grows faster than the generation
number. This proves a Frostman bound for every such exponent; it does not
assert the endpoint Frostman bound at s.

For coverings, the factor multiplying the u-power at each completed stage is
strictly less than one. Thus the global upper covering bound is valid at all
scales. At the distinguished radius lambda times h, a ball meets at most a
constant number of slats and a constant times h divided by delta horizontal
cells. Its mass is at most a constant times

$$
p\delta^{3s/2-1}.
$$

The new block depth dominates every old depth. Hence every positive outer-mass
subset has upper box dimension at least

$$
\frac{3s/2-1}{s/2}=\frac{13}{11}.
$$

Applying the countable-cover characterization of packing dimension proves the
packing lower bound. Endpoint cylinder counts and the Frostman exponents prove
the Hausdorff dimension. The result is one fixed compact set and probability,
independent of the later source restriction or norm exponent.

## The collision scale and parent factors

The pin measure is the translate by the fixed vector (0,3). Inside matching
source and pin parent-tracks, the transverse displacement is at most a constant
times lambda times w. The vertical difference between source points in one
slat is at most a constant times lambda times delta. The distance denominator
is bounded below by the fixed source--pin separation. Thus the radial
oscillation is bounded by

$$
C(\lambda\delta+\lambda^2w^2)\le C'\lambda\delta.
$$

In particular there is no missing inverse-parent factor in the curvature
term. The separation between the translated parent copies stays close to
three; it is not rescaled to lambda.

Each full pin parent-track has mass p times m. Applying Cauchy--Schwarz over
source slats, tracks, and parents yields the squared-norm lower bound

$$
c M^2p^2\lambda^{-1}\delta^{3s/2-2}.
$$

The exact binary exponent in the draft is correct:

$$
14L_j-48\sum_{k<j}L_k+26(j-1)\longrightarrow+\infty.
$$

This proves divergence for every nonzero positive source measure supported on
the compact set. Domination by the constructed probability is not used in this
part of the argument.

## Weak norms and the stronger quantifier

For each pin, take the union of the short radial intervals containing all
matching source slats. Over the pin space this is a Borel set S at the stage in
question. Its reference measure and distance-law mass satisfy

$$
(\nu\times dt)(S)\le C\lambda\delta^{1-s/2},
\qquad
\mathcal D_{\eta,\nu}(S)\ge pmM.
$$

The second identity uses only the equal masses of the full pin tracks and the
total mass M of the source measure. It remains valid even if that source
measure is singular with respect to the constructed probability.

A nonnegative weak-Lq function obeys the support integral estimate obtained by
integrating the minimum of its distribution bound and the set measure. This
gives the lower bound in the draft. Its microscopic exponent simplifies to

$$
\beta-(1-s/2)(1-1/q)=-\frac25+\frac{9}{20q},
$$

which is negative exactly for q greater than 9/8. The rapidly increasing block
depths absorb all preceding mass and side factors for each fixed such q.
There is no asserted endpoint result at q equal to 9/8.

For matched pin restrictions the same support argument has mass at least
M squared times p times m, and reference measure at most M times the preceding
bound. The exponent is unchanged. A common-submeasure extension can be proved
directly by the same support test; no unsupported change of reference measure
for a Lorentz norm is needed.

## Exact consequence for the research target

The full pin measure has finite tau-energy for every tau strictly between one
and s. The proved bisector criterion would force a raw joint second-norm
density for any nonzero source measure on this compact set having finite first
energy and the proposed bisector mixed norm. The obstruction excludes that
possibility. Thus merely choosing a different positive source measure cannot
establish the proposed mixed-norm hypothesis against these fixed pins.

This does not exclude independently restricting the pin set to avoid matching
source regions, or allowing the source restriction to depend on the pin. It
does not contradict absolute continuity or positive distance length. Indeed
the support dimensions satisfy the manuscript's coherent sufficient condition.
The dimension cutoff and its strict endpoints are unchanged by this audit.

## Stronger same-set pins, with radii bounded away from zero

The translated construction admits a particularly simple internal version.
The number of first-stage vertical slats is even. Change the first vertical
slat digit by half that number, cyclically, and keep every horizontal and
later digit fixed. This defines an involution F of the compact set. On each
first-stage child it is exactly a vertical translation by plus or minus 1/32,
and it preserves the natural probability.

For every later generation, F maps each parent and all its track and slat
descendants to identical translated copies. Use pins in F(Q,i) when the source
lies in parent-track (Q,i). These pin pieces still partition K and each has
mass p times m. Because the parent side is at most the tiny first child side,
all corresponding source--pin distances lie strictly between 1/64 and 1/16.
The fixed-separation radial width estimate is unchanged. The source-law mass
and reference-volume bounds for the joint support sets are therefore exactly
the same as above, with full pins equal to the original probability on K.

Consequently the weak-norm obstruction holds against full same-set pins for
every positive source measure on K, even after restricting the distance law
to that one fixed radial interval. It is not caused solely by pairs approaching
the source--pin diagonal. The original translated and matching-pin variants
remain valid. This strengthening does not assert failure for every arbitrary
independently chosen pin measure on K.
