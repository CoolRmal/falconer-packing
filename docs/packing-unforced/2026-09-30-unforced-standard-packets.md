# Removing the prescribed midpoint using auxiliary Fourier caps

30 September 2026. Proposed analytic refinement, presented for an independent
audit before inclusion in a distance-set theorem. This note concerns the
finite-profile Fourier transfer, not its chain optimization.

## The proposed change

Keep the source wave packets at the standard angular width $$R^{-1/2}$$ and
physical tube width $$R^{-1/2+h}$$. Permit the Fourier-only cap partition used
in ball inflation to continue to widths smaller than $$R^{-1/2}$$. At those
later scales, mark all auxiliary caps inside the same standard source-cap
label identically. The marking uses that standard label's direction.

The fine Fourier pieces are defined by partitioning the original spectral
cap measure. They are **not** obtained by applying fine angular cutoffs to
individual spatially truncated source packets. Consequently the argument
does not assert that each such fine piece stays in the original packet tube.

## 1. The two inequalities needed for the geometry

Let

$$
n_0>n_1>\cdots>n_K=0,\qquad
2n_j-n_{j+1}\leq N,\qquad R=2^N,
$$

where $$n_0=(1-\zeta)N+O(T)$$ and $$K$$ is bounded independently of $$N$$.
Put

$$
a_j=2^{-n_j},\qquad r_j=Ra_j,\qquad
\delta_j=r_j^{-1},\qquad
\rho_j=\frac{a_j}{a_{j+1}}=2^{-(n_j-n_{j+1})}.
$$

Write $$\delta_*=R^{-1/2}$$ for the standard source-cap width. There are two
separate geometric facts:

$$
\delta_j\leq\rho_j,
\qquad
\delta_*\leq\rho_j.
\tag{1}
$$

The first is precisely the curvature inequality. For the second,

$$
n_j-n_{j+1}\leq n_j,
\qquad
n_j-n_{j+1}\leq N-n_j,
$$

so every admissible edge has length at most $$N/2$$. This does not require
any endpoint to equal $$N/2$$. The final edge implies only
$$n_{K-1}\leq N/2$$, which will suffice for final Fourier flatness.

The effective angular width at level $$j$$ is

$$\overline\delta_j=\max\{\delta_j,\delta_*\}.$$

Equation (1) says that this width fits into the child-to-parent tube aspect
ratio at every edge.

## 2. Labels and multipliers

Fix a standard smooth annular partition into source-cap labels $$S$$ of width
$$\delta_*$$. Denote its multipliers by $$\psi_S$$; their supports may overlap
boundedly. Each label has a nominal dyadic angular cell, and its support is
contained in a fixed dilation of that cell.

For levels with $$\delta_j\geq\delta_*$$, group whole standard labels according
to the dyadic angular cells of size $$\delta_j$$ containing their nominal
cells. These are the level-$$j$$ labels. Each has support in a fixed dilation
of an arc of width $$\delta_j$$; the supports have bounded overlap.

For levels with $$\delta_j<\delta_*$$, a label is a pair $$(S,I)$$, where
$$I$$ is a dyadic angular interval of width $$\delta_j$$ meeting the support
of $$\psi_S$$. Its multiplier is

$$\psi_S(\xi)\,\mathbf 1_I(\xi/|\xi|).$$

The intervals may partition the entire support of the standard label, not
just its nominal cell. Every such interval still lies within distance
$$O(\delta_*)$$ of the standard label's direction. Bounded overlap persists
because at a fixed direction only boundedly many standard multipliers are
nonzero. Using half-open intervals makes the label assignment literal;
their endpoints are immaterial for circular integration.

These labels form a tree: before the standard scale, parents group whole
standard labels; after it, parents retain the same standard label and group
dyadic intervals. Insert the standard scale as an auxiliary level if a chain
edge crosses it. This insertion changes no spatial scale and incurs no
inflation step.

At a circle radius $$r\asymp_T R$$, define the terminal functions by

$$
F_{S,I}
=\left(\big(\psi_S\mathbf 1_I\widehat\mu\,d\omega_r\big)*\psi\right)^\vee.
$$

If the terminal level is the standard one, omit $$I$$. The compact smooth
frequency convolution by $$\psi$$ makes these functions smooth. The hard
angular partition requires no packet localization theorem: it is only a
partition of a finite measure on the circle. Sums over descendants define
functions at all coarser angular labels. All nesting identities are exact.

## 3. Effective marks

For an active spatial cube $$Q_j$$, a level-$$j$$ Fourier label has an
effective angular label as follows:

- Before the standard angular scale, it is the level-$$j$$ label itself.
- After that scale, it is the standard label $$S$$ of the pair $$(S,I)$$.

Mark the effective label bad if the enlarged $$a_j\times a_{j+1}$$ tube
centered at $$Q_j$$ in its direction has conditional pin mass greater than
$$H_j\rho_j$$. Every Fourier label with that effective label receives the
same mark. Descendant spatial cubes inherit marks from their unique ancestors,
exactly as in the current transfer proof.

Every mark is therefore a union of whole standard source-cap labels. In
particular, all terminal Fourier labels with the same standard parent have
identical survival decisions at the initial pin cube.

For a good auxiliary fine label, its dual tube has direction within
$$O(\overline\delta_j)$$ of the effective label. By (1), its displacement over
length $$a_{j+1}$$ is at most a constant times $$a_j$$. Its tube, the relevant
child cube enlargements, and the local-constancy neighborhoods therefore fit
in the effective good test tube after the same small-power enlargements
already used in the transfer.

## 4. The source-packet identity is required only at the initial scale

Use the original standard source packets. In each initial pin cube $$Q_0$$,
remove packets whose enlarged tubes meet $$Q_0$$ and whose standard label is
marked bad at any inherited level. Let the resulting source function be
$$G_{Q_0}$$.

On $$Q_0$$, standard packet localization identifies its circular extension,
up to a rapid error, with the sum of the retained full standard-cap
extensions. This is the usual packet-to-cap replacement. Because every
terminal Fourier descendant of a retained standard label is retained, exact
spectral partition then gives

$$
\check\psi\,(G_{Q_0}*\widehat\omega_r)
=\sum_{\text{surviving terminal labels}}F_{S,I}
+\operatorname{RapDec}(R)
\quad\text{on }Q_0.
\tag{2}
$$

There is no claim that a single $$F_{S,I}$$ is localized to the spatial tube
of a source packet. Equation (2) is obtained by summing whole standard caps
first, then partitioning their original spectral measures. Fine-cutoff
spatial tails consequently do not enter the bad-part first-norm estimate.

## 5. The bad-part estimate still uses standard packet multiplicity

A separated source-pin pair belongs to at most $$R^{O(h)}$$ enlarged standard
packet tubes. If such a packet is removed, its standard direction differs
from the connecting line by $$O(R^h\delta_*)$$. The effective bad direction
differs from the packet direction by $$O(\overline\delta_j)$$. Both fit the
enlarged conditional test tube by (1).

The same squared pin-tube mass count and source angular-maximal estimate
therefore bound the union of bad pairs. No number of auxiliary Fourier caps
occurs in this argument: those caps are never individually packetized.
The first-norm bound has precisely the same $$R^{O(h)}$$ multiplicity as
before, not the fixed loss $$R^{1-2\beta}$$ associated with packetizing a
terminal angular width $$R^{\beta-1}$$ when $$\beta<1/2$$.

## 6. The inherited Fourier identity and inflation

For a level-$$j$$ cube and a parent angular label, sum terminal descendants
surviving all marks at levels $$j,j+1,\ldots,K-1$$. At level $$j$$ the mark
is constant on each level-$$j$$ Fourier label by construction. The remaining
future marks depend only on the parent cube. Hence the identity

$$
F_{Q_j,\alpha}
=\sum_{\substack{\theta_j\subset\alpha\\\theta_j\text{ good at }Q_j}}
F_{Q_{j+1},\theta_j}
\tag{3}
$$

is exact. The functions on the right are independent of the child cube.
The fact that several fine labels share one standard effective mark does
not alter this identity.

The level-$$j$$ Fourier supports lie in bounded-overlap balls of radius
$$O_T(R\delta_j)=O_T(R/r_j)$$. For the fixed cap in (3), the circular support
and fixed convolution lie in a rectangle of widths

$$
O_T(R/r_j),\qquad O_T(R/r_j^2)+O(1)
\leq O_T(R/r_{j+1}).
$$

The good effective test controls the mass of its dual tubes by Section 3.
Local orthogonality, local constancy and the tube-to-parent area cancellation
therefore give the same one-step loss $$R^{O_K(h)}H_j$$. No step of this
calculation needs the Fourier labels to correspond to source wave packets.

At the final step, $$n_{K-1}\leq N/2$$ implies $$r_{K-1}\geq R^{1/2}$$,
so the normal frequency width is at most a constant. The final functions
are ordinary terminal spectral pieces with no marks left. Their quadratic
norm sum satisfies

$$
\sum_{S,I}\|F_{S,I}\|_2^2
\lesssim_T R^{-1}\int_{S^1}|\widehat\mu(r\omega)|^2\,d\omega.
$$

The proof uses the normalized circle mass of a fixed frequency ball and
bounded overlap of the terminal multipliers. It holds for caps narrower
than the standard width as well. The terminal tangential frequency width
is $$2^{n_{K-1}}\geq1$$, so the fixed smoothing causes no new frequency-power
loss in local orthogonality.

## 7. Conditional consequence and unresolved audit status

If all these steps withstand independent scrutiny, the analytic loss depends
only on the sum of costs of an admissible chain, without a prescribed
midpoint. For $$b\geq1/2$$, the already proved unforced chain lemma gives
cost at most $$ (b-a)/(1+2b) $$, up to the established small errors. Its strict
sufficient inequality is

$$
\frac{b-a}{1+2b}<a
\quad\Longleftrightarrow\quad
b<\frac{2a}{1-2a},\qquad a<1/2.
$$

In dimension notation this would give

$$D<\frac1{3-2d},\qquad \frac76<d\leq\frac54,$$

using $$b=\max\{D-1,1/2\}$$ and strict approximation of dimensions.
The cutoff reaches two at $$d=5/4$$ and does not claim an unrestricted
improvement below the known five-quarters threshold.

This consequence is conditional here on completing the independent audit of
the revised Fourier transfer. The purpose of this note is to specify that
transfer precisely enough to expose any missing step.
