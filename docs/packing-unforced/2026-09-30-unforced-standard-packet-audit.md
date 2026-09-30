# Audit of standard source packets with finer auxiliary Fourier caps

30 September 2026. Independent adversarial audit of the Fourier agent's proposed removal of the forced midpoint. This note checks the additional construction against the existing conditional-energy inflation argument. It does not replace a fully assembled proof of that analytic argument or establish optimality.

## Findings

I find no obstruction arising from the previously identified source-packet multiplicity or from the finer auxiliary caps, provided the construction below is followed literally. The essential separation is between physical source packets, which always remain at the standard angular scale $R^{-1/2}$, and exact spectral subdivisions of their summed circular extensions. One must never decompose individual physical source packets into the finer auxiliary caps in the bad-mass estimate.

This audit supports integrating the modification into a complete analytic proof. A claim about distance sets should cite that completed proof, not this audit alone.

## Geometry from admissibility

Write $R=2^N$ and consider an admissible profile edge $n\to m$, where $0\le m<n\le N$ and $2n-m\le N$. Put

$$
r=R2^{-n},\qquad r'=R2^{-m},\qquad
\delta=1/r,\qquad \rho=r/r'=2^{m-n},\qquad
\delta_*=R^{-1/2}.
$$

Two independent consequences of admissibility are

$$
\delta\le\rho
$$

and

$$
n-m\le\min\{n,N-n\}\le N/2,
\qquad \delta_*\le\rho.
$$

Thus the effective angular uncertainty

$$
\bar\delta=\max\{\delta,\delta_*\}
$$

fits the conditional tube aspect ratio at every edge, even after $r>R^{1/2}$. The latter inequality follows from the same admissibility condition, rather than from an added forced-midpoint hypothesis.

A fine-cap dual tube has width $r/R$, length $r'/R$, and direction given by a fine-cap center. Changing that direction by $O(\delta_*)$ changes its transverse extent by at most

$$
O(\delta_*r'/R)\le O(r/R).
$$

It is therefore contained in a constant enlargement of the corresponding tube in the standard-cap direction. The same statement holds before the standard scale with angular uncertainty $O(\delta)$.

## Smooth multipliers must be chosen in the correct order

First fix the ordinary smooth standard-cap multipliers $\psi_\beta$ of angular width $\delta_*$. Their derivative bounds are those needed for the usual physical source-packet localization.

At coarser auxiliary levels, group standard labels into angular blocks with the desired support width. Their sums are only used as spectral functions. At finer auxiliary levels, use exact partitions of the form

$$
\psi_\beta\chi_\alpha,
\qquad \sum_{\alpha}\chi_\alpha=1
$$

within each fixed standard root $\beta$. Finer labels must retain this standard-root index. Further refinement can be obtained by nested smooth partitions, with bounded overlap constants depending on the fixed chain length $K$.

One must **not** define the standard multiplier by sharply grouping a pre-existing finest partition. That construction could give standard multipliers transition widths much smaller than $R^{-1/2}$ and destroy the required physical packet localization. Fixing $\psi_\beta$ first and multiplying it by finer spectral partitions avoids this problem.

## Marks and spatial inheritance

At a coarse auxiliary level, use the corresponding coarse angular ancestor to define a bad mark. At a level finer than the standard scale, use the standard ancestor $\beta$ instead. For a fixed spatial child cube, every fine descendant of a given effective ancestor receives the same mark.

Marks are tested against the same normalized conditional pin measure and the same enlarged parent used in the original one-step estimate. Descendant spatial cubes inherit their ancestors' marks. Consequently, at the initial spatial cube $Q_0$, the removed labels are a union of whole standard labels $\beta$.

The dependency on spatial ancestors causes no algebraic problem: for a fixed parent cube, all its future marks are fixed; current marks only select which child angular labels occur. With the root label retained, the identity

$$
F_{Q_j,\alpha_{j-1}}
=
\sum_{\substack{\alpha_j\text{ child of }\alpha_{j-1}\\
\alpha_j\text{ good for }Q_j}}
F_{Q_{j+1},\alpha_j}
$$

is an exact partition identity. The summands on its right depend on the parent cube and fine label, not on the child spatial cube. After the standard scale, a current mark may retain or delete many fine children together; this does not alter the identity.

## Packet replacement and the bad part

Define the physical good source function using the ordinary standard spatial packets: for a marked standard label, delete its packets that meet the prescribed enlargement of $Q_0$. All packets of an unmarked standard label are retained. The packets of a marked label that do not meet that enlargement have rapidly small extensions on $Q_0$. Thus the existing standard packet-extension localization gives the sum of the retained whole standard circular cap functions on $Q_0$, up to rapidly decreasing error.

Only after that identity is established, subdivide each retained standard circular function spectrally into its fine auxiliary pieces. This is exact. There is no claim that an individual spatially cut source packet has fine-cap Fourier support, and no such claim is needed.

The bad-part first-norm estimate is consequently still summed over standard physical packets only. For a fixed separated source-pin pair, their multiplicity remains the standard $R^{O(h)}$ bound. No factor counting fine descendants of a standard cap occurs.

To compare a bad effective-cap mark with the conditional tube deletion lemma, its direction uncertainty is $O(\bar\delta)\le O(\rho)$. Thus it is contained in the same type of discretized conditional tube and associated source-direction interval used in that lemma. All enlargement factors are covered by its existing $R^{O_K(h)}$ allowances. This applies independently to every edge and then to their finite union.

## Fine spectral support and spatial tails

For a fine label at scale $r$, the circular Fourier support has tangential width $O(R/r)$ and normal width $O(R/r^2)$. Admissibility gives $r'\le r^2$, so the latter is at most $O(R/r')$.

The fixed compactly supported frequency convolution used in the circular functions adds only bounded width. It is harmless because $r\le r'\le R$, hence both target widths $R/r$ and $R/r'$ are at least one. Thus even the last fine auxiliary labels have frequency rectangles of the required size.

Fine-cap centers are separated at tangential frequency scale $R/r\ge1$. Fixed convolution and the bounded-overlap root labels therefore preserve bounded overlap, with constants depending on $K$, rather than producing a power of $R$.

The local orthogonality and local-constancy steps use these exact spectral supports, not fine physical source packets. Their spatial tails come from the same smooth averaging kernels as in the original proof. A rapidly decreasing tail may be multiplied by the polynomial number of fine labels, cubes, and standard packets; choosing its decay order sufficiently large absorbs that count.

## Conditional tube weights

Fix a parent cube and a fine label. Every fine-label dual tube is contained in a bounded enlargement of the effective-ancestor test tube whenever it contains a good child. Therefore the sum of the masses of the contributing enlarged good children is bounded by

$$
R^{O_K(h)}H_j\rho\,\sigma(Q_{j+1}^{+}).
$$

This is the original good-tube inequality with the same conditional normalization. The local-constancy comparison contributes the reciprocal area ratio $1/\rho$, so the one-step loss remains $H_j$.

There is no factor for the number of fine labels inside a standard cap: local orthogonality sums their nonnegative squared norms, and the same one-step bound is applied to each. The eventual Plancherel bound sums fine multipliers with bounded overlap. Its circle-mass factor remains $O(R^{-1})$.

## Consequence conditional on the completed analytic transfer

If the modified construction is integrated into the full packet, inflation, and summation proof, it permits a profile chain without the forced midpoint. In the range $b\ge1/2$, the previously proved unforced profile cost is

$$
\frac{b-a}{1+2b}.
$$

Putting $a=s-1$ and $b=u-1$, strict summability would then require

$$
\frac{u-s}{2u-1}<s-1,
$$

or, for $s<3/2$,

$$
u<\frac{1}{3-2s}.
$$

This last formula is an algebraic consequence of the proposed analytic modification. It is not a stand-alone proof of the corresponding distance-set theorem and is not asserted to be optimal.
