# Finite critical measures do not supply the covering deficit by restriction

Date: 2026-09-30. This note addresses a specific possible upgrade of the critical covering theorem: extracting a source with its required covering deficit from finiteness of critical Hausdorff or packing measure. It gives an explicit obstruction to that extraction. It is not a null-distance construction and does not disprove a dimension-only distance theorem.

## 1. Statement

For every

$$
1<d<\frac32,\qquad D=2d-1<2,
$$

there is a compact planar set K with a probability measure mu such that

$$
0<\mathcal H^d(K)<\infty,\qquad
0<\mathcal P^D(K)<\infty,
\qquad
\dim_H K=d,\qquad\dim_P K=D,
\tag{1}
$$

and the two normalized critical measures both equal the natural probability:

$$
\frac{\mathcal H^d|_K}{\mathcal H^d(K)}
=\mu
=\frac{\mathcal P^D|_K}{\mathcal P^D(K)}.
\tag{2}
$$

In particular the source has an ordinary d-Frostman bound. There are infinitely many depths tending to infinity such that for every subset of positive mu outer measure,

$$
N(S,2^{-b_j})\ge c\mu^*(S)\,2^{Db_j}.
\tag{3}
$$

Consequently no such subset can satisfy any all-scale vanishing covering deficit of the form

$$
N(S,2^{-n})\le C2^{Dn}w(n),\qquad w(n)\longrightarrow0.
\tag{4}
$$

This rules out both the subpower margin used in the endpoint examples and the no-log covering summability certificate

$$
\sum_n\left[2^{-nD}N_{n+1}(S)\right]^\eta<\infty,
\qquad\eta>0,
\tag{5}
$$

where the count is of occupied dyadic squares. The summands fail to tend to zero along the peak depths, with an index shift of one. It also rules out the older certificate with an additional factor n.

More strongly, no compactly supported nonzero Frostman source of any exponent greater than one inside K can satisfy the corresponding no-log critical covering certificate for its exponent. The same is true for the stronger weighted version using the square of the sum of the square roots of the cell masses; its proof appears at the end of Section 5. Thus selecting countably many restrictions, changing to a different critical Frostman source, or choosing a smaller source exponent does not supply either missing certificate.

## 2. The homogeneous dyadic construction

Use the branching construction from the endpoint example, but replace its upper barrier by the exact line

$$
U(n)=Dn.
$$

Choose a sufficiently large initial depth and an even integer branching count within two of the lower line. Thereafter grow the count in increments of two until first meeting the upper line, then keep it constant until the lower line first catches it. Denote the successive upper and lower stopping depths by the following symbols:

$$
b_j<a_j<b_{j+1}<a_{j+1}<\cdots.
$$

Every growing phase terminates because its slope is two and D is strictly below two. The two barriers are eventually separated by more than ten, so every flat phase has positive length. First-crossing and first-catching give

$$
Db_j\le F(b_j)<Db_j+2,
\qquad
da_j-d<F(a_j)=F(b_j)\le da_j.
\tag{6}
$$

In particular

$$
dn-2\le F(n)\le Dn+2
\tag{7}
$$

after the finite initial range, and

$$
\frac{a_j}{b_j}\longrightarrow\frac Dd.
\tag{8}
$$

At each depth retain all four planar dyadic children if the count increment is two, and otherwise only the lower-left child. Apply the same choice at every occupied square. The compact limit is K, and equal conditional weights define mu.

There are infinitely many common forced-zero depths after every fixed depth. Therefore no admissible binary coordinate tail can consist entirely of ones. This removes the dyadic endpoint ambiguity: each symbolic depth-n cylinder lies in its unique half-open dyadic square and has mass exactly

$$
2^{-F(n)}.
$$

The number of cylinders is exactly the reciprocal of this mass. These cylinders are compact, disjoint, and relatively open in K, and their diameters tend to zero.

## 3. Hausdorff measure and exact comparison with the natural probability

The lower bound in (7) and the bounded number of dyadic squares met by a ball at comparable scale give

$$
\mu(B(x,r))\le Cr^d.
\tag{9}
$$

The mass distribution principle gives positive critical Hausdorff measure. At the flat endpoints, the full square cover has critical cost

$$
2^{F(a_j)}(\sqrt2\,2^{-a_j})^d
\le2^{d/2},
$$

so the critical Hausdorff measure is also finite and the Hausdorff dimension is d.

There is an exact, rather than merely comparable, relation to the natural probability. At any fixed depth all cylinders are translates of one common scaled tail set. Thus they have equal Hausdorff measure. They are disjoint Borel sets whose union is K, and the measure of K is finite and positive. Each cylinder consequently has the fraction

$$
2^{-F(n)}
$$

of the total Hausdorff measure. These cylinder sets generate the Borel sigma algebra of K. Uniqueness of finite measures proves the first equality in (2).

## 4. Finite positive critical packing measure

The upper bound in (7) supplies a lower mass bound at every point of K:

$$
\mu(B(x,r))\ge c r^D,
\qquad x\in K,\quad 0<r<r_0.
\tag{10}
$$

Indeed choose a dyadic depth whose whole containing cylinder has diameter at most r and side comparable to r. That cylinder is inside the ball and has mass at least a constant times r to the power D.

For any disjoint family of sufficiently small balls centered in K, (10) bounds the sum of their D-dimensional diameter powers by a constant times the sum of their mu masses, which is at most one. Hence the D-dimensional packing premeasure, and therefore packing measure, of K is finite.

For positivity, the upper hitting times have a matching upper mass estimate at their common scale:

$$
\sup_x\mu(B(x,C_0 2^{-b_j}))\le C(C_0)2^{-Db_j}
\tag{11}
$$

for each fixed geometric factor. This follows by counting the bounded number of depth-b_j squares met by such a ball and using (6).

Let S be any subset of K. Take a maximal family of points in S mutually separated by more than twice the peak radius. The balls of that radius about them are disjoint, while the balls of twice that radius cover S. Using outer measure and (11), the number of balls is at least a constant times

$$
\mu^*(S)\,2^{Db_j}.
$$

Their total D-dimensional packing cost is therefore at least a constant times mu outer measure of S, uniformly in j. Letting j tend to infinity shows

$$
\mathcal P^D_0(S)\ge c\mu^*(S).
$$

Apply this inequality to every member of a countable cover of K and use countable subadditivity of outer measure. The packing outer-measure definition gives

$$
\mathcal P^D(K)\ge c>0.
$$

Thus the packing dimension is D. The same cylinder symmetry used for Hausdorff measure applies to the finite positive Borel packing measure, giving the second equality in (2). Different standard normalizations of packing measure change its total value, not this normalized identity.

## 5. All-source and countable-restriction quantifiers

Estimate (11) immediately proves (3) by applying it to any ball cover of S. A positive-mass restriction of mu, critical Hausdorff measure, or critical packing measure therefore cannot have a support satisfying (4) or (5).

The obstruction also applies to a different d-Frostman source. If a finite nonzero measure eta supported in K obeys

$$
\eta(B(x,r))\le C_\eta r^d,
$$

then the covering definition of Hausdorff measure gives

$$
\eta\ll\mathcal H^d|_K\ll\mu.
$$

Consequently its compact support has positive mu measure, and (3) applies. This is why changing the source probability cannot circumvent the obstruction at the critical exponent. More generally, every positive eta restriction has positive mu outer measure on any set carrying its mass.

For a countable family of restrictions covering positive mu mass, at least one member has positive mu outer measure. In fact each member having positive mass separately obeys (3). No decomposition into pieces with the desired deficit can therefore cover the source up to a null set.

To include sources of smaller exponent, use the following hereditary inequality, proved exactly from the flat intervals:

$$
\dim_H S\le\frac dD\dim_P S
\qquad(S\subset K).
\tag{12}
$$

Here is the argument. Cover S by sets whose upper box dimensions are at most its packing dimension plus a tolerance. At depth b_j their covering counts are at most the corresponding exponential in b_j. Since no branching occurs between b_j and a_j, the same number of depth-a_j squares covers each piece. Equation (8) gives its Hausdorff dimension at most d divided by D times its upper box bound. Countable stability and a vanishing tolerance prove (12) for arbitrary subsets.

Suppose eta is a probability of Frostman exponent s greater than one with compact support S inside K. Necessarily s is at most d. If it is strictly smaller, (12) gives

$$
\dim_P S\ge\frac Dd\dim_H S\ge\frac Dd s
=2s-\frac sd>2s-1.
$$

But summability of the critical covering certificate at source exponent s would imply an eventual uniform bound on its summands and hence

$$
\overline{\dim}_B S\le2s-1,
$$

a contradiction. At s equal to d, the positive-mu support argument already rules it out. At s greater than d, no such source exists. This proves the claimed quantifier over all Frostman sources and all permissible source exponents.

The flat geometry also gives a shorter direct proof for the stronger weighted certificate from the frequency-band comparison. Let eta be any Frostman probability of exponent s greater than one supported on K. For its depth-n masses define

$$
\mathcal N_n(\eta)=
\left(\sum_{Q\text{ at depth }n}\sqrt{\eta(Q)}\right)^2.
$$

Necessarily s is at most d. At an upper stop, every occupied cylinder has a unique descendant at the following lower stop, and all of its intersection with K lies in that descendant. The source Frostman bound therefore gives

$$
\max_{Q\text{ at depth }b_j}\eta(Q)
\le C_\eta 2^{-s a_j}.
$$

For any probability vector, the sum of square roots is at least the sum of the entries divided by the square root of their maximum. Consequently

$$
\mathcal N_{b_j}(\eta)\ge c_\eta2^{s a_j}.
$$

The stopping identities give a lower bound for the lower stopping depth without an asymptotic error:

$$
da_j\ge F(b_j)\ge Db_j.
$$

Using the critical value of D yields

$$
2^{-(2s-1)b_j}\mathcal N_{b_j}(\eta)
\ge c_\eta
2^{[sD/d-(2s-1)]b_j}
=c_\eta2^{(1-s/d)b_j}.
\tag{12a}
$$

This is bounded below by a positive constant at s equal to d and tends to infinity when s is smaller. With the fixed one-level index shift, it rules out every weighted all-scale series

$$
\sum_n
\left[2^{-n(2s-1)}\mathcal N_{n+1}(\eta)\right]^\eta_0<\infty,
\qquad \eta_0>0.
\tag{12b}
$$

This argument needs neither absolute continuity of the replacement source with respect to mu nor any assumption on its distribution among the peak cells. It applies to every replacement Frostman probability supported on K. The failure concerns all-scale numerical sufficient certificates, and remains compatible with the selected-scale positive result below.

## 6. Interpretation and limitations

The hypotheses of finite positive critical Hausdorff measure and sigma-finite critical packing measure are both present in (1), in the stronger form of finite positive measures. They do not force a positive source restriction satisfying the critical covering certificate or its weighted strengthening, even after changing the source measure. Therefore a dimension-only endpoint under these hypotheses cannot be deduced by this extraction argument alone.

The construction has D strictly below two. At the limiting value D equal to two, positive critical packing measure in the plane is comparable to positive area and is incompatible with finite Hausdorff measure of smaller dimension; thus the stronger finite-positive-two-dimensional-packing formulation would itself be impossible there. The examples above already obstruct the proposed general extraction claim throughout the range relevant to the manuscript's low branch.

These examples are not claimed to have null distance sets. They do not rule out an endpoint proof by geometry-sensitive estimates, adapted partitions, or sharper comparison of the actual affine laws. In particular the actual affine error vanishes along a flat chain if its center is inherited unchanged. A large conditional-energy upper bound at such a transition would not establish a lower bound on the actual approximation error. The obstruction here is to the covering certificate and its extraction from critical measure finiteness.

## 7. A positive sparse-scale result for the same examples

The obstruction to the all-scale certificate coexists with a stronger positive conclusion for a substantial part of this exact construction. The selected-scale comparison in `output/pdf/packing-unforced-sparse-moran.tex` proves raw joint absolute continuity for these zero-gauge examples whenever

$$
1<d<\frac{1+\sqrt{17}}4\approx1.280776,
\qquad D=2d-1.
\tag{13}
$$

The pin measure may be any prescribed compactly supported Frostman probability of exponent greater than one. Separation is removed by countably many separated source–pin restrictions, so this includes the natural self-pin probability. In particular the pinned distance set has positive length for almost every natural pin.

Here is the precise calculation linking that theorem to this construction. Write a for the previous lower stopping depth, b for the next upper stopping depth, and m for the following lower stopping depth. First crossing and catching give

$$
(2-D)b=(2-d)a+O(1),\qquad dm=Db+O(1),
$$

and therefore

$$
\frac ma\longrightarrow
\kappa=\frac{D(2-d)}{d(2-D)}.
\tag{14}
$$

At every lower stopping depth, the occupied count is at most the exponential of d times that depth. For any fixed angular exponent q greater than one and any fixed positive gamma smaller than half of d minus one, the coherent comparison between these selected depths has the bound

$$
\|f_m-f_a\|_{L^1(\nu\times dt)}
\le C2^{-2\gamma\eta_q(2a-m)},
\qquad \eta_q=\frac{q-1}{2q-1}.
\tag{15}
$$

When the ratio in (14) is strictly below two, the curvature gaps are eventually a fixed positive proportion of a. The comparison errors are summable, and the positive affine laws converge in first norm to the raw joint distance law. The equivalence

$$
\kappa<2
\quad\Longleftrightarrow\quad
D<\frac{4d}{d+2}
$$

becomes, upon substituting the critical packing exponent,

$$
2d^2-d-2<0
\quad\Longleftrightarrow\quad
d<\frac{1+\sqrt{17}}4.
$$

Thus every example from this note in the manuscript's low branch has raw absolutely continuous pinned laws despite the failure of every all-scale critical covering extraction described above. At the boundary of (13), this zero-gauge argument does not supply a summable gap. The separate sparse construction inserts a logarithmic deficit into its upper barrier to cover that boundary; the finite positive critical packing-measure assertion in this note is made only for the zero-gauge construction.

The selected-scale proof and its logarithmic boundary construction have been independently checked against the original coherent angular and first-norm comparison argument. The support needed in the first-norm estimate is the union of two intervals of child-scale length; the gap between the intervals does not contribute to its Lebesgue measure. The required translation bound follows directly from the Fourier proof for any translation range, and all source and pin choices remain fixed across the selected scales. The newer frequency-band comparison sharpens the coefficient in the exponent of (15) from twice gamma to d minus one, without changing the recurrence threshold. Root and the critical-endpoint agent independently reviewed the critical-measure, count extraction, and sparse application arguments without finding an error. The critical-endpoint agent also independently checked the weighted refinement (12a)–(12b), including its one-level index shift. No universal dimension-only conclusion follows from this structured positive family.
