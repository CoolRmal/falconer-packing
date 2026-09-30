# Critical covering examples without regular subsets

Date: 2026-09-30. This note proves the explicit Moran construction for the variable-exponent coherent endpoint criterion and independently checks that varying the comparison exponent is legitimate.

For every

$$
1<d\le\frac32,\qquad D=2d-1,
$$

there is a compact K⊂[0,1]² and a probability μ on K such that

$$
0<\mathcal H^d(K)<\infty,\qquad
\dim_HK=d,\qquad \dim_PK=D,
\tag{1}
$$

$$
\mu(B(x,r))\le C r^d,\qquad
N(K,r)\le C r^{-D}\exp\!\left(-c\sqrt{\log(1/r)}\right)
\tag{2}
$$

for sufficiently small r>0. Moreover, every subset S⊂K satisfies

$$
\boxed{\quad \dim_HS\le\frac dD\dim_PS.\quad}
\tag{3}
$$

Thus K contains no subset of positive dimension whose Hausdorff and packing dimensions agree. The endpoint coherent criterion nevertheless gives positive-length pinned distances from K for μ-almost every pin in K. This is an endpoint example under the extra covering gauge (2), not a theorem for every set with dimensions d and D.

## 1. Integer branching function

Fix A>0 and define

$$
U(n)=Dn-A\sqrt{n+1}.
$$

Choose a large integer a_0 so that for every n≥a_0,

$$
U(n)-dn>10,\qquad 0<U(n+1)-U(n)<2.
\tag{4}
$$

This is possible because D>d and D≤2. For D=2 the square-root term still makes the upper-barrier increments strictly smaller than two.

Set F(a_0)=2⌈da_0/2⌉. Increasing a_0 if necessary ensures F(a_0)≤2a_0. Choose an initial path from F(0)=0 to this value, with every increment in {0,2}.

Starting at a_{j−1}, set

$$
F(n)=F(a_{j-1})+2(n-a_{j-1})
$$

until its first crossing of U: let b_j be the smallest integer larger than a_{j−1} for which this value is at least U(b_j). The crossing is finite. For D<2 the difference of the growing line and U tends to infinity linearly; for D=2 that difference is a fixed constant plus A√(n+1). By the first-crossing property and (4),

$$
U(b_j)\le F(b_j)<U(b_j)+2.
\tag{5}
$$

Next keep F constant until the lower line dn first catches it. Namely, let a_j be the smallest integer greater than b_j satisfying da_j≥F(b_j), and set F(n)=F(b_j) for b_j≤n≤a_j. Then

$$
da_j-d<F(a_j)\le da_j.
\tag{6}
$$

Both phases have positive length because their barriers are separated by more than ten. Thus a_j,b_j tend to infinity. Every increment of F is 0 or 2, and throughout the construction

$$
dn-2\le F(n)\le Dn-A\sqrt{n+1}+2
\quad(n\ge a_0).
\tag{7}
$$

For the lower bound, the growing slope exceeds d and the flat phase stops within one integer step of the lower line. For the upper bound, use (5) and monotonicity of U.

The exact flat-phase identity F(a_j)=F(b_j), together with (5)–(6), gives

$$
da_j=Db_j-A\sqrt{b_j+1}+O(1),
\qquad
\frac{a_j}{b_j}\longrightarrow\frac Dd>1.
\tag{8}
$$

No asymptotic formula for the growing-phase lengths is needed.

## 2. Compact dyadic set and natural measure

Use the same rule at every occupied planar dyadic square at depth n:

- if F(n)−F(n−1)=2, retain all four children;
- otherwise retain only the lower-left child.

Equal conditional child weights give a probability μ on the compact intersection K. There are exactly 2^{F(n)} symbolic depth-n cells, each with mass 2^{-F(n)}.

After every fixed depth there are infinitely many zero-increment depths, by the flat phases. Hence an admissible coordinate tail cannot consist entirely of ones. This excludes the alternative upper-endpoint binary expansion of a dyadic rational. The usual half-open dyadic partition assigns every point of K an unambiguous admissible address, with the indicated cell mass. Equivalently, descendants in each fixed closed construction square stay below its upper edges because of a subsequent common zero digit. This handles boundary points without removing points from K.

A ball of radius 2^{-n} meets a bounded number of dyadic depth-n cells. Thus (7) gives

$$
\mu(B(x,2^{-n}))\le C2^{-F(n)}\le C2^{-dn}.
\tag{9}
$$

The finite initial segment changes only C, and adjacent dyadic scales give the d-Frostman estimate for every radius.

The occupied-cell count also gives

$$
N(K,2^{-n})\le C2^{Dn-A\sqrt{n+1}}.
\tag{10}
$$

A fixed shift of dyadic depth accounts for square diameter. Comparison with adjacent dyadic scales proves the second bound of (2), with some c>0.

## 3. Exact Hausdorff measure and packing dimension

The d-Frostman estimate implies H^d(K)>0. At flat endpoints a_j, the full cell cover has d-dimensional cost

$$
2^{F(a_j)}\left(\sqrt2\,2^{-a_j}\right)^d
=2^{d/2}\,2^{F(a_j)-da_j}\le2^{d/2}.
\tag{11}
$$

These cover diameters tend to zero, so H^d(K)<∞ and dim_H K=d.

The upper covering bound gives upper box dimension and packing dimension at most D. At the growing endpoints,

$$
F(b_j)=Db_j-A\sqrt{b_j+1}+O(1),
\qquad
\sup_x\mu(B(x,2^{-b_j}))\le C2^{-F(b_j)}.
$$

Thus every E⊂K with positive μ outer measure satisfies

$$
N(E,2^{-b_j})\ge c\,\mu^*(E)\,2^{F(b_j)},
$$

and has upper box dimension at least D. Any countable cover of K contains a member of positive μ outer measure. The countable-cover characterization of packing dimension therefore gives dim_P K≥D, proving (1).

## 4. The hereditary dimension inequality

Let S⊂K be arbitrary, without a measurability assumption, and put v=dim_P S. For ε>0, the countable-cover characterization supplies a cover by S_i⊂K with upper box dimension at most v+ε. Intersecting the original cover pieces with K does not increase upper box dimension.

For each fixed i and sufficiently large j,

$$
N(S_i,2^{-b_j})\le2^{(v+2\epsilon)b_j}.
\tag{12}
$$

Replace each ball by the bounded number of depth-b_j dyadic cells it meets. Between depths b_j and a_j there is no branching. Every occupied depth-b_j cell has exactly one occupied depth-a_j descendant. Therefore S_i is covered by at most C2^{(v+2ε)b_j} squares of side 2^{-a_j}.

If t>(d/D)(v+2ε), (8) shows that the t-dimensional cost tends to zero:

$$
C2^{(v+2\epsilon)b_j}
 \left(\sqrt2\,2^{-a_j}\right)^t\longrightarrow0.
$$

Hence dim_H S_i≤(d/D)(v+2ε). Countable stability of Hausdorff dimension and ε↓0 prove (3). Since d/D<1, K contains no positive-dimensional subset of equal Hausdorff and packing dimension.

## 5. Audit of the variable-exponent coherent criterion

Let μ be any compact d-Frostman probability and the pin probability have Frostman exponent greater than one. Choose the coherent centers and affine densities f_n once, using the averaged angular exponent q>1. Neither depends on the Sobolev comparison exponent.

For sufficiently large n, put

$$
\gamma_n=\frac{d-1-1/n}{2},\qquad
\tau_n=1+2\gamma_n=d-\frac1n,\qquad r=2^{-n}.
\tag{13}
$$

When 1<d≤3/2, these γ_n lie in a fixed compact subinterval of (0,1/2). The angular comparison constants are uniform there: Fourier interpolation, the angular Slobodeckij estimates, the translation inequality, and the Riesz energy constants remain bounded on that compact interval. The selected center angular moments and the bad-pin estimate do not depend on γ_n.

The conditional Frostman calculation gives, for each source child Q of mass p_Q,

$$
I_{\tau_n}(\mu_Q)
\le\frac{C}{p_Q(d-\tau_n)}\,r^{d-\tau_n}
\le\frac{Cn}{p_Q}r^{1/n}.
\tag{14}
$$

The only unbounded factor is the displayed n. With N_{n+1} occupied child squares,

$$
\begin{aligned}
Z_n(\gamma_n)
&=r^{1+4\gamma_n}\sum_Qp_QI_{\tau_n}(\mu_Q)\\
&\le Cn\,r^{2d-1-1/n}N_{n+1}\\
&=2Cn\,2^{-n(2d-1)}N_{n+1}.
\end{aligned}
\tag{15}
$$

The identity r^{-1/n}=2 is essential: no scale-exponential loss appears. Optimizing the angular threshold separately at each n gives convergence if

$$
\sum_n
\left[n\,2^{-n(2d-1)}N_{n+1}\right]^{(q-1)/(2q-1)}
<\infty.
\tag{16}
$$

The same affine sequence is used throughout; these are not unrelated approximation schemes.

For the constructed K,

$$
n\,2^{-nD}N_{n+1}\le Cn\,2^{-A\sqrt{n+2}},
$$

so (16) converges for every positive angular exponent (q−1)/(2q−1). The natural measure is d-Frostman. Neither a logarithmic improvement to its ball bound nor finite critical energy I_d is needed.

For separated source and pin supports the endpoint coherent argument gives absolute continuity of the raw joint law. For self-pins ν=μ, cover the complement of the diagonal by countably many products of separated compact rational balls, as in the established coherent Borel reduction. Positive normalized restrictions retain the d-Frostman and occupied-count bounds, with constants depending on the restriction. The diagonal has zero μ×μ mass. Thus the full raw joint law is absolutely continuous and μ-almost every pinned distance set has positive length.

For 1<d≤(7−√7)/4 these examples lie exactly at D=2d−1, the strict boundary of the previous dimension-only branch. More strongly, every subset S⊂K with h=dim_H S>1 satisfies

$$
\dim_P S\ge(D/d)h\ge2h-1=B_H(h),
\qquad
(D/d)h-(2h-1)=1-h/d\ge0.
$$

Thus the previous strict sufficient condition cannot be recovered by first passing to any such subset. The extra covering gauge is essential. No assertion is made that every set at that dimensional endpoint has positive-length pinned distances.
