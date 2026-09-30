# Exact curvature profiles and an obstruction to selected levels

30 September 2026. This note analyzes the exact positive kernel in [packing-unforced-band-comparison.tex](packing-unforced-band-comparison.tex). Its complete manuscript proof is [packing-unforced-curvature-obstruction.tex](packing-unforced-curvature-obstruction.tex). The source-replacement lower bound and finite-positive-critical-measure example were independently developed and checked in [the all-source curvature note](2026-09-30-all-source-curvature-certificate-obstruction.md).

These are limitations of the sufficient coefficient, not lower bounds for actual approximation errors or counterexamples to positive-length distance sets.

## 1. Exact homogeneous formula

Let the natural homogeneous planar dyadic measure have the following cell count, equal cell masses, and increment bound:

$$
\#\{\text{occupied depth-}k\text{ cells}\}=2^{F(k)},\qquad
\mu(Q)=2^{-F(k)},\qquad 0\le F(k+1)-F(k)\le2.
$$

Write

$$
G(k)=F(k)-k,\qquad H(L)=\sum_{k\ge L}2^{-G(k)}.
$$

For the positive curvature kernel

$$
J_\delta(\lambda)=
\iint\min\{|x-x'|^{-1},\delta^2|x-x'|^{-3}\}\,
d\lambda(x)d\lambda(x'),
$$

the exact comparison coefficient satisfies

$$
\boxed{
W^\mu_{n,m}\asymp 2^{G(m)}H(\max\{m,2n\}),\qquad n<m.
}
\tag{1}
$$

Constants are independent of F,n,m, and the expressions may be infinite.

Indeed, inside a depth-m cylinder the pair-ball mass at radius 2^{-k}, k≥m, is comparable to 2^{F(m)−F(k)}. The upper bound uses bounded dyadic overlap. The lower bound uses pairs in the same depth-(k+1) descendant. Radial layer cake therefore gives

$$
J_{2^{-2n}}(\mu_Q)
\asymp
2^{F(m)}
\sum_{k\ge m}2^{-F(k)}
\min\{2^k,2^{3k-4n}\}.
$$

For k<2n the summands 2^{3k−4n−F(k)} increase at least geometrically, since the increment of F is at most two. This part is bounded by a constant times the first term of the tail beginning at 2n. All cylinders have the same comparable conditional energy, and their weights sum to one, proving (1).

For every replacement source probability η supported on K, not necessarily dominated by μ, the independent all-source lemma gives

$$
W^\eta_{n,m}\ge c\,2^{G(m)}H(\max\{m,2n\}).
\tag{2}
$$

The same lower bound applies to any countable measurable partition into pieces of diameter at most C₀2^{-m}, with a constant depending on C₀. Its proof sums same-descendant indicators in the positive kernel and applies Cauchy–Schwarz to the available descendant masses. In particular the natural probability minimizes these coefficients up to constants among all such choices.

One immediate consequence is

$$
m\ge2n\quad\Longrightarrow\quad W^\eta_{n,m}\ge c.
\tag{3}
$$

Thus jumping past twice the current depth cannot produce a vanishing coefficient.

## 2. Limiting profile functional

Assume F(k)≥(1+a)k−C, a>0, and the normalized profiles converge uniformly along N_j:

$$
\frac{F(N_jx)-N_jx}{N_j}\longrightarrow g(x),
\qquad g(1)=a.
$$

For 0<x<y≤1 with 2x≤1, equation (1) gives

$$
\lim_{j\to\infty}
\frac1{N_j}
\log_2 W^\mu_{\lfloor xN_j\rfloor,\lfloor yN_j\rfloor}
=
g(y)-\min_{\max(y,2x)\le z\le1}g(z).
\tag{4}
$$

Up to depth N_j, the sum lies between its largest summand and N_j+1 times that summand. Beyond N_j the global Frostman barrier bounds the tail by C_a2^{-aN_j}; since g(1)=a this does not change the limiting exponential rate. This proves both inequalities in (4).

The future minimum, rather than just the endpoint value or the number of occupied fine squares, controls the curvature coefficient.

## 3. A barrier that every selected sequence crosses

Suppose integers L_j→∞ and u_j≥2L_j satisfy, for one fixed C,

$$
\min_{L_j<k\le2L_j}G(k)\ge G(u_j)-C.
\tag{5}
$$

For any increasing selected sequence, choose its edge n≤L_j<m. If m≥2n, (3) gives a uniform lower bound. Otherwise m belongs to (L_j,2L_j] and the sum in (2) includes k=u_j, so

$$
W^\eta_{n,m}\ge c2^{G(m)-G(u_j)}\ge c2^{-C}.
$$

Infinitely many distinct edges cross these barriers. Therefore the coefficients fail to tend to zero for every source probability and every permitted sequence of common-depth partitions. Every positive-power summability test fails, as does any weaker criterion that still requires these coefficients to vanish.

This assertion keeps one common pair of depths for each comparison. It does not address heterogeneous source-dependent trees with separate diameters and comparison scales on different branches.

## 4. Testing the sharp profile witnesses

The single-collapse profile is

$$
g(x)=\min\{bx,1+a-x\}.
$$

It has a valley at v=1 of height av. The two-collapse witness is

$$
g(x)=\min\{bx,av+|x-v|,1+a-x\},
$$

with its prescribed v=t∈(0,1). In both cases

$$
g(x)>av\qquad(av/b<x<v).
$$

If b>2a, choose c with av/b<c<v/2. The compact interval [c,2c] lies strictly above the valley. Any fixed-measure realization of the template then has barriers

$$
L_j=\lfloor cN_j\rfloor,\qquad
u_j=\lceil vN_j\rceil,
$$

with an exponentially favorable gap in (5). Thus even arbitrary selected levels cannot make the curvature coefficients vanish. This holds for every replacement source on the realizing support.

At b=2a<1, use the exact catch-up realization. With h(x)=x+g(x), d=1+a, D=1+b, define a new continuous block after endpoint M by

$$
\mathcal F(t)=
\min\{Nh(t/N),\,2t-(2-d)M\}.
$$

For N sufficiently large the two entries meet in the initial linear segment at

$$
t_0=\frac{2-d}{2-D}M<vN/2.
$$

After that meeting the template is the smaller entry, since its slopes are at most two. Hence the realization agrees exactly with the template on [vN/2,N]. Rounding by F(k)=2⌊𝔽(k)/2⌋ adds a uniformly bounded error. The barriers at L_j=⌊vN_j/2⌋ and u_j=⌈vN_j⌉ therefore satisfy (5) with fixed C, including equality b=2a.

Where the matching profile cost is at least a, these same examples have no fixed strict profile-cost margin along their realizing scales and no curvature-coefficient convergence under any common selected levels. This does not rule out a new argument coupling the two approximation schemes.

## 5. Finite positive critical measures do not remove the barrier

The independently checked construction in [the all-source note](2026-09-30-all-source-curvature-certificate-obstruction.md), now fully included in the manuscript fragment, gives such examples for every

$$
1<d<\frac32,\qquad 2d-1\le D<2,
$$

with

$$
0<\mathcal H^d(K)<\infty,\qquad
0<\mathcal P^D(K)<\infty.
$$

Moreover the normalized restrictions of both critical measures are the same natural d-Frostman probability.

Its branching count catches the even upper line V(n)=2⌊Dn/2⌋, follows that line for a long interval, then stays flat until the lower line dn catches it. The plateau is chosen to include [a/2,b], where b is the peak and a the subsequent trough. On this interval,

$$
G(k)\ge(D-1)k-2\ge(d-1)a-2\ge G(a)-2,
$$

using D≥2d−1. On the flat remainder up to a, G(k)≥G(a). Hence every block supplies a crossing barrier with a uniform constant, including the critical equality.

This does not establish failure of raw pinned absolute continuity. These coefficients overestimate actual comparison errors; inherited centers, cancellation, more precise geometric estimates, or genuinely different source–pin selections may still help.
