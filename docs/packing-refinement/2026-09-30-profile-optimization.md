# A sharper forced-midpoint profile estimate

30 September 2026. This note proves an elementary chain estimate. Its application to pinned distance sets is **conditional on a separate valid analytic transfer theorem**. It does not establish an optimal distance-set condition.

## Statement

Let a real number $N>0$ and parameters satisfy

$$
0<a\le b\le\frac12.
$$

Suppose $g:[0,N]\to\mathbb R$ is 1-Lipschitz and

$$
ax\le g(x)\le bx.
$$

For $m<n$, write

$$
c_g(m,n)=g(m)-\min_{x\in[m,n]}g(x).
$$

An edge from $n$ down to $m$ is admissible when $2n-m\le N$.
For each fixed $n_0\in[N/2,N)$ there is an admissible decreasing chain from $n_0$ to $N/2$, then to zero, of length

$$
K\le C\left(1+\log\frac N{N-n_0}\right),
$$

and total cost at most

$$
\boxed{\left[\frac{1+2b-4a}{8}
       +\frac{b-a}{2(1+a)}\right]N.}
\tag{1}
$$

The constant $C$ is absolute. If $g$ is piecewise linear on a grid of mesh $T$, $N/2$ and $3N/4$ are grid points, and $n_0$ is a grid point, one can choose grid endpoints and replace the right side by itself plus $O(T)$.

The former forced-midpoint estimate, in this range of parameters, was

$$
\left[\frac{1/2-a}{2}+\frac{b-a}{2(1+a)}\right]N.
$$

The gain is exactly $(1/2-b)N/4$.

## Proof on a grid

Put $l=N/2$, $r=3N/4$, and

$$
\alpha=\frac{b-1/2}{2}N,
\qquad L(x)=x-\frac N2+\alpha-g(x),
\qquad V(x)=\frac{L(x)_+}{2}.
$$

For $x\in[l,N]$, since $b\le1/2$,

$$
g(x)\le bx\le\frac{x}{2}+\alpha.
\tag{2}
$$

The function $L$ is nondecreasing because $g$ is 1-Lipschitz. Also $L(l)=\alpha-g(l)<0$. Almost everywhere on $\{L\ge0\}$,

$$
(-g')_+\le\frac{1-g'}2=V'.
\tag{3}
$$

Indeed, if $g'\ge0$, the right side is nonnegative; if $g'<0$, the inequality is equivalent to $g'\ge-1$.

If $n_0\le r$, skip the next two paragraphs. Otherwise let $q$ be the largest grid point in $[l,N]$ with $L(q)\le0$, setting $q=N$ when appropriate. In the region $L>0$, move from $n_0$ toward $\max\{r,q+T\}$ by the rule

$$
n\longmapsto\max\{r,q+T,2n-N\},
$$

whenever its target is below $n$. Such edges are admissible. Apart from the final edge, the complementary depth $N-n$ doubles. On each of these edges (3) and

$$
c_g(m,n)\le\int_m^n(-g')_+\,dx
$$

show that their total cost is at most $V(n_0)$. If this procedure reaches $q+T>r$, take the additional edge to $q$; its cost is at most $T$. The only cases in which this extra edge is needed have $q+T<N$, so the grid edge is admissible. We have either reached $n\le r$, or reached a grid point with $L(n)\le0$.

For a current point $n>r$ with $L(n)\le0$, put $m_0=2n-N>l$. The envelope (2) gives

$$
g(m_0)\le\frac{m_0}{2}+\alpha
       =n-\frac N2+\alpha\le g(n).
$$

Choose the leftmost grid minimizer $m$ of $g$ on $[m_0,n]$. This satisfies $m<n$ (if $n$ is a minimizer, then $m_0$ has value at most its value) and yields an admissible zero-cost edge. Monotonicity of $L$ keeps all later endpoints in $\{L\le0\}$. Iterate until $n\le r$. This takes finitely many steps on the grid. Greedily merge consecutive zero-cost edges whenever their union is admissible. A union of consecutive zero-cost edges remains zero-cost. For any two consecutive unmergeable edges, the complementary depth more than doubles across those two edges. Therefore the number of retained zero-cost edges is $O(1+\log(N/(N-n_0)))$.

We have reached a point $n\in[l,r]$ at a cost of at most $V(n_0)+T$. The edge $n\to l$ is admissible. Set $v=g(l)$. For every $x\ge l$,

$$
g(x)\ge\max\{ax,v-(x-l)\}
       \ge\frac{a(v+l)}{1+a}.
$$

Thus this final edge has cost at most

$$
v-\frac{a(v+l)}{1+a}
=\frac{v-al}{1+a}
\le\frac{b-a}{2(1+a)}N.
\tag{4}
$$

The final edge $l\to0$ has zero cost since $g\ge0$. Finally, monotonicity of $L$, the lower endpoint bound $g(N)\ge aN$, and $a\le b\le1/2$ give

$$
V(n_0)\le V(N)
\le\frac{\big((1/2+b)N/2-aN\big)_+}{2}
=\frac{1+2b-4a}{8}N.
\tag{5}
$$

The positive part can be omitted because $1+2b-4a\ge1-2b\ge0$. Equations (4)–(5) prove (1), up to the claimed grid error. The positive-cost doubling part, the possible one-grid edge, and the compressed zero-cost part give the length estimate.

## Continuous profiles and approximate barriers

For a continuous profile, interpolate it on grids whose mesh tends to zero and which contain $0,N/2,3N/4,N$. If $n_0$ is not a grid point, first replace it by a grid point immediately below it; the one additional edge from $n_0$ costs at most the mesh and is admissible for sufficiently small mesh. The interpolants remain 1-Lipschitz and retain both linear barriers. Their uniform error tends to zero. The chain-length bound is uniform. Pad endpoint vectors by repetitions, extract a convergent subsequence, and remove repeated endpoints. Interval minima depend continuously on the profile and endpoints in the uniform topology. Admissibility is closed. This proves the exact real-endpoint bound (1).

If the barriers have an additive error $eN$, clamp the profile between $ax$ and $bx$ and interpolate grid values. The clamped profile remains 1-Lipschitz: minimum and maximum of 1-Lipschitz functions are 1-Lipschitz. Its uniform change is at most $eN+O(T)$. Each edge cost changes by at most twice that uniform error. The resulting total error is $O(KeN+KT)$.

## Conditional consequence for the existing notation

Set $a=s-1$, $b=u-1$, where $1<s\le u\le3/2$. The improved profile exponent is

$$
C(s,u)=\frac{2u-4s+3}{8}+\frac{u-s}{2s}.
$$

It satisfies

$$
C(s,u)<s-1
\quad\Longleftrightarrow\quad
u<\frac{s(12s-7)}{2s+4}.
\tag{6}
$$

This right side exceeds $2s-1$ exactly when

$$
s>\frac{13+\sqrt{41}}{16}\approx1.212695265.
$$

It reaches $3/2$ at the same transition as the former middle branch,

$$
s=\frac{5+\sqrt{97}}{12}\approx1.237404817.
$$

For example, at $s=61/50$ and $u=36/25$ (that is, $s=1.22$, $u=1.44$),

$$
C(s,u)=\frac18+\frac{11}{122}
=\frac{105}{488}
<\frac{11}{50}=s-1.
$$

The margin is $59/12200$. By continuity, (6) also allows some $u>2s-1$. These are rigorously improved **profile parameters**, not an independently verified pinned-distance theorem.

## What is not proved

This estimate is not known to be minimax sharp, even in the finite-profile model. An exact two-collapse example at $a=1/5$, $b=1/2$ has cost $9/40$, while (1) only gives $11/40$. The analytic construction converting profile costs to a Fourier estimate also requires a separate audit. Neither a global optimality claim nor a counterexample to a distance-set conclusion follows from these profile calculations.

## A stronger estimate in one additional profile subcase

The following auxiliary observation applies to $1/2\le b<1$ and normalized $N=1$. It is not a universal replacement for (1), because its location hypothesis on a minimum need not hold.

Suppose $t\in[1/2,3/4]$ is a global minimizer of $g$ on $[1/2,1]$. Put

$$
m=g(t),\qquad v=g(1/2),\qquad e=g(1).
$$

For $n_0\in[t,1)$ a forced-midpoint chain can be constructed with cost at most

$$
v-m+\min\left\{\frac{b-e}{1+2b},
                         \frac{1-e-t+m}{3}\right\}.
\tag{7}
$$

As before, its length is bounded by an absolute multiple of $1+\log(1/(1-n_0))$, with grid errors when using grid endpoints.

To prove (7), use the upper envelope

$$
H(z)=\min\{bz,m+z-t\},\qquad z\ge t,
$$

and define

$$
L(x)=H(2x-1)-g(x),\qquad x\ge (1+t)/2.
$$

Since $H$ has slopes $1$ and $b\ge1/2$, $L$ is nondecreasing. Also $L((1+t)/2)=m-g((1+t)/2)\le0$. The same doubling and zero-cost continuation argument as above reaches $n\le(1+t)/2$. Its jump to $t$ is free because $t$ is a global minimum. Finally $t\to1/2$ is admissible because $t\le3/4$, and costs $v-m$.

It remains to estimate the positive-cost part. Write

$$
z_* = \frac{t-m}{1-b},\qquad x_* = \frac{1+z_*}{2}.
$$

Since $m\le bt$, we have $z_*\ge t$. If $z_*\ge1$, then $H(z)=m+z-t$ throughout the relevant interval. The negative variation is bounded by $L'/3$, so its total cost is at most $(1-e-t+m)/3$.

If $z_*\le1$, the corresponding derivative bounds are $L'/3$ before $x_*$ and $L'/(1+2b)$ afterward. Thus the cost is at most

$$
\frac{b-e}{1+2b}
-\left(\frac1{1+2b}-\frac13\right)L(x_*)_+.
\tag{8}
$$

The Lipschitz estimate from $x=1$ gives

$$
g(x_*)\le e+1-x_*,\qquad
L(x_*)\ge\left(b+\frac12\right)z_*-e-\frac12.
$$

Substitution into (8), separating the two signs of the last expression, gives exactly the minimum in (7). In the case $z_*\ge1$, the cone bound is the smaller of the two displayed bounds, so the same formula holds.

For profiles in this subcase, maximizing (7) under the available scalar constraints gives the useful estimate

$$
\frac{b-a}{2(1+a)}
+\min\left\{\frac{b-a}{1+2b},
             \frac{(1-a)(1-t_*)}{3}\right\},
\qquad t_* =\frac{1+b}{2(1+a)},
\tag{9}
$$

when $t_*\le3/4$. Here is the scalar optimization: replace $e$ by $a$, use $v\le\min\{b/2,m+t-1/2\}$ and $m\ge at$. For fixed $t\le t_*$ the expression is maximized at $m=b/2-t+1/2$, and increases with $t$. For fixed $t\ge t_*$ it is maximized at $m=at$, and decreases with $t$. The maximum therefore occurs at $t=t_*$ and $m=at_*$. The displayed upper bound is still valid when the maximizing scalar data are not realizable by an actual profile.

For $a=1/5,b=1/2$, (9) equals $9/40$, matching the explicit two-collapse example. But profiles whose global tail minimum occurs after $3/4$ are not covered by this argument. A direct jump from such a minimum to $1/2$ violates curvature admissibility. Using a crude variation bound to cover that remaining case destroys the numerical gain. Consequently (9) must not be substituted for the universal profile exponent without an additional argument.
