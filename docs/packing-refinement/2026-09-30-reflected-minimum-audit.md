# Independent audit of the reflected-minimum profile argument

30 September 2026. Audited independently from the reflection derivation supplied by the Fourier-audit agent and the root agent's convex-combination calculation. This audit concerns the elementary profile theorem only. Its analytic transfer to distance sets must be established separately.

## Audit outcome

The reflection argument, the bounded-length terminal chain, and their convex combination are valid. They imply the following sufficient profile condition throughout $0<a\le1/4$:

$$
E(a,b):=\frac{1-2a-2a^2+(2+a)b}{6(1+a)}<a.
$$

In particular, the previously separate late-minimum restriction is unnecessary for this sufficient criterion. Equivalently,

$$
b<\frac{8a^2+8a-1}{a+2}.
$$

This conclusion does not claim that $E$ is the optimal profile cost or that the resulting distance-set condition is optimal.

## Setup and early-minimum ingredient

Let $g:[0,1]\to\mathbb R$ be 1-Lipschitz with $g(0)=0$ and $ax\le g(x)\le bx$, where $0<a\le1/4$ and $a\le b\le1$. Start at $3/4\le n_0<1$. For an edge from $n$ to $p<n$, define

$$
c_g(p,n)=g(p)-\min_{[p,n]}g,
$$

and require $2n-p\le1$. The desired chain is forced through $1/2$ and then zero.

The only early-minimum ingredient needed for the reflection argument is this scalar statement: if a 1-Lipschitz nonnegative profile $h$, with $h(0)=0$, has its global minimum on $[1/2,1]$ at $u\le3/4$, then there is a forced-midpoint chain whose cost is at most

$$
h(1/2)-h(u)+\frac{1-u+h(u)-h(1)}3.
\tag{1}
$$

Its length is $O(1+\log(1/(1-n_0)))$. This statement does not require an upper linear barrier for $h$. It follows from the slope-one cone $h(z)\le h(u)+z-u$ for $z\ge u$, the affine-envelope chain construction, the zero-cost edge to $u$, and the admissible edge $u\to1/2$. The cone term is nonnegative by Lipschitz continuity. These are exactly the hypotheses available for the reflected profile below.

The usual optimization of (1), when $h=g$ and the global tail minimum is early, gives cost at most $E(a,b)$ as proved in `2026-09-30-tail-minimum-split.md`.

## Reflection is 1-Lipschitz

Suppose a global tail minimum of $g$ occurs at $t>3/4$. Choose a minimum $u$ of $g$ on $[1/2,3/4]$ and put

$$
v=g(1/2),\qquad w=g(u),\qquad m=g(t),\qquad e=g(1).
$$

Define

$$
r(x)=
\begin{cases}
0,&x\le u,\\
w-\min_{u\le z\le x}g(z),&x\ge u,
\end{cases}
\qquad h(x)=g(x)+r(x).
$$

The function $r$ is nonnegative and nondecreasing. The second formula is nonnegative because the defining interval includes $u$. For $x\ge u$, one has $h(x)\ge w$.

Here is a direct proof that $h$ is 1-Lipschitz, without differentiating the running minimum. Let $u\le x<y$. Monotonicity of $r$ gives

$$
h(y)-h(x)\ge g(y)-g(x)\ge-(y-x).
$$

If $r(y)=r(x)$, the opposite inequality is the ordinary Lipschitz inequality for $g$. If $r(y)>r(x)$, a new minimum is attained at some $z\in[x,y]$, and

$$
h(y)=g(y)+w-g(z),\qquad h(x)\ge w.
$$

Consequently

$$
h(y)-h(x)\le g(y)-g(z)\le y-z\le y-x.
$$

Thus $h$ is 1-Lipschitz on $[u,1]$. Before $u$ it equals $g$, and both formulas agree at $u$; gluing the two Lipschitz estimates proves the claim on all of $[0,1]$.

Since $u$ minimizes $g$ on $[1/2,3/4]$, we have $h\ge w$ on the whole tail $[1/2,1]$ and $h(u)=w$. Also

$$
h(0)=0,\qquad h(1/2)=v,\qquad h(1)=e+w-m.
$$

The endpoint identity uses $t>3/4\ge u$, so that the minimum of $g$ on $[u,1]$ is exactly $m$. The reflected profile is nonnegative because $g$ and $r$ are nonnegative.

## Transfer of the reflected chain back to the original profile

For every edge $[p,q]$, monotonicity of $r$ yields

$$
\min_{[p,q]}(g+r)\le\min_{[p,q]}g+r(q).
$$

Therefore

$$
c_g(p,q)\le c_h(p,q)+r(q)-r(p).
\tag{2}
$$

Summing (2) along a decreasing chain telescopes. The added cost is $r(n_0)-r(0)\le w-m$; it does not depend on the number of edges. Applying (1) to $h$ gives an available $g$-chain with cost at most

$$
\begin{aligned}
R
&=v-w+\frac{1-u+w-(e+w-m)}3+(w-m)\\
&=v+\frac{1-u-e-2m}3.
\end{aligned}
\tag{3}
$$

The chain retains the forced midpoint and the original logarithmic edge bound. No linear upper barrier for $h$ has been used.

## The second chain and the case of a minimum after the starting point

Every edge satisfies $0\le c_g(p,q)\le q-p$. From any $x>3/4$, repeated edges to $\max\{3/4,2x-1\}$ reach $3/4$, have total cost at most $x-3/4$, and use $O(1+\log(1/(1-x)))$ edges.

If $t\le n_0$, use the slope-one cone based at $(t,m)$ to reach $t$ at cost at most $(1-t+m-e)/3$. Then use the preceding chain to reach $3/4$. The last edge $3/4\to1/2$ has cost exactly $v-w$. This gives

$$
S=v-w+\frac{2t+m-e-5/4}{3}.
\tag{4}
$$

If $t>n_0$, begin the terminal chain directly at $n_0$. Its cost is no more than $t-3/4$, and the omitted cone allowance $(1-t+m-e)/3$ is nonnegative by Lipschitz continuity between $t$ and $1$. Hence the same upper bound (4) is valid. This verifies the potentially problematic case where one cannot physically visit $t$ in a decreasing chain.

The edge count remains controlled by $n_0$: whenever the construction visits $t$, it has $t\le n_0$; otherwise it begins at $n_0$. Appending $1/2\to0$ has zero cost.

## Convex combination and domination at the early threshold

Lipschitz continuity between $1/2$ and $u$ gives

$$
w\ge v-u+\frac12.
$$

Using this in (4) yields

$$
S\le u+\frac{2t+m-e-11/4}{3}.
$$

Choose the better of the two chains. Its cost is at most

$$
\begin{aligned}
\min\{R,S\}
&\le\frac34R+\frac14S\\
&\le\frac{3v}{4}+\frac1{48}-\frac e3
+\frac t6-\frac{5m}{12}\\
&\le\frac{3b}{8}+\frac1{48}-\frac a3
+\frac{2-5a}{12}t\\
&\le M(a,b):=\frac{3b}{8}+\frac3{16}-\frac{3a}{4}.
\end{aligned}
\tag{5}
$$

The substitutions are $v\le b/2$, $e\ge a$, $m\ge at$, and $t\le1$. The last step is valid because $2-5a>0$ for $a\le1/4$.

Let

$$
b_E=\frac{8a^2+8a-1}{a+2}.
$$

The inequality $E(a,b)<a$ is exactly $b<b_E$. At this threshold, direct algebra gives

$$
M(a,b_E)-a=\frac{5a(4a-1)}{16(a+2)}\le0
\qquad(0<a\le1/4).
$$

Since $M$ is strictly increasing in $b$, the strict inequality $b<b_E$ implies $M(a,b)<a$. Thus the early condition also handles every late-minimum profile. No optimization of $R$ or $S$ separately, and no case split according to an intersection location, is needed.

## Mesh and approximate-barrier checks

The reflection can be performed on a piecewise-linear grid profile using its running minimum; it remains 1-Lipschitz even if new bends occur between original grid points. Construct the bounded-length continuous chain and round each endpoint down to a grid point. When $1$ is a grid point, downward rounding preserves admissibility: from $p\ge2q-1$ one obtains

$$
\lfloor p/T\rfloor T\ge2\lfloor q/T\rfloor T-1.
$$

Remove duplicate consecutive endpoints. If $1/2$ and the starting point are grid points, these required endpoints are unchanged. Each edge cost changes by at most $2T$, because endpoint changes of size $T$ change the endpoint value and the interval minimum by at most $T$ each. Thus rounding incurs $O(KT)$ error. Using the affine-envelope mesh construction directly sharpens the basic exact-barrier errors, but $O(KT)$ suffices in the analytic application with fixed $K$.

For uniform approximate-barrier error $\epsilon N$, clamp the profile between its exact linear barriers and interpolate grid values. This changes it uniformly by $O(\epsilon N+T)$, preserves the 1-Lipschitz property, and changes each edge cost by at most twice that amount. The combined early/late theorem therefore has error $O(K\epsilon N+KT)$. Classify the clamped profile using its own minimum, so no preservation of minimum location is assumed.

## Consequence at the level of profile parameters

Writing $s=1+a$ and $u=1+b$, the sufficient elementary condition is

$$
u<\frac{s(8s-7)}{s+1},\qquad 1<s\le\frac54.
$$

For example, at $s=31/25=1.24$, the cutoff is exactly $2263/1400\approx1.6164285714$. This is a profile consequence; any corresponding positive-measure pinned-distance theorem must cite a separately verified analytic transfer.
