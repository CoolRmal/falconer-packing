# A strict improvement at the former onset using the actual free frontier

30 September 2026. This gives an independent elementary improvement at $a=1/10$, $b=1/5$. It is a sufficient profile estimate, and is not claimed optimal. It uses no hard-point decomposition or numerical optimization.

## Exact statement

Let $g:[0,1]\to\mathbb R$ be 1-Lipschitz and satisfy

$$
\frac{x}{10}\le g(x)\le\frac{x}{5}.
$$

For every $15/16\le n_0<1$, there is an admissible chain from $n_0$ to zero, with edges $n\to v$ satisfying $2n-v\le1$, whose total cost is at most

$$
\frac{161}{1630}<\frac1{10},
\qquad \frac1{10}-\frac{161}{1630}=\frac1{815}.
\tag{1}
$$

The edge count is $O(1+\log(1/(1-n_0)))$. Grid and barrier perturbations have the same $O(KT+K\epsilon)$ errors as the previous constructions.

First clip the endpoint by $g\mapsto\min(g,1+1/10-x)$. This preserves the barriers and Lipschitz constant, makes $g(1)=1/10$, and increases every edge cost. It is therefore enough to prove (1) after this normalization.

## The actual free frontier

Write $a=1/10$, $b=1/5$, $q=b/(2b-a)=2/3$, and

$$
D(x)=b(2x-1)-g(x).
$$

We have $D\le0$ on $[1/2,q]$, while $D(1)=b-a>0$. Define

$$
\rho=\inf\{x\in[q,1]:D(x)>0\}.
$$

Continuity gives $q\le\rho<1$, $D\le0$ on $[q,\rho]$, and

$$
w:=g(\rho)=b(2\rho-1).
\tag{2}
$$

Every endpoint below $\rho$ has a free continuation: whenever $1/2<n\le\rho$, move to a leftmost minimum on $[2n-1,n]$, using $g(2n-1)\le g(n)$; below $1/2$, jump to zero. The finite-chain justification is supplied at the end.

The endpoint Lipschitz bound gives

$$
b(2\rho-1)=g(\rho)\le a+1-\rho,
\qquad \rho\le\frac{1+a+b}{1+2b}=\frac{13}{14}<\frac{15}{16}.
\tag{3}
$$

Let $t$ minimize $g$ on $[\rho,1]$, and put $m=g(t)$. Thus

$$
\rho\le t,\qquad at\le m\le a,\qquad m\le w.
\tag{4}
$$

The choice of tail minimum is made *after* selecting the frontier. It need not be a minimum on the larger interval $[q,1]$.

## A reflected route that improves as the minimum rises

Reflect running minima after $\rho$: put $r=0$ to the left of $\rho$, and

$$
r(x)=w-\min_{[\rho,x]}g\quad(x\ge\rho),\qquad f=g+r.
$$

As in the earlier reflection lemma, $f$ is 1-Lipschitz, has minimum $w$ on $[\rho,1]$, and satisfies $f(1)=a+w-m$. The cone construction reaches $\rho$ from $n_0$ with cost at most $(1-\rho-a+m)/3$ for $f$. Its transfer to $g$ costs at most $w-m$, by the telescoping edge inequality. After that, continue freely below $\rho$. Consequently the cost is at most

$$
R=w+\frac{1-\rho-a-2m}{3}
=\frac1{10}+\frac{\rho-10m}{15}.
\tag{5}
$$

This remains valid if $t>n_0$: the correction at $n_0$ is at most $w-m$, and the cone only needs to reach $\rho<n_0$.

The Lipschitz bound between $\rho$ and $t$ gives $w-m\le t-\rho$. Combining this with $t\le10m$ yields

$$
\rho\le\frac{1+55m}{7}.
$$

Substitution in (5) gives the decreasing bound

$$
R\le\frac{23}{210}-\frac m7.
\tag{6}
$$

## A supporting-line route for small minima

Put

$$
M=\frac{184}{2445}.
$$

If $m\le M$, then

$$
t\le10M=\frac{368}{489}<\frac56
\le\frac{1+\rho}{2},\qquad t<n_0.
\tag{7}
$$

The two upper bounds $g(z)\le bz$ and $g(z)\le m+z-t$ on $[t,1]$ have a slope-$1/2$ supporting line. The affine-potential construction therefore reaches $t$ at cost at most

$$
P(t,m)=\frac15-\frac3{16}(t-m).
\tag{8}
$$

For clarity, this is the same supporting-line construction used for the improved zero-terminal case: stop at $(1+t)/2$ and jump freely to $t$. If positive potential remains at that threshold, discard it; if it vanishes earlier, use zero-cost minimum steps. Its validity uses only that $t$ is a tail minimum and that all left endpoints before the terminal jump are at least $t$.

If $t=\rho$, continue freely immediately. Otherwise (7) makes $[2t-1,\rho]$ nonempty. Choose its minimum $v$, jump from $t$ to $v$, and continue freely. Since $g\ge m$ on $[\rho,t]$, this terminal edge has cost at most

$$
\bigl(b(2t-1)-m\bigr)_+.
$$

When that quantity is zero, (8) is at most $3/32$: indeed $t-m\ge q-a=17/30$. When it is positive, the total bound is

$$
P(t,m)+b(2t-1)-m
=\frac{17}{80}t-\frac{13}{16}m
\le\frac{21}{16}m,
\tag{9}
$$

using $t\le10m$.

The increasing line in (9) and the decreasing line in (6) intersect exactly at $m=M$, with common value $161/1630$. If $m\ge M$, use (6). If $m\le M$, use (8)--(9). Since $3/32<161/1630$, this proves (1) in all cases.

## Finite chains and stability

For piecewise affine $g$, the free minimum iterations terminate: each chosen leftmost minimum is a breakpoint or the left endpoint, and steps of the latter type double complementary depth. The reflected and supporting-line constructions have a bounded number of portions.

Any two adjacent edges may be merged without increasing their cost when their union is admissible, because

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n),\qquad l<m<n.
$$

After compression, complementary depth more than doubles every two retained edges. Thus the edge bound is uniform. For general Lipschitz profiles, interpolate preserving the barriers, run the finite constructions, and pass to a subsequence of uniformly bounded endpoint lists. The frontier itself need not depend continuously on the profile; only the resulting chains, costs and closed admissibility constraints pass to the limit. Grid rounding and barrier clamping give the claimed error bounds.

## An explicit continuous neighborhood

The argument extends without a new geometric idea. For general nearby $a,b$, let $q=b/(2b-a)$, $\kappa=(1/2-b)/(1-b)$, and define

$$
R_0=\frac{1-a-2b(1+a)}{3(1+2b)},\qquad
R_1=\frac{2b(3+a)-1-3a}{3a(1+2b)},
$$

$$
B_0=\frac14-\frac a2-b,\qquad
B_1=\frac{2b-\kappa/2}{a}+\frac\kappa2-1,
\qquad
F=\frac{(1-a)(b-a)}{4(2b-a)(1-b)}.
$$

The same proof with a chosen cutoff $M>0$ gives the sufficient cost

$$
\max\{F,\ R_0+R_1M,\ B_0+B_1M\},
\tag{10}
$$

provided $0<a<b\le1/2$, $b>1/6$, $R_1<0$, $B_1>0$, $2b-\kappa/2\ge0$, and

$$
\frac{1+a+b}{1+2b}\le\frac{15}{16},\qquad
\frac Ma\le\min\left\{\frac{15}{16},\frac{1+q}{2}\right\}.
$$

These conditions have strict slack at the point used above, so (10) proves an open strict improvement around it. As one fully rational example, take

$$
a=\frac{999}{10000},\qquad b=\frac15,\qquad M=\frac{184}{2445}.
$$

All the stated guards hold by rational comparison, and (10) equals

$$
\frac{967086511}{9770220000},\qquad
a-\frac{967086511}{9770220000}
=\frac{8958467}{9770220000}>0.
$$

Under the previously established transfer theorem, this already gives a strict improvement below the former onset: $d=1.0999$, $D=1.2$, beyond the coherent threshold $2d-1=1.1998$.

The cutoff $M$ can be optimized, but no optimality statement is needed for the exact improvement proved here. Stronger independent hard-point estimates, if verified, should be used in preference to this sufficient bound.
