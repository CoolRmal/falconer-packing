# A stronger profile bound from an adaptive free head interval

30 September 2026. This note gives a new sufficient profile estimate. It uses the actual tail minimum twice: first to enlarge the free interval, then to choose the head interval. It also retains the elementary relation between that minimum and the endpoint value. No published source file is changed here.

## Statement

Assume

$$
\frac19\le a\le\frac16,\qquad 2a\le b\le\frac12.
$$

Let $g:[0,N]\to\mathbb R$ be 1-Lipschitz, with $ax\le g(x)\le bx$. An admissible edge from $n$ to $v<n$ satisfies $2n-v\le N$, and has cost

$$
c_g(v,n)=g(v)-\min_{[v,n]}g.
$$

For every $15N/16\le n_0<N$, there is an admissible chain from $n_0$ to zero of total cost at most $NW(a,b)$, where

$$
W(a,b)=\max\left\{
 \frac{(b-a)(1+6b-a)}{3(4b-a)},
 \frac{b-a}{4b+3a-9ab}
\right\}.
\tag{1}
$$

The chain has at most $C(1+\log(N/(N-n_0)))$ edges, with absolute $C$. Rounding to a grid of mesh $T$ costs $O(KT)$; additive barrier errors of size $\epsilon N$ cost $O(K\epsilon N)$. Thus this estimate has the same transfer properties as the published profile estimates, after choosing the fixed initial loss $\zeta<1/16$.

This is a strict improvement near $b=2a$: for every $1/9<a\le1/6$,

$$
W(a,2a)=\max\left\{\frac{1+11a}{21},\frac1{11-18a}\right\}<a.
\tag{2}
$$

The onset supplied by this argument is consequently $d=1+a>10/9$, improving the previous onset $d>9/8$. The claim is a new sufficient bound, not an optimality assertion.

## Two elementary chain constructions

Normalize $N=1$. Negative variation on an interval satisfies

$$
\operatorname{Var}^-(g;[v,w])
\le\frac{w-v+g(v)-g(w)}2.
\tag{3}
$$

Every edge cost is at most the negative variation on its interval, so any decreasing chain inside $[v,w]$ has total cost at most the right side of (3).

We use the following two consequences of the affine-potential construction proved in `output/pdf/packing-unforced-minimum.tex`. Their proof uses only the displayed potential calculation, recalled here to specify their hypotheses.

If $H(z)=cz+d$ with $c\ge1/2$ majorizes the profile at the relevant left endpoints, put $\Lambda(x)=H(2x-1)-g(x)$. It is nondecreasing and

$$
(-g')_+\le\frac{2c-g'}{2c+1}=\frac{\Lambda'}{2c+1}
\quad\text{almost everywhere}.
$$

Maximal admissible edges through the positive-potential region, shortening the last edge to its boundary, cost at most $\Lambda(n_0)_+/(2c+1)$. In the nonpositive region, move to a leftmost minimum on $[2n-1,n]$ for zero cost.

First, if $t$ is a minimum on $[t,1]$, write $m=g(t)$ and $e=g(1)$. The cone $H(z)=m+z-t$, followed by a free jump to $t$ when the current endpoint is at most $(1+t)/2$, gives a chain to $t$ of cost at most

$$
\frac{1-t+m-e}{3},\qquad n_0\ge t.
\tag{4}
$$

This quantity is nonnegative by the Lipschitz condition. Second, the slope-$1/2$ floor used below gives (8).

## The adaptive free interval

Put

$$
q=\frac b{2b-a}.
$$

Every endpoint $n\le q$ has a free continuation to zero: for $1/2<n\le q$,

$$
g(2n-1)\le b(2n-1)\le an\le g(n),
$$

so move to a leftmost interval minimum; below $1/2$, jump to zero.

Choose a minimum point $t$ on $[q,1]$, and write $m=g(t)$, $e=g(1)$. In particular,

$$
aq\le at\le m\le bq,\qquad e\ge\max(a,m).
\tag{5}
$$

Define the two adaptive endpoints

$$
Q=\frac{1+m/b}{2},\qquad H=\frac{1+Q}{2}=\frac{3+m/b}{4}.
\tag{6}
$$

Then

$$
q\le Q\le\frac{1+q}{2},\qquad H\le\frac{3+q}{4}\le\frac{11}{12}<\frac{15}{16}\le n_0.
$$

The last inequality uses $b\ge2a$, hence $q\le2/3$.

Every endpoint below $Q$ also has a free continuation. Indeed, if $q<n\le Q$,

$$
g(2n-1)\le b(2n-1)\le m\le g(n).
\tag{7}
$$

If a chosen interval minimum crosses below $q$, use the already proved free continuation there.

The affine function $H_m(z)=z/2+(b-1/2)m/b$ majorizes $bz$ for $z\ge m/b$. Its potential is nonpositive at $Q$. Applying the potential construction down to the expanded free interval gives a chain of cost at most

$$
\frac{1-2e}{4}-\frac{1-2b}{4b}m
\le\frac14-\frac{m}{4b}.
\tag{8}
$$

The last step retains $e\ge m$, rather than merely $e\ge a$.

## An early minimum

If $t\le Q$, apply (4) and then the free continuation. Its cost is at most

$$
E_1=\frac{1-q}{3}=\frac{b-a}{3(2b-a)}.
\tag{9}
$$

Suppose now that $Q<t\le H$. Choose a minimum $v$ of $g$ on $[2t-1,Q]$. The edge $t\to v$ is admissible and has cost at most $(b(2t-1)-m)_+$, after which the continuation is free. The total cost is bounded by

$$
\frac{1-t+m-e}{3}+(b(2t-1)-m)_+.
\tag{10}
$$

If the positive part vanishes, use (9). Otherwise (10) is at most

$$
A(t,m)=\frac{1-a-3b+(6b-1)t-2m}{3}.
$$

We have $t\le\min\{m/a,H\}$. Put

$$
m_0=\frac{3ab}{4b-a},
\quad\text{so that}\quad \frac{m_0}{a}=\frac{3+m_0/b}{4}.
$$

For $m\le m_0$, the bound $t\le m/a$ gives an increasing affine bound for $A$, with slope $(6b-1-2a)/(3a)>0$. For $m\ge m_0$, the bound $t\le H$ gives

$$
A(t,m)\le\frac1{12}-\frac a3+\frac b2-\frac{2b+1}{12b}m,
\tag{11}
$$

which decreases with $m$. The two lines agree at $m_0$. Their common value is

$$
E=\frac{(b-a)(1+6b-a)}{3(4b-a)}.
\tag{12}
$$

Thus the early case has cost at most $\max(E_1,E)$.

## A late minimum: reflection or a free terminal interval

Suppose $t>H$. Let $u$ minimize $g$ on $[Q,H]$, and put $w=g(u)$ and $z=b(2u-1)$. We have $2u-1\le Q$, $w\ge m$, and

$$
m\ge at>aH,
\quad\text{hence}\quad m>m_0.
\tag{13}
$$

If $w\le z$, reflect successive new minima after $u$: let $r=0$ before $u$, let $r(x)=w-\min_{[u,x]}g$ after $u$, and put $f=g+r$. The function $f$ is 1-Lipschitz, agrees with $g$ to the left of $u$, has minimum $w$ on $[Q,1]$, and has endpoint $e+w-m$. The direct running-minimum proof and edge inequality are

$$
c_g(v,n)\le c_f(v,n)+r(n)-r(v).
$$

The extra costs telescope to at most $w-m$. Apply the cone construction to $f$, then jump to a minimum on $[2u-1,Q]$ and use the free continuation below $Q$. The resulting cost for $g$ is at most

$$
\frac{1-u-e-2m}{3}+\max(w,z)
=\frac{1-e-3b+(6b-1)u-2m}{3}.
$$

Since $u\le H$ and $m>m_0$, (11) bounds this by $E$.

It remains to treat $w\ge z$. If $t\le n_0$, take the cone chain to $t$, then any maximal admissible chain down to $H$. The edge $H\to u$ is free because $u$ minimizes on $[Q,H]$ and $Q=2H-1$. The next edge to a minimum on $[2u-1,Q]$ is free because its minimum is at most $z\le w$. Finish freely below $Q$.

The middle chain is bounded by negative variation. Combining (3) and (4), its total cost before the free part is at most

$$
\frac{1-e}{3}-\frac{(1-b)H}{2}+\frac{t-m}{6}.
$$

Use $e\ge m$, $t\le m/a$, and (6). The resulting bound is

$$
S+\sigma m,
\qquad S=\frac{-1+9b}{24},
\qquad \sigma=\frac{1-3a}{6a}-\frac{1-b}{8b}>0.
\tag{14}
$$

For the positivity, use $b\ge2a$ to obtain $\sigma\ge(5-18a)/(48a)>0$.

If $t>n_0$, omit the cone and start the middle chain at $n_0$. Restricting the interval decreases negative variation. The omitted allowance $(1-t+m-e)/3$ is nonnegative, so (14) remains valid without change.

Finally compare (14) with the decreasing floor bound (8). The elementary intersection inequality gives, for every real $m$,

$$
\min\left\{\frac14-\frac{m}{4b},\ S+\sigma m\right\}
\le\frac{b-a}{4b+3a-9ab}=:J.
\tag{15}
$$

Thus all cases have cost at most $\max(E_1,E,J)$. In the stated domain, $E_1\le J$: after cancelling $b-a>0$, this is equivalent to

$$
b(2+9a)\ge6a,
$$

which follows from $b\ge2a$ and $a\ge1/9$. This proves (1).

## Length, limiting profiles, and perturbations

The constructions have a bounded number of cone, maximal-edge, and zero-cost portions. Maximal edges double complementary depth. Adjacent free edges can be merged when their union is admissible; after all such merges, every two retained free edges more than double complementary depth. Piecewise affine profiles therefore have the asserted uniform logarithmic edge bound.

For arbitrary Lipschitz profiles, interpolate on finer partitions containing $0,n_0,1$, preserving the linear barriers. Pad the uniformly bounded endpoint lists and pass to a convergent subsequence. Interval minima, costs, and admissibility pass to the limit. Rounding endpoints down preserves admissibility and changes each cost by at most $2T$. Clamping approximate profiles between the linear barriers changes each cost by at most $2\epsilon N$. This supplies the claimed bounded-chain and stability properties without assuming termination of an arbitrary infinite minimum iteration.

## Explicit sufficient cutoff and comparison

Both terms in (1) increase strictly with $b$. Their inequalities $E<a$ and $J<a$ are respectively

$$
6b^2+(1-19a)b+4a^2-a<0,
\qquad
b(1-4a+9a^2)<a(1+3a).
$$

Consequently, within the stated parameter range,

$$
W(a,b)<a
\quad\Longleftrightarrow\quad
b<\min\left\{
\frac{19a-1+\sqrt{265a^2-14a+1}}{12},
\frac{a(1+3a)}{1-4a+9a^2}
\right\}.
\tag{16}
$$

For example, take $a=3/25$ and $b=1/4$. Then

$$
E=\frac{1547}{13200},\qquad
J=\frac{13}{109},\qquad
W=\frac{13}{109}<\frac3{25},\qquad
\frac3{25}-W=\frac2{2725}.
$$

Subject to the previously established transfer argument, this covers $d=28/25=1.12$, $D=5/4=1.25$, whereas the earlier coherent condition required $D<2d-1=1.24$ and the previous actual-minimum refinement only improved that condition for $d>9/8$.

The new $W$ need not dominate the published cost $V$ throughout their common domain. One should take the cheaper of the available constructions. No global optimality is claimed.
