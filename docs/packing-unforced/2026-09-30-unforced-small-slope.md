# An unforced profile bound below upper slope one half

30 September 2026. This is an elementary chain theorem. Its application to distance sets is **conditional on a valid analytic transfer that does not require the chain to pass through the midpoint**. The existing forced-midpoint transfer cannot simply be substituted here. No distance-set improvement is claimed by this note alone.

## Statement

Let

$$
0<a\le b\le\frac12,
$$

and let g:[0,1]→ℝ be 1-Lipschitz with

$$
ax\le g(x)\le bx.
$$

For an edge from n down to m<n, define

$$
c_g(m,n)=g(m)-\min_{[m,n]}g,
\qquad 2n-m\le1.
$$

For every n₀<1, there is an admissible decreasing chain from n₀ to zero of length

$$
K\le C\left(1+\log\frac1{1-n_0}\right)
$$

and cost at most

$$
\boxed{U(a,b)=\frac{(b-a)(1-a)}{2(2b-a)}.}
\tag{1}
$$

There is no forced intermediate endpoint. Scaling to [0,N] multiplies the bound by N and replaces the logarithm by log(N/(N−n₀)). A mesh version has an additive O(KT) error, and approximate linear barriers with uniform error εN have an additional O(KεN) error.

## A region with free continuation

Put

$$
q=\frac{b}{2b-a},\qquad r=2q-1=\frac{a}{2b-a}.
$$

Then 1/2<q≤1 and 0<r≤1. If 1/2<n≤q, the two barriers imply

$$
g(2n-1)\le b(2n-1)\le an\le g(n),
\tag{2}
$$

because (2b−a)n≤b. Thus the interval [2n−1,n] has a minimum at some m<n; choose its leftmost minimum. The edge n→m is admissible and has zero cost. When n≤1/2, the edge directly to zero is admissible and has zero cost since g(0)=0 and g≥0.

On a finite grid this procedure terminates. Consecutive zero-cost edges can be merged whenever their union is admissible: their final lower endpoint remains a minimum on the union. Every two consecutive unmergeable edges more than double the complementary depth 1−n. Hence the retained zero-cost portion has logarithmically many edges. A grid limit gives the continuous statement, as detailed below.

If a=b, then q=1, so this free-continuation argument already proves the theorem with cost zero. We henceforth allow b>a and treat a starting point n₀>q; if n₀≤q, the same free continuation suffices.

## A localized affine majorant for the initial portion

On z≥r, the affine function

$$
H(z)=\frac z2+\left(b-\frac12\right)r
$$

majorizes bz, because

$$
H(z)-bz=\left(\frac12-b\right)(z-r)\ge0.
$$

For x≥q define

$$
\Lambda(x)=H(2x-1)-g(x)
=x-\frac12+\left(b-\frac12\right)r-g(x).
$$

The function Λ is nondecreasing. At the lower endpoint,

$$
\Lambda(q)=H(r)-g(q)=br-g(q)=aq-g(q)\le0.
\tag{3}
$$

Almost everywhere,

$$
(-g')_+\le\frac{1-g'}2=\frac{\Lambda'}2.
\tag{4}
$$

Starting at n₀, move down through the region Λ>0 by maximal admissible jumps, shortening the last jump if necessary to reach the zero-potential boundary. The sum of the costs is at most Λ(n₀)₊/2, since each edge cost is bounded by the negative variation of g on that edge and (4) telescopes. Because Λ is nondecreasing, this is at most Λ(1)/2.

Within Λ≤0 and above q, the interval [2n−1,n] again contains a point of value at most g(n), now because

$$
g(2n-1)\le H(2n-1)\le g(n).
$$

The majorant is valid here because 2n−1≥r. Choose a leftmost minimum to take a zero-cost edge. Continue until an endpoint becomes at most q; it need not equal q. Thereafter use (2) to reach zero for free. The positive-cost maximal jumps and the compressed zero-cost portion both have the required logarithmic edge bounds.

Finally, H(1)≥g(1), and g(1)≥a, so

$$
\frac{\Lambda(1)}2
=\frac{H(1)-g(1)}2
\le\frac{1/2+(b-1/2)r-a}{2}
=\frac{(b-a)(1-a)}{2(2b-a)}.
$$

This proves (1).

For full formal detail of the continuous construction, apply the described procedure on increasingly fine uniform grids to the piecewise affine interpolants of g, using a mesh crossing error at q and at the sign change of Λ. The interpolants retain both barriers and the Lipschitz constant and converge uniformly to g. All crossing errors are bounded by a fixed multiple of the mesh, and the number of retained edges is uniform in the mesh. Pad endpoint lists by repeated endpoints and extract a convergent subsequence. Interval minima vary continuously with the profile and endpoints; admissibility is closed. Removing repeated endpoints yields a continuous chain with the asserted exact cost. The same argument gives O(KT) error on a fixed grid. Clamping approximate barriers and comparing every edge cost gives O(KεN+KT) stability.

## Comparison with the old unforced estimate

Using the global majorant g(x)≤x/2 only gave (1/2−a)/2. The gain from (1) is

$$
\frac{1/2-a}{2}-U(a,b)
=\frac{a(1/2-b)}{2(2b-a)}\ge0,
$$

and is strict for b<1/2. At b=1/2 the new bound joins the known upper-slope bound continuously:

$$
U(a,1/2)=\frac{1/2-a}{2}
=\frac{b-a}{1+2b}\Big|_{b=1/2}.
$$

The new estimate is not asserted to be sharp. The single-collapse example gives the lower model obstruction (b−a)/(1+2b), which is smaller than U when a<b<1/2. Indeed, the difference between the corresponding numerator factors is

$$
(1-a)(1+2b)-2(2b-a)=(1+a)(1-2b)>0.
$$

## Exact single-collapse obstruction

For every 0<a<b≤1, define

$$
g(x)=\min\{bx,1+a-x\},\qquad
p=\frac{1+a}{1+b}.
$$

The profile is affine of slope b up to p, and affine of slope −1 afterward. It is 1-Lipschitz and satisfies ax≤g(x)≤bx: the lower barrier on the second piece is equivalent to (1+a)(1−x)≥0. Put

$$
C=\frac{b-a}{1+2b},\qquad
s=1-C=\frac{1+a+b}{1+2b},\qquad
q=2s-1=\frac{1+2a}{1+2b}.
$$

The inequality a<b implies q<p<s. For 0<ζ<C, the exact infimum of the cost of admissible chains from 1−ζ to zero is

$$
C-\zeta.
\tag{7}
$$

To prove the lower bound, consider the first edge from n>s to an endpoint u≤s. All earlier edges lie on the terminal descending affine piece and have total cost 1−ζ−n. If u≥p, the crossing edge costs n−u≥n−s, yielding total cost at least C−ζ. If u<p, admissibility gives u≥2n−1>q. The interval contains the single peak, so its minimum is at an endpoint and the crossing cost is

$$
\bigl(bu-(1+a-n)\bigr)_+
\ge(1+2b)(n-s).
$$

Adding the previous cost gives at least C−ζ again. All subsequent costs are nonnegative.

For attainment, double the complementary depth down to s, shortening the last step as needed. This costs C−ζ. The edge s→q is admissible with equality and has zero cost, because

$$
g(s)=1+a-s=\frac{b(1+2a)}{1+2b}=g(q),
$$

and the profile lies above that common value between q and s. On [0,q] the profile is increasing, so all downward edges cost zero. Maximal admissible jumps therefore finish at zero without extra cost. The chain length is O(1+log(1/ζ)). This proves (7). When a=b, the profile is simply ax and the exact cost is zero.

Consequently the known universal unforced bound

$$
\frac{b-a}{1+2b}\qquad(b\ge1/2)
$$

is sharp in the limiting profile minimax problem. The lower construction itself works even below b=1/2, where equality with the universal minimax is not established.

At a=1/4 and b=1, its limiting cost equals 1/4. Thus the strict source-margin condition based on this unforced profile minimax cannot continue beyond its critical full-packing balance at d=5/4. This is only a limitation of this profile-based estimate: it does not prove a necessary dimension threshold for distance sets or rule out different analytic methods.

## Conditional source-energy balances

For a<1/5,

$$
U(a,b)<a
\quad\Longleftrightarrow\quad
b<\frac{a(1-3a)}{1-5a}.
\tag{5}
$$

At b=2a the cost simplifies to

$$
U(a,2a)=\frac{1-a}{6},
$$

so the comparison U<a holds exactly when a>1/7. The cutoff in (5) exceeds 2a precisely when a>1/7 and reaches b=1/2 at a=1/6. Its derivative in a is

$$
\frac{1-6a+15a^2}{(1-5a)^2}>0.
$$

For a≥1/6, the existing unforced estimate for b≥1/2 gives

$$
\frac{b-a}{1+2b}<a
\quad\Longleftrightarrow\quad
b<\frac{2a}{1-2a}.
$$

Thus, **if the independently investigated unforced analytic transfer is valid**, the profile balances together with the coherent criterion suggest the continuous sufficient curve

$$
B_{\mathrm{unforced}}(d)=
\begin{cases}
2d-1,&1<d\le8/7,\\[4pt]
\dfrac{2+2d-3d^2}{6-5d},&8/7<d\le7/6,\\[7pt]
\dfrac1{3-2d},&7/6<d\le5/4.
\end{cases}
\tag{6}
$$

The joins equal 9/7 and 3/2 respectively. This is currently a conditional candidate for distance sets, not a proved consequence of the existing forced-midpoint construction.

An exact favorable profile example is

$$
a=\frac3{20},\qquad b=\frac8{25},\qquad
U(a,b)=\frac{289}{1960}<\frac3{20},
$$

with margin 1/392. These parameters correspond to d=1.15 and D=1.32; the coherent dimension cutoff at d=1.15 is only 1.30. Again, obtaining that geometric conclusion requires the new analytic transfer to be proved.
