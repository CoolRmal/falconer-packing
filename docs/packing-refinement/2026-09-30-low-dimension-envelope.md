# A further profile improvement near Hausdorff exponent 1.19

30 September 2026. This is an elementary profile estimate. The pinned-distance consequence requires the separate analytic transfer, and no globally weakest dimension condition is claimed.

## An upper envelope using both barriers

Assume

$$
0<a\le b\le\frac12,
\qquad ax\le g(x)\le bx\quad(0\le x\le1),
$$

where g is 1-Lipschitz. Suppose t in [1/2,3/4] is a global minimum of g on [1/2,1], and put

$$
m=g(t),\qquad v=g(1/2),\qquad e=g(1),
\qquad z_* =\frac{t-m}{1-b}.
$$

Because m≤bt, we have z_*≥t. On the entire tail z≥t,

$$
g(z)\le\min\{bz,m+z-t\}.
$$

The affine function

$$
H(z)=\frac z2+\left(b-\frac12\right)z_*
\tag{1}
$$

majorizes this minimum. Indeed, when z≤z_*,

$$
H(z)-(m+z-t)=\frac{z_*-z}{2}\ge0,
$$

and when z≥z_*,

$$
H(z)-bz=\left(\frac12-b\right)(z-z_*)\ge0.
$$

This argument also covers z_*>1.

## Chain estimate before the minimum

Let n₀ be in [3/4,1). For x≥(1+t)/2 define

$$
\Lambda(x)=H(2x-1)-g(x).
$$

This is nondecreasing because H has slope 1/2 and g is 1-Lipschitz. Almost everywhere,

$$
(-g')_+\le\frac{1-g'}2=\frac{\Lambda'}2.
$$

In the positive-potential region, maximal admissible downward jumps cost at most half the decrease of Λ. Stop upon reaching (1+t)/2 if this occurs before leaving that region. Otherwise, while Λ(n)≤0 and n>(1+t)/2, the admissible interval [2n−1,n] contains a point with value at most g(n), since

$$
g(2n-1)\le H(2n-1)\le g(n).
$$

Choose its leftmost minimum. That edge costs zero and its endpoint is at least t. Continue until the endpoint first becomes at most (1+t)/2. The edge from that endpoint to t is admissible and costs zero. On a finite grid the process is finite; consecutive zero-cost intervals can be merged whenever their union is admissible. Every two unmergeable intervals more than double the complementary depth, so the retained chain has O(1+log(1/(1−n₀))) edges. Passing to finer grids gives the continuous statement. A grid crossing costs only O(mesh).

The positive-part cost is at most

$$
\frac{\Lambda(1)}2
=\frac{1/2+(b-1/2)z_*-e}{2}.
$$

This quantity is nonnegative because H(1)≥g(1). If n₀≤(1+t)/2, the direct free jump to t suffices instead. Finally, t→1/2 is admissible and costs v−m, and 1/2→0 costs zero.

Combining this construction with the cone-only prefix construction gives a forced-midpoint chain of cost at most

$$
v-m+\min\left\{
\frac{1-t+m-a}{3},\quad
\frac{1/2-a-k(t-m)}2
\right\},
\qquad k=\frac{1/2-b}{1-b}.
\tag{2}
$$

No endpoint sign condition on Λ at (1+t)/2 was used: the construction explicitly stops there when the potential is still positive.

## Scalar optimization

The available constraints include

$$
m\ge at,
\qquad v\le\min\{b/2,m+t-1/2\}.
$$

For fixed t, replace v by its displayed upper bound. Each expression inside (2), after adding v−m, is nondecreasing in m before m=b/2−t+1/2, and decreasing afterward. Hence both are maximized at the same scalar value

$$
m=\max\{at,b/2-t+1/2\}.
$$

Write

$$
t_* =\frac{1+b}{2(1+a)}.
$$

For t≤t_*, the two resulting expressions increase with slopes 1/3 and 1−k. For t≥t_*, they decrease with slopes −(1+2a)/3 and −a−k(1−a)/2. Also t_* lies in [1/2,3/4] because a≤b≤1/2. Thus their minimum is maximized at t=t_* and m=at_*.

Consequently every early-minimum profile has a forced-midpoint chain of cost at most

$$
\boxed{\min\{E(a,b),F(a,b)\},}
\tag{3}
$$

where

$$
E(a,b)=\frac{1-2a-2a^2+(2+a)b}{6(1+a)},
$$

$$
F(a,b)=\frac{b-a}{2(1+a)}+\frac{1-2a}{4}
-\frac{(1-2b)(1-a)(1+b)}{8(1-b)(1+a)}.
\tag{4}
$$

The bound has a logarithmic number of edges. Approximate barriers have the same O(number of edges times uniform barrier error) stability as the previous chain estimates.

## Combination with the reflection estimate

The separately proved reflection estimate in `../output/pdf/packing-refinement-reflection-lemma.tex` gives the late-minimum bound

$$
M(a,b)=\frac{3b}{8}+\frac3{16}-\frac{3a}{4}.
$$

Thus, for b≤1/2, a universal sufficient profile balance is

$$
\max\{\min(E(a,b),F(a,b)),M(a,b)\}<a.
\tag{5}
$$

The new early condition is

$$
F(a,b)<a\quad\Longleftrightarrow\quad G(a,b)<0,
$$

where

$$
G(a,b)=-2(1+a)b^2+(3+13a+12a^2)b+1-13a-12a^2.
\tag{6}
$$

For 0≤b≤1/2 its derivative with respect to b satisfies

$$
\partial_bG=3+13a+12a^2-4(1+a)b
\ge1+11a+12a^2>0.
$$

On the parameter interval 3/16≤a≤1/5 there is a unique root b_F(a) in (a,1/2), because

$$
G(a,a)=(a-1)(a+1)(10a-1)<0,
\qquad G(a,1/2)=2-7a-6a^2>0.
$$

Explicitly, with c=13a+12a²,

$$
b_F(a)=\frac{3+c-\sqrt{(3+c)^2+8(1+a)(1-c)}}{4(1+a)}.
\tag{7}
$$

The late condition holds automatically below this early cutoff in that interval. To see this, put R(a)=14a/3−1/2. The inequality M<a is equivalent to b<R(a), and R lies in [0,1/2] for the parameters under consideration. Direct expansion gives

$$
G(a,R(a))=\frac{112a^3+76a^2+30a-9}{9}.
$$

This is increasing for a>0 and equals 1/256 at a=3/16. Therefore G(a,R)>0, so monotonicity in b implies b_F(a)<R(a). In particular, b<b_F(a) guarantees both F<a and M<a.

## Where this improves the existing dimension curve

The new cutoff first exceeds b=2a when

$$
16a^3+6a^2-7a+1<0,
\tag{8}
$$

because the left side is G(a,2a). Let a_L be its unique root in (3/16,19/100). The polynomial is strictly decreasing on this interval; its values at the endpoints have opposite signs. Numerically,

$$
a_L=0.188783591161\ldots.
$$

The root b_F exceeds the earlier rational cutoff

$$
b_E(a)=\frac{8a^2+8a-1}{a+2}
$$

until a=a_C, where a_C is the unique positive root in (19/100,1/5) of

$$
-32a^5-4a^4+103a^3+80a^2+a-4=0.
\tag{9}
$$

Indeed,

$$
(a+2)^2G(a,b_E(a))
=-32a^5-4a^4+103a^3+80a^2+a-4.
$$

The polynomial on the right is strictly increasing on [0,1/4]: its derivative is at least

$$
1-16(1/4)^3-160(1/4)^4=\frac18>0,
$$

after dropping its other positive terms. Its values at 19/100 and 1/5 are respectively −71456049/312500000 and 648/3125. Numerically,

$$
a_C=0.195322470969\ldots.
$$

Therefore, combining only proved profile balances with the separate coherent criterion, the new candidate dimension cutoff is

$$
B_{\mathrm{low}}(d)=
\begin{cases}
2d-1,&1<d\le1+a_L,\\[3pt]
1+b_F(d-1),&1+a_L<d<1+a_C,\\[3pt]
\dfrac{d(8d-7)}{d+1},&1+a_C\le d\le5/4.
\end{cases}
\tag{10}
$$

All joins agree exactly. The middle interval lies below d=1.2, so b_F is within the range for which it was proved. The curve strictly improves max(2d−1,d(8d−7)/(d+1)) throughout its open middle interval. Passing from (10) to a distance theorem still requires the same separately justified analytic transfer.

For a concrete exact balance, take

$$
a=\frac{19}{100},\qquad b=\frac{761}{2000}.
$$

Then

$$
F(a,b)=\frac{74596147}{393176000},\qquad
M(a,b)=\frac{3003}{16000},
$$

and

$$
a-\max(F(a,b),M(a,b))
=\frac{107293}{393176000}>0.
$$

These profile parameters correspond to d=1.19 and D=1.3805. The coherent condition alone only permits D<1.38, and the rational cutoff is also below 1.38 at this d.
