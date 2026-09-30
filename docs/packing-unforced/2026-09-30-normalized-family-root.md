# Exact optimized cutoff for the normalized interpolated family

30 September 2026. This note establishes continuity, strict monotonicity, and a unique-root description for the full normalized interpolated profile bound. Its geometric validity is the construction in the adaptive and interpolated head notes, with endpoint clipping and both late routes retained. The profile bound has also been independently audited by the profile-minimax agent.

## Definitions

Assume

$$
\frac1{10}\le a\le\frac16,\qquad 2a\le b\le\frac12,
\qquad 0\le\theta\le1.
$$

Put

$$
k=2b-a,\quad q=\frac b{k},\quad h=\frac{1+q}{2},\quad
h_\theta=h-\frac{\theta a}{4k},\quad r_\theta=\frac{\theta}{4b},
\quad m_\theta=\frac{a h_\theta}{1-a r_\theta}.
$$

Define the floor and early quantities

$$
L_0=\frac{1-2a}{4},\quad \lambda=\frac{1-2b}{4b},\quad
A_0=\frac{1-a-3b}{3},\quad
\gamma=\frac{6b-1-2a}{3a},
$$

$$
E_\theta=A_0+\gamma m_\theta,\qquad
J_E=\frac{\gamma L_0+\lambda A_0}{\gamma+\lambda}.
$$

The denominator $\gamma+\lambda$ is positive, including at $(a,b)=(1/10,1/5)$ where $\gamma=0$.

For the late variation and length routes, respectively, set

$$
A_v=\frac{1-a}{3}-\frac{(1-b)h_\theta}{2},\qquad
\sigma_v=\frac{1-a}{6a}-\frac{(1-b)r_\theta}{2},
$$

$$
A_l=\frac{1-a}{3}-h_\theta,\qquad
\sigma_l=\frac{a+2}{3a}-r_\theta.
$$

Both slopes are positive. For $i=v,l$, define

$$
P_i=A_i+\sigma_i a,\qquad
J_i=\frac{\sigma_i L_0+\lambda A_i}{\sigma_i+\lambda},\qquad
K_\theta=\min(P_v,J_v,P_l,J_l).
$$

Finally retain the safe zero-terminal bound

$$
Z=\min\left\{\frac{1-q}{3},
\frac{(1-a)(b-a)}{4(2b-a)(1-b)}\right\},
$$

and put

$$
C_\theta(a,b)=\max\{Z,\min(E_\theta,J_E),K_\theta\},
\qquad
N(a,b)=\min_{0\le\theta\le1}C_\theta(a,b).
\tag{1}
$$

These formulas use only rational operations, finite maxima/minima, and minimization over a fixed compact interval. The minimum is attained. All denominators are positive on the stated closed domain. The family gives admissible chains with the established logarithmic edge bound, grid error, and barrier-error stability, starting at $n_0\ge15/16$.

## Strict monotonicity in the packing parameter

For each fixed $a,\theta$, every function entering the minimum and maximum in (1) is strictly increasing in $b$.

The two terms defining $Z$ increase strictly: the ratio $(b-a)/(2b-a)$ increases, and the additional factor $1/(1-b)$ in the second term increases. For $E_\theta$, the useful factorization is

$$
E_\theta=\frac{b-a}{3(2b-a)}\,T,
\qquad
T=\frac{2b(6b-4a+1)-\theta a(1-a)}{4b-\theta a}.
$$

Both factors are positive. The first increases strictly. Writing $b=2a+x$, $x\ge0$, the numerator of $T'$ after multiplication by $(4b-\theta a)^2$ is

$$
a^2(192-44\theta)+ax(192-24\theta)+2a\theta+48x^2>0.
$$

Thus $E_\theta$ increases strictly. The earlier derivative computation for $J_E$ remains valid on this larger domain:

$$
\partial_bJ_E=
\frac{a(1-a)(60b^2-12b+1-4a)}{(24b^2-14ab+3a-4b)^2}>0.
$$

The quadratic factor is increasing for $b\ge2a\ge1/5$, and at $b=2a$ it equals $240a^2-28a+1\ge3/5$ for $a\ge1/10$.

The endpoint costs $P_i$ increase strictly because $H_\theta(a)=h_\theta+r_\theta a$ decreases strictly in $b$. Explicitly,

$$
P_l=1-H_\theta(a),\qquad
P_v=\frac{1-a}{2}-\frac{(1-b)H_\theta(a)}2.
$$

For the intersection costs $J_i$, there is a short proof avoiding large derivative expressions. Write

$$
L_b(m)=L_0-\lambda m,\qquad S_{i,b}(m)=A_i+\sigma_i m.
$$

Their intersection occurs at a positive $m$. In fact it lies strictly above $aq$, since

$$
L_b(aq)-S_{v,b}(aq)
=\frac{(b-a)(5-2a-9b)}{12(2b-a)}>0,
$$

$$
L_b(aq)-S_{l,b}(aq)=\frac{(4-a)(1-q)}6>0.
$$

At every fixed $m>0$, the floor $L_b(m)$ increases strictly in $b$. So do both route lines: $H_\theta(m)$ decreases strictly in $b$, and

$$
S_{l,b}(m)=\frac{1-a}{3}-H_\theta(m)+\frac{a+2}{3a}m,
$$

$$
S_{v,b}(m)=\frac{1-a}{3}-\frac{(1-b)H_\theta(m)}2
+\frac{1-a}{6a}m.
$$

At the old intersection point, increasing $b$ therefore increases both line values strictly. The new intersection value is at least their new minimum at that point, and hence is strictly larger than the old intersection value. This proves strict increase of $J_v,J_l$, including comparison with the endpoint $b=1/2$ where the floor becomes constant.

Finite minima and maxima preserve strict increase. Therefore $C_\theta(a,b)$ increases strictly in $b$. Compact minimization over $\theta$ preserves it here: if $b_1<b_2$, choose a minimizing parameter $\theta_2$ at $b_2$. Then

$$
N(a,b_1)\le C_{\theta_2}(a,b_1)
<C_{\theta_2}(a,b_2)=N(a,b_2).
$$

Joint continuity of $N$ follows from joint continuity of $C_\theta$ and minimization over the fixed compact interval $[0,1]$.

## The unique cutoff

For every $a\in[1/10,1/6]$, there is a unique

$$
\beta(a)\in[2a,1/2],\qquad N(a,\beta(a))=a.
\tag{2}
$$

Moreover $\beta$ is continuous,

$$
\beta(1/10)=1/5,\qquad \beta(1/6)=1/2,
$$

and $2a<\beta(a)<1/2$ for $1/10<a<1/6$. Within the parameter domain,

$$
N(a,b)<a\quad\Longleftrightarrow\quad b<\beta(a).
\tag{3}
$$

Here are the endpoint checks. At $b=2a$, the choice $\theta=1$ bounds the three cases by

$$
\frac{1-a}{12(1-2a)},\qquad
\frac{1+11a}{21},\qquad
\frac{1+6a}{16}.
$$

All are strictly below $a$ for $a>1/10$; the first is already strictly below $a$ at $a=1/10$, while the last two equal $a$ there.

At $(a,b)=(1/10,1/5)$ no interpolating parameter gives a strict bound below $a$. Indeed $L_b(a)=1/8>a$, while

$$
P_v=\frac{1+4a}{12}-\frac{\theta(1-2a)}{48}\ge a,
\qquad P_l=\frac16-\frac{\theta}{24}\ge\frac18>a.
$$

Every intersection value is at least the minimum of its two lines at $m=a$, so $J_v\ge a$ and $J_l>a$. Consequently $K_\theta\ge a$. Equality is achieved at $\theta=1$, proving the lower endpoint in (2). For $\theta<1$, all four late bounds exceed $a$, so the endpoint optimum is uniquely $\theta=1$. Thus optimizing this family does not further lower its onset beyond $a=1/10$.

At $b=1/2$, all three intersection values equal $L_0=(1-2a)/4$. Also $E_\theta\ge E_0=(1-2a)/3>L_0$, $P_l\ge L_0$, $P_v>L_0$, and $Z\le L_0$. Hence

$$
C_\theta(a,1/2)=N(a,1/2)=\frac{1-2a}{4}\ge a,
$$

with equality only at $a=1/6$. Continuity and strict increase in $b$ now prove (2) and (3). Continuity of $\beta$ follows by taking convergent subsequences of roots and using uniqueness at the limit.

This yields a clean exact cutoff without listing the several algebraic branches selected by the optimizer. Equation (2), with (1), is the definition of the cutoff; numerical root finding is only a way to evaluate it.

## Exact examples

For a simple example demonstrating the lower onset, choose

$$
a=\frac{11}{100},\qquad b=\frac9{40},\qquad\theta=1.
$$

Exact substitution gives

$$
C_1=\frac{644}{5925},\qquad
\frac{11}{100}-C_1=\frac{31}{23700}>0.
$$

Under the established transfer argument, this covers $d=1.11$, $D=1.225$, whereas the former coherent condition required $D<1.22$.

For an example where interpolation improves the fully adaptive endpoint, choose

$$
a=\frac7{50},\qquad b=\frac{11}{35},\qquad \theta=\frac13.
$$

Here

$$
E_{1/3}=\frac{31871951}{228208050},\qquad
K_{1/3}=J_v=\frac{452437}{3234750},
$$

and

$$
C_{1/3}=\frac{452437}{3234750},\qquad
\frac7{50}-C_{1/3}=\frac{214}{1617375}>0.
$$

In contrast, the two early bounds at $\theta=1$ both exceed $a$:

$$
E_1-a=\frac{572}{205275}>0,\qquad
J_E-a=\frac{264}{56195}>0.
$$

Thus the interpolation supplies an exact strict improvement for the dimension pair $d=57/50=1.14$, $D=46/35\approx1.314286$.

## Relation to the previously published bound

At $\theta=0$, the early quantity is the published $E_2$, and the new late minimum is at most each of the published $J_F,J_V$ because it retains those same intersection bounds as well as two endpoint bounds. Also $Z\le(1-q)/3$. Therefore, on $a\ge1/8$, the earlier proof that this zero-terminal term is redundant gives $C_0\le V$, hence $N\le V$.

The optimized family therefore preserves all previously obtained sufficient pairs and strictly improves some of them. It is not asserted to be the optimal profile bound or the weakest possible geometric condition.
