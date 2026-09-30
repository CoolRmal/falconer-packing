# Near-extremal pin profiles and source Fourier-energy saturation at the same scales

Date: 2026-09-30.

This note supplements [the profile-realizability construction](2026-09-30-profile-realizability.md). It proves that the same construction can exhibit a near-extremal pin profile and a source Fourier energy with exponent arbitrarily close to the Frostman upper bound on the same annulus, even after placing source and pins on fixed separated compact subsets.

It does not estimate the modified good part used in the distance proof, assert sharpness of a restriction estimate, or construct a null-distance counterexample.

## Precise statement

Let $0<a<b\le1$, let $d=1+a<2$, and let $D=1+b$. Fix a 1-Lipschitz template $g$ satisfying

$$
ax\le g(x)\le bx,\qquad g(1)=a,
\qquad g(x)=bx\quad(0\le x\le c)
$$

for some $c>0$. Let $E$, $\mu$, $N_j$, and the linearly interpolated dyadic branching exponent $F$ be those of the profile-realizability construction, so

$$
\mu(Q)=2^{-F(n)}
$$

on each occupied depth-$n$ dyadic square,

$$
F(N_j)\le dN_j,
\qquad
\left\|\frac{F(N_jx)}{N_j}-x-g(x)\right\|_\infty\longrightarrow0,
\tag{1}
$$

and $\mu$ is $d$-Frostman. Here $F$ denotes the rounded exponent called $F_{\rm dyad}$ in the construction note.

**Proposition.** There are fixed compact sets $E_{\rm s},E_{\rm p}\subset E$ with positive separation and probabilities $\sigma,\nu$ supported on them, with the following properties.

1. Both probabilities are $d$-Frostman, and both support sets have Hausdorff dimension $d$ and packing dimension $D$.
2. There is one common conditional dyadic exponent $F_k$ for both probabilities, with linearly interpolated normalized profiles

$$
g^{(k)}_n(x)=F_k(nx)/n-x.
$$

3. For every tolerance $\tau>0$ and every exponent loss $\epsilon>0$, there are infinitely many integers $n$ such that

$$
\|g^{(k)}_n-g\|_\infty\le\tau,
\qquad
\int_{2^n\le|\xi|<2^{n+1}}|\widehat\sigma(\xi)|^2\,d\xi
\ge2^{(2-d-\epsilon)n}.
\tag{2}
$$

Thus the pin probability $\nu$ has a near-extremal profile at exactly the annulus where the source probability $\sigma$ has nearly saturated Fourier energy. The compact source and pin supports are fixed independently of $n$, $\tau$, and $\epsilon$.

The Fourier-transform convention is

$$
\widehat\sigma(\xi)=\int e^{-2\pi i x\cdot\xi}\,d\sigma(x).
$$

## Fixed separated restrictions and their exact profiles

The Frostman measure is non-atomic and has at least two distinct points in its support. Choose disjoint open balls about two such points whose closures have positive separation. Each ball has positive measure. At a sufficiently large common depth $k$, choose an occupied dyadic square in each ball whose closed square still lies inside its ball. Such squares exist: the union of all depth-$k$ squares whose closures lie in a given open ball increases to that ball up to the harmless dyadic boundaries, and some such square must have positive measure for large $k$.

Call these squares $Q_{\rm s}$ and $Q_{\rm p}$. Both have mass $w=2^{-F(k)}$. Define

$$
\sigma=w^{-1}\mu|_{Q_{\rm s}},\qquad
\nu=w^{-1}\mu|_{Q_{\rm p}},
$$

and take $E_{\rm s}=\operatorname{supp}\sigma$, $E_{\rm p}=\operatorname{supp}\nu$. These supports are compact subsets of the separated closed squares and of $E$. They have positive original $\mu$ measure. The Frostman bounds follow from domination by $w^{-1}\mu$. Their Hausdorff dimensions are at least $d$ by those bounds, and at most $d$ by inclusion in $E$. Every positive-$\mu$ subset of $E$ has packing dimension $D$, by the positive-outer-measure covering argument in the realization note, so their packing dimensions equal $D$ as well.

For either conditional measure the exponent at integer depth $n$ is

$$
F_k(n)=
\begin{cases}
0,&n\le k,\\
F(n)-F(k),&n\ge k.
\end{cases}
\tag{3}
$$

Indeed the first $k$ digits are fixed, while each occupied descendant depth-$n$ square has conditional mass $2^{F(k)-F(n)}$. There are exactly $2^{F(n)-F(k)}$ such descendants. Binary-boundary ambiguities have zero measure as in the original construction.

After interpolation, $F_k$ is nondecreasing, its slopes are zero or two, and

$$
\|F_k-F\|_{L^\infty([0,\infty))}\le F(k)\le2k.
\tag{4}
$$

In particular the two conditional probabilities have exactly the same branching profile at every depth.

## Gaussian energy lower and upper bounds

For any probability $\lambda$ on the plane, Fubini and the Fourier transform of the Gaussian give

$$
\mathcal E_\lambda(R):=
\int e^{-\pi|\xi|^2/R^2}|\widehat\lambda(\xi)|^2\,d\xi
=R^2\iint e^{-\pi R^2|x-y|^2}\,d\lambda(x)\,d\lambda(y).
\tag{5}
$$

Fubini is justified directly because the Gaussian is integrable and the product measure has mass one. The inner Fourier integral is the two-dimensional product of the one-dimensional Gaussian transforms.

Take $R_j=2^{N_j}$, with $N_j\ge k$. Pairs of points in the same depth-$N_j$ dyadic square have distance at most $\sqrt2/R_j$. For the conditional source probability $\sigma$, the sum of the squares of the depth-$N_j$ cube masses equals $2^{F(k)-F(N_j)}$. The right side of (5) therefore gives

$$
\mathcal E_\sigma(R_j)
\ge e^{-2\pi}R_j^2\,2^{F(k)-F(N_j)}
\ge c_0R_j^{2-d},
\qquad c_0=e^{-2\pi}2^{F(k)}>0.
\tag{6}
$$

Only equal-cube pair counting is used; there is no claim that individual Fourier coefficients are large.

For the upper bound at arbitrary $R\ge1$, the $d$-Frostman estimate gives, uniformly in $x$,

$$
\int e^{-\pi R^2|x-y|^2}\,d\sigma(y)
\le C R^{-d}.
$$

To see this explicitly, use the ball $|x-y|\le R^{-1}$ and the annuli $2^{m-1}R^{-1}<|x-y|\le2^mR^{-1}$, $m\ge1$. Their respective contributions are bounded by $CR^{-d}$ and

$$
C R^{-d}2^{md}e^{-\pi 2^{2m-2}},
$$

whose sum converges. The Frostman bound can be enlarged to all radii by increasing its constant. Equation (5) yields

$$
\mathcal E_\sigma(R)\le C_1R^{2-d},
\qquad
\int_{|\xi|\le R}|\widehat\sigma(\xi)|^2\,d\xi
\le e^\pi\mathcal E_\sigma(R)\le C_2R^{2-d}.
\tag{7}
$$

## Locating a nearby dyadic annulus

Write $q=2-d>0$. Fix $0<\eta<1/4$ for now. In the Gaussian integral at $R_j$, the contribution from $|\xi|\le R_j^{1-\eta}$ is, by (7), at most

$$
C_2R_j^{(1-\eta)q}=o(R_j^q).
\tag{8}
$$

Since $|\widehat\sigma|\le1$, the contribution from $|\xi|\ge R_j^{1+\eta}$ is bounded by the exact planar Gaussian tail

$$
\int_{|\xi|\ge R_j^{1+\eta}}e^{-\pi|\xi|^2/R_j^2}\,d\xi
=R_j^2e^{-\pi R_j^{2\eta}}=o(R_j^q).
\tag{9}
$$

Equations (6), (8), and (9) show that the intermediate region contributes at least $(c_0/2)R_j^q$ for all sufficiently large $j$. Its Gaussian weight is at most one, and it is covered by at most $2\eta N_j+3$ dyadic annuli. Therefore one of them, with index $n_j$ satisfying

$$
(1-\eta)N_j-1\le n_j\le(1+\eta)N_j+1,
\tag{10}
$$

has

$$
\int_{2^{n_j}\le|\xi|<2^{n_j+1}}|\widehat\sigma(\xi)|^2\,d\xi
\ge\frac{c_\eta}{N_j}\,2^{qN_j},
\tag{11}
$$

where $c_\eta>0$ is fixed. This is an existence statement about some annulus in the specified window, not a lower bound for every annulus.

## Quantifiers, exponent comparison, and profile control

Given $\tau>0$ and $\epsilon>0$, put

$$
\epsilon_0=\min\{\epsilon,q/2\},
$$

and choose

$$
0<\eta<\min\left\{\frac14,\frac{\tau}{16},\frac{\epsilon_0}{8q}\right\}.
\tag{12}
$$

For all sufficiently large $j$, (10) gives $n_j\le(1+2\eta)N_j$, and

$$
(q-\epsilon_0)n_j
\le(q-\epsilon_0)(1+2\eta)N_j
\le(q-3\epsilon_0/4)N_j.
$$

The logarithm of the polynomial loss in (11) is smaller than $(3\epsilon_0/4)N_j$ for all sufficiently large $j$. Hence (11) implies

$$
\int_{2^{n_j}\le|\xi|<2^{n_j+1}}|\widehat\sigma(\xi)|^2\,d\xi
\ge2^{(q-\epsilon_0)n_j}
\ge2^{(q-\epsilon)n_j}.
\tag{13}
$$

For the profile control, put $G(t)=F(t)-t$. This is 1-Lipschitz and $G(0)=0$, so for positive $n,N$,

$$
\left\|\frac{G(nx)}n-\frac{G(Nx)}N\right\|_{L^\infty_x([0,1])}
\le\frac{2|n-N|}{n}.
\tag{14}
$$

Indeed split the difference into the change in the argument and the change in the denominator; each is at most $|n-N|/n$ since $|G(Nx)|\le N$.

By (10), for sufficiently large $j$, the right side of (14) is at most $4\eta+4/N_j$. Using (4), (14), and (1),

$$
\|g^{(k)}_{n_j}-g\|_\infty
\le\frac{F(k)}{n_j}+4\eta+\frac4{N_j}
+\left\|\frac{G(N_jx)}{N_j}-g(x)\right\|_\infty.
\tag{15}
$$

The second term is less than $\tau/4$ by (12), and each of the other three terms is at most $\tau/4$ for sufficiently large $j$. This proves the profile part of (2). Finally $N_{j-1}/N_j\to0$, so the windows in (10) are eventually disjoint; the obtained $n_j$ are infinitely many distinct integers.

This proves the proposition with all quantifiers in the stated order. The same separated supports work for every $\tau$ and $\epsilon$; only the selected annuli depend on those tolerances.

## Consequence for further research

An improvement cannot simply assume that near-extremal pin profiles force a better raw source Fourier-energy exponent. The examples above have both obstructions at the same frequencies. They remain compatible with improvements using angular distribution, the good-packet energy, cancellation not measured by the raw energy, correlated summation, or a different analytic criterion. In particular, they do not show that the present dimension threshold is necessary for positive-length distances.
