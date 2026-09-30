# Synchronized source and pin profiles: an energy obstruction and a bilinear target

30 September 2026. This note investigates whether regularizing both source and pin measures can improve the high-slope distance criterion merely by improving the source Fourier-energy factor. It proves a fixed-measure obstruction to that approach. It also isolates a positive collision term that the current quadratic inflation treats too expensively. No improved dimension-only distance theorem is claimed.

## 1. A fixed measure realizing both sharp features

Fix

$$
1<s<u\le2.
$$

There exist a compact planar set $K$, a probability $\mu$ supported on $K$, and dyadic frequencies $R_k\to\infty$ with all the following properties:

$$
\dim_H K=s,\qquad \dim_P K=u,
$$

$$
\mu(B(x,r))\le C r^s,\qquad I_s(\mu)<\infty,
\qquad N(K,r)\le C r^{-u},
$$

and, for a fixed nonzero nonnegative smooth function $\Psi$ supported in $1<|\xi|<2$,

$$
\int |\widehat\mu(\xi)|^2\Psi(\xi/R_k)\,d\xi
\asymp \frac{R_k^{2-s}}{(\log R_k)^2}.
\tag{1}
$$

Moreover, along the corresponding terminal depths $N_k$, its homogeneous dyadic entropy profiles converge uniformly to

$$
\frac{f(N_k x)}{N_k}\longrightarrow \min\{ux,s\},
\qquad 0\le x\le1.
\tag{2}
$$

Consequently the shifted profiles converge to

$$
\frac{f(N_k x)-N_kx}{N_k}
\longrightarrow
\min\{(u-1)x,s-x\}.
\tag{3}
$$

For $a=s-1$ and $b=u-1$, this is exactly the single-collapse profile

$$
g(x)=\min\{bx,1+a-x\}
$$

that realizes the sharp high-slope unforced chain constant.

Taking a sufficiently large translation vector $v$, the two separated probabilities $\mu$ and $(x\mapsto x+v)_*\mu$ are supported on subsets of the one set $K\cup(K+v)$, which still has Hausdorff dimension $s$ and packing dimension $u$. Their finite-scale profiles are identical. Thus using a common ambient set, or synchronizing the two profiles, does not eliminate this example.

### Construction of the entropy sequence

Construct an integer sequence $f(n)$ with increments in $\{0,1,2\}$. It alternates long growth intervals with increments averaging $u$ and intervals with zero increments.

Set $N_0=0$ and $f(0)=0$. Having defined the sequence through $N_{k-1}$, choose an integer $P_k>N_{k-1}$ so large that

$$
\frac{P_k}{N_{k-1}+1}\longrightarrow\infty
$$

and all the requirements below hold. On the growth interval put

$$
f(n)=f(N_{k-1})+\lfloor u(n-N_{k-1})\rfloor,
\qquad N_{k-1}\le n\le P_k.
$$

Choose $N_k\ge P_k$ to be the largest integer such that

$$
sN_k+2\log_2(N_k+2)\le f(P_k),
$$

and set $f(n)=f(P_k)$ for $P_k<n\le N_k$. Choosing $P_k$ sufficiently large ensures that such an $N_k$ exists and exceeds $P_k$.

The growth increments are $1$ or $2$, since $1<u\le2$, and the intervening increments are zero. Inductively,

$$
f(n)\le un.
\tag{4}
$$

At the terminal depths,

$$
f(N_k)=sN_k+2\log_2(N_k+2)+O_s(1).
\tag{5}
$$

There is also a constant independent of $n$ such that

$$
f(n)\ge sn+2\log_2(n+2)-C.
\tag{6}
$$

To check (6), it holds without the constant on each zero-increment interval by the definition of its endpoint. On a subsequent growth interval, writing $n=N_{k-1}+\ell$ gives

$$
f(n)-sn\ge2\log_2(N_{k-1}+2)+(u-s)\ell-1.
$$

Once $N_{k-1}$ is large, the logarithmic increase is bounded by $(u-s)\ell$, because the derivative of $2\log_2 x$ is $2/(x\log 2)$. The finite initial interval is absorbed in $C$.

Since $P_k/N_{k-1}\to\infty$,

$$
\frac{f(P_k)}{P_k}\longrightarrow u,
\qquad
\frac{N_k}{P_k}\longrightarrow\frac us,
\qquad
\frac{f(N_k)}{N_k}\longrightarrow s.
\tag{7}
$$

During the last growth interval, $f(n)$ differs from $un$ by $O(N_{k-1}+1)$. During the last zero-increment interval it differs from $sN_k$ by $O(\log N_k)$. The earlier part has length $N_{k-1}=o(N_k)$. These observations prove the uniform convergence (2), using piecewise-linear interpolation of $f$.

### The homogeneous dyadic measure

At level $n$, use the same branching rule in every occupied dyadic square:

- if $f(n)-f(n-1)=2$, retain all four children;
- if the increment is $1$, retain the two children with vertical digit zero;
- if it is $0$, retain only the lower-left child.

Assign equal mass to all retained children. The resulting compact limit set is $K$ and the resulting probability is $\mu$. Every occupied level-$n$ square has mass $2^{-f(n)}$, and there are $2^{f(n)}$ such squares. Both coordinates branch infinitely often, so dyadic boundary ambiguities have measure zero.

A ball of radius $2^{-n}$ meets only a bounded number of level-$n$ squares. Hence

$$
\mu(B(x,2^{-n}))\le C2^{-f(n)}
\le C2^{-sn}(n+2)^{-2}.
\tag{8}
$$

This gives the stated Frostman bound. Summing the usual dyadic energy annuli gives

$$
I_s(\mu)\le C+C\sum_{n\ge0}2^{sn-f(n)}<\infty.
$$

Equation (4) gives the uniform covering estimate $N(K,r)\le Cr^{-u}$. The Frostman estimate implies $\dim_H K\ge s$, while the covers at depths $N_k$ and (5) imply $\dim_H K\le s$.

For completeness, packing dimension is also exactly $u$. It is at most $u$ by the covering bound. If it were smaller, its countable-cover characterization would cover $K$ by sets of upper box dimension bounded by some $v<u$. Taking closures makes the cover measurable, and at least one member $A$ has positive $\mu$-mass. But along $P_k$,

$$
\mu(A)\le C N(A,2^{-P_k})2^{-f(P_k)}\longrightarrow0,
$$

because $f(P_k)/P_k\to u>v$. This is a contradiction.

### Annular energy calculation

Let

$$
M_k=2^{f(P_k)}=2^{f(N_k)}.
$$

The zero digits between $P_k$ and $N_k$ place the descendants of each occupied level-$P_k$ square in a microscopic copy at its lower-left corner. Homogeneity gives an exact representation

$$
\mu=\frac1{M_k}\sum_{j=1}^{M_k}
(T_{x_{k,j}}\circ D_{2^{-N_k}})_*\nu_k,
\tag{9}
$$

where $\nu_k$ is a probability on $[0,1]^2$, $T_x$ is translation by $x$, and $D_r$ is dilation by $r$. Distinct corners $x_{k,j}$ have separation at least $2^{-P_k}$.

Choose a sufficiently small fixed dyadic number $\epsilon>0$ and put $R_k=\epsilon2^{N_k}$. Then $|\widehat\nu_k(\epsilon\eta)|\ge1/2$ for all $|\eta|\le2$, uniformly in $k$. This follows directly from the bounded support and total mass one. For fixed nonzero $\Psi\ge0$ in $C_c^\infty(\{1<|\eta|<2\})$, let

$$
\Phi_k(\eta)=\Psi(\eta)|\widehat\nu_k(\epsilon\eta)|^2.
$$

These functions have uniformly bounded derivatives of every fixed order, fixed compact support, and integrals bounded below by a positive constant. Their inverse Fourier transforms therefore satisfy uniform Schwartz estimates.

Using (9), expanding the square, and rescaling frequency gives

$$
\int|\widehat\mu(\xi)|^2\Psi(\xi/R_k)\,d\xi
=
\frac{R_k^2}{M_k^2}
\sum_{i,j}\check\Phi_k(R_k(x_{k,i}-x_{k,j})).
\tag{10}
$$

The diagonal terms are comparable to $R_k^2/M_k$. For each fixed integer $L$, the sum of absolute values of all off-diagonal terms is at most

$$
C_LR_k^2\bigl(R_k2^{-P_k}\bigr)^{-L}.
$$

By (7), $N_k-P_k\sim(1-s/u)N_k$. Choosing $L$ large enough makes this error $o(R_k^2/M_k)$. Finally (5) gives

$$
M_k\asymp R_k^s(\log R_k)^2,
$$

which proves (1).

### Precise obstruction supplied by this construction

For every $\varepsilon>0$, the fixed measure above violates an estimate

$$
\int|\widehat\mu(\xi)|^2\Psi(\xi/R)\,d\xi
\le C_\mu R^{2-s-\varepsilon}
$$

along $R_k$. This remains true with a finite $I_s(\mu)$ and with synchronized sharp source and pin profiles. Therefore those facts alone do not yield a power saving in the global annular source-energy factor of the current proof.

This is not a distance-set counterexample. Nor does it rule out a gain from estimates that use the interaction between source pairs and pins. That interaction is absent from the single global source-energy factor.

## 2. The source clusters giving that energy are cheap in the positive collision formula

Fix a nonnegative mollifier $\varphi\in C_c^\infty(\mathbb R)$ of integral one and set $\widetilde\varphi(t)=\varphi(-t)$ and $K=\varphi*\widetilde\varphi$. For a pin $y$ define

$$
h_{y,\delta}(t)=\int\delta^{-1}\varphi\left(\frac{t-|x-y|}{\delta}\right)\,d\mu(x).
$$

Tonelli gives the exact nonnegative collision identity

$$
\|h_{y,\delta}\|_2^2
=
\iint\delta^{-1}K\left(\frac{|x-y|-|x'-y|}{\delta}\right)
\,d\mu(x)\,d\mu(x').
\tag{11}
$$

For any measurable partition $\{A_j\}$ of the source, the contribution from pairs in the same part satisfies

$$
0\le D_{y,\delta}
\le \|K\|_\infty\delta^{-1}\sum_j\mu(A_j)^2.
\tag{12}
$$

This estimate is uniform in the pin and uses no pin regularity or inflation loss.

For the clusters in (9), take $\delta=R_k^{-1}$. Each cluster has mass $M_k^{-1}$ and diameter at most $\sqrt2\epsilon\delta$. Since $K(0)>0$, reducing $\epsilon$ if necessary also gives a matching lower bound in (12), uniformly for every pin:

$$
D_{y,R_k^{-1}}\asymp\frac{R_k}{M_k}
\asymp\frac{R_k^{1-s}}{(\log R_k)^2}.
\tag{13}
$$

This tends to zero for every $s>1$. Thus the same microscopic self-clusters that saturate the global Fourier-energy input have a directly controlled, decaying contribution to the positive pinned collision integral. Applying the full inflation loss to that contribution is unnecessary in principle.

## 3. A precise remaining bilinear target

More generally, let $\delta_k\to0$ and choose a source partition $\mathcal P_k$. Decompose the nonnegative right side of (11) into pairs in the same partition member and pairs in different members. Suppose

$$
\delta_k^{-1}\sum_{A\in\mathcal P_k}\mu(A)^2\le C
$$

and the averaged contribution from pairs in different members is bounded uniformly:

$$
\int\sum_{\substack{A,B\in\mathcal P_k\\A\ne B}}
\int_A\int_B
\delta_k^{-1}K\left(\frac{|x-y|-|x'-y|}{\delta_k}\right)
\,d\mu(x)\,d\mu(x')\,d\nu(y)
\le C.
\tag{14}
$$

Then the joint mollified pinned laws are bounded in $L^2(d\nu\,dt)$. When source and pins have bounded support, their radial supports lie in a fixed bounded interval after mollification. Weak compactness in this Hilbert space and convergence of the mollified measures identify a subsequential weak limit as the actual joint distance law. Consequently $(d_y)_*\mu$ has an $L^2$ density for $\nu$-almost every pin.

This is a valid conditional criterion with an explicit new target: control (14) without charging the source self-cluster contribution for the full pin-profile loss. It is not yet a bound for (14) in terms of $s,u$.

One cannot replace (14) naively by the signed off-diagonal part of the global Fourier-energy expansion (10). Those terms oscillate and can cancel or be negative, whereas (14) is nonnegative. A successful refinement needs a genuinely bilinear source-pair estimate or another argument that retains the interaction with the pin measure.
