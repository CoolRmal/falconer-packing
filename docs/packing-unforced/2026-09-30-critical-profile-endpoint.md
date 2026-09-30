# Finite starts and the critical profile endpoint

Date: 2026-09-30. This is a bounded investigation of two possible extensions of the current hard-gap theorem: optimizing the starting scale without sending it to the terminal scale, and replacing a strictly negative Fourier-shell exponent by a zero exponent. It gives rigorous limitations of those particular proposals. It proves neither a counterexample to the distance theorem nor exclusion of its dimensional boundary.

## 1. The exact correction for initial localization

Normalize the profile interval to $[0,1]$. Let $g$ be 1-Lipschitz, put $f(x)=x+g(x)$, and write $n=1-\zeta$. The chain cost from $n$ is

$$
\Phi_\zeta(g)=\inf_{n=n_0>n_1>\cdots>n_k=0}
\sum_{j=0}^{k-1}\left[g(n_{j+1})-\min_{[n_{j+1},n_j]}g\right],
\qquad 2n_j-n_{j+1}\le1.
$$

The current transfer uses the area-ratio loss $2\zeta$ in the initial localization, apart from small positive errors. Regular cube masses give a more precise replacement:

$$
\mathcal I_\zeta(g)
=2\zeta+f(1-\zeta)-f(1)
=\zeta+g(1-\zeta)-g(1).
\tag{1}
$$

In particular $0\le\mathcal I_\zeta(g)\le2\zeta$.

Here is the finite-scale calculation underlying (1). At depth $N$, suppose every occupied terminal cube has mass at most $2^{-f_N(N)}$, while every occupied initial cube $Q$ of depth $n_N$ has mass at least $2^{-f_N(n_N)-e_N}$. Bandwidth $O(R)$, $R=2^N$, permits localization to balls of radius $R^{-1}$. Summing their weights costs at most the largest terminal cube mass times $R^2$. On an enlarged initial cube the unnormalized Lebesgue integral is its normalized average times $O(2^{-2n_N})$, up to the prescribed enlargement factor. Dividing by the mass of the initial cube therefore gives the exponent

$$
2(N-n_N)+f_N(n_N)-f_N(N)+e_N.
\tag{2}
$$

For normalized $f(x)=N^{-1}f_N(Nx)$, the leading term of (2) is $N\mathcal I_\zeta(g)$. The regularization error $e_N$, enlarged supports, and rapidly decreasing tails still have to be paid. The exact profile term is available before those errors.

This is an upper-bound exponent for this particular local-constancy estimate, not a lower bound for every possible Fourier operator estimate. Additional geometry or cancellation could permit a different estimate.

## 2. A variation obstruction to improving the cutoff by a finite start

**Proposition.** For every 1-Lipschitz $g$ and every $0<\zeta<1$,

$$
0\le\Phi_0(g)-\Phi_\zeta(g)
\le \operatorname{Var}^-(g;[1-\zeta,1])
\le\frac12\mathcal I_\zeta(g),
\tag{3}
$$

where $\Phi_0(g)=\lim_{\zeta\downarrow0}\Phi_\zeta(g)$ and $\operatorname{Var}^-$ is negative variation. Consequently

$$
\Phi_\zeta(g)+\mathcal I_\zeta(g)
\ge\Phi_0(g)+\frac12\mathcal I_\zeta(g)
\ge\Phi_0(g),
\tag{4}
$$

and, more precisely,

$$
\inf_{0<\zeta<1}
\bigl(\Phi_\zeta(g)+\mathcal I_\zeta(g)\bigr)=\Phi_0(g).
\tag{5}
$$

**Proof.** If $0<n<n'<1$, truncate any admissible chain from $n'$ when it crosses $n$. Replacing the crossing edge's upper endpoint by $n$ preserves admissibility and can only increase the interval minimum, hence can only decrease its cost. Thus the optimal cost is nondecreasing in the starting point.

For the reverse comparison, form a bridge from $n'$ to $n$ by repeatedly replacing its current point $x$ with $\max\{n,2x-1\}$. Each step is admissible. Until the last step, $1-x$ doubles, so the bridge is finite. On any edge $[m,x]$,

$$
g(m)-\min_{[m,x]}g\le\operatorname{Var}^-(g;[m,x]).
$$

Summing over the bridge and appending an arbitrarily near-minimizing chain from $n$ gives

$$
\Phi_{1-n'}(g)\le\Phi_{1-n}(g)+\operatorname{Var}^-(g;[n,n']).
$$

Monotonicity and boundedness give the limit as $n'\uparrow1$. Lipschitz functions are absolutely continuous, so

$$
\operatorname{Var}^-(g;[n,1])
=\int_n^1(-g'(x))_+\,dx
\le\frac12\int_n^1(1-g'(x))\,dx
=\frac{1-n+g(n)-g(1)}2.
$$

The pointwise inequality used here is $(-v)_+\le(1-v)/2$ for $-1\le v\le1$. This proves (3) and (4). As $\zeta\downarrow0$, both $\mathcal I_\zeta(g)\to0$ and $\Phi_\zeta(g)\to\Phi_0(g)$, giving (5). $\square$

The argument does not require the endpoint clipping $g(1)=a$, piecewise linearity, or the linear barriers. It therefore applies to the actual profiles before endpoint normalization. Grid and regularization errors can only add to this leading upper-bound calculation.

For the coarser initial bound currently written in the transfer, (3) also yields

$$
\Phi_\zeta(g)+2\zeta\ge\Phi_0(g)+\zeta.
\tag{6}
$$

**Consequence for the current optimization.** Optimizing the finite start, even separately for every component and even using the profile-aware initial exponent (1), cannot lower the limiting model cost. If $\Phi_0(g)\ge a$ for one of the already constructed extremal profiles, then every such corrected finite-start cost is at least $a$. Thus finite-start optimization alone cannot remove an equality case of the hard-gap model or extend its sufficient dimensional curve. A stronger initial estimate exploiting information beyond these mass-profile bounds is not excluded.

## 3. A zero shell exponent does not by itself prove positive length

The following elementary construction distinguishes the actual positive-length target from mere control of each increment.

Start from $E_0=[0,1]$. At stage $j\ge1$, subdivide each surviving stage-$(j-1)$ interval into $j+1$ equal intervals and retain the first $j$. Endpoint overlaps have zero Lebesgue measure and can be handled by half-open intervals during the density calculations. Take closed intervals when defining the final compact set. Then

$$
\#\mathcal E_j=j!,\qquad
\ell_j=\frac1{(j+1)!},\qquad
|E_j|=\frac1{j+1}.
$$

Define the probability densities

$$
p_j=(j+1)\mathbf1_{E_j},\qquad p_0=\mathbf1_{[0,1]}.
$$

Each child interval receives the same mass, and the mass of every fixed earlier interval is preserved. Thus $p_j(t)\,dt$ converges weakly to the product probability $\eta$ supported on the compact set

$$
E_\infty=\bigcap_j E_j,
\qquad |E_\infty|=0.
$$

Nevertheless,

$$
\|p_j\|_2^2=j+1,
\qquad
\|p_j-p_{j-1}\|_2^2=1
\quad(j\ge1).
\tag{7}
$$

Indeed $p_{j-1}=j$ on $E_j$, so $\int p_jp_{j-1}=j$, and the second equality follows by expansion. The increments are mutually orthogonal: their conditional averages on every previous-stage interval vanish, while earlier increments are constant on such intervals.

This example even has Hausdorff dimension one. Each stage-$j$ interval has $\eta$-mass $1/j!$. If $\ell_j\le r<\ell_{j-1}$, an interval of length $r$ intersects at most $r/\ell_j+2$ stage-$j$ grid cells, whence

$$
\eta(I)\le 3(j+1)r.
$$

For every fixed $0<t<1$, the quantity

$$
(j+1)\ell_{j-1}^{1-t}=(j+1)(j!)^{-(1-t)}
$$

is bounded. Therefore $\eta(I)\le C_t r^t$ for every interval $I$, and $\dim_H E_\infty=1$. At its natural resolution $R_j=(j+1)!$, the squared approximation norm $j+1$ is smaller than $R_j^\varepsilon$ for every fixed $\varepsilon>0$ and all sufficiently large $j$.

Thus nonnegative probability approximations, mutually orthogonal increments with uniformly bounded squared $L^2$ norm, full Hausdorff dimension of the limiting one-dimensional support, and subpower growth of approximation norms can all coexist with a zero-length limiting support. This is an abstract obstruction to inferring positive length from a zero or arbitrarily small positive shell exponent. These increments are not asserted to be annular Fourier pieces of planar distance measures; the example is not a Falconer counterexample.

## 4. What an endpoint argument would still have to supply

The present transfer gives, schematically,

$$
\|G_R\|_{L^2(d\nu\,dt)}^2
\lesssim R^{1-s+\mathcal C+\eta}I_s(\mu),
\qquad \eta>0,
$$

and a summable first-norm bound for the bad shells. It uses a strictly positive margin to choose a fixed starting fraction, a bounded chain length, deletion thresholds, and a regularization block size. At $\mathcal C=s-1$, that margin disappears. The manuscript does not contain estimates uniform under frequency-dependent choices of all those parameters, nor coefficients sufficient to replace their losses by a summable logarithmic factor.

Even an ideal lossless zero exponent would not finish the argument: (7) explains why uniform bounds on individual squared shell norms need not control the limiting support length. A concrete endpoint mechanism would have to control the full positive approximations, yield a summable square function together with suitable radial-frequency localization, retain a fixed positive mass in approximations with uniformly bounded quadratic norm, or prove another nonconcentration statement strong enough to imply positive length.

There is also a separate dimension-to-measure issue. A set of Hausdorff dimension $d$ need not support a probability of finite $d$-energy. For example, if a compact set has $N(E,r)\le Cr^{-d}$ at all small scales, every probability $\mu$ on it satisfies $I_d(\mu)=\infty$: partition a covering into at most $Cr^{-d}$ measurable pieces of diameter $O(r)$; Cauchy--Schwarz gives $\mu\times\mu\{|x-y|\le O(r)\}\gtrsim r^d$, and integration against $r^{-d-1}\,dr$ diverges. Ahlfors regular sets supply such examples. Thus simply setting $s=d$ in the current energy estimate is not justified by the dimension hypothesis.

No nontrivial dimensional equality case is established by this investigation. The new positive result is the exact finite-start identity (5), which rules out one possible extension mechanism without claiming that the distance theorem's boundary is false.
