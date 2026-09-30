# Realizing the sharp profiles in one Frostman measure

Date: 2026-09-30.

This note addresses a possible way around the sharp universal profile bounds: perhaps their matching profiles cannot occur at arbitrarily large scales of one measure. They can. In fact they occur for a compact homogeneous dyadic product set with exactly the prescribed Hausdorff and packing dimensions, and every large component of a finite regularization remains close to the same profile at those scales.

There is also a precise obstruction to the *single-collapse* profile occurring at every large scale: its near occurrences have logarithmic upper density tending to zero with the approximation tolerance. That sparsity does not, by itself, make positive-power Fourier losses summable.

These are statements about mass profiles. No set with null pinned distance sets is constructed or claimed.

## 1. A realization theorem

Fix

$$
0<a<b\le1,\qquad d=1+a,\qquad D=1+b.
$$

Let a template $g:[0,1]\to\mathbb R$ satisfy:

- $g$ is 1-Lipschitz;
- $ax\le g(x)\le bx$;
- $g(1)=a$;
- for some $c>0$, $g(x)=bx$ on $[0,c]$.

Put $h(x)=x+g(x)$. Then $h$ is nondecreasing and 2-Lipschitz,

$$
dx\le h(x)\le Dx,\qquad h(1)=d,\qquad h(x)=Dx\quad(0\le x\le c).
$$

**Theorem.** There are a compact set $E\subset[0,1]^2$, a probability $\mu$ supported on $E$, integers $N_j\to\infty$, and an integer-grid branching function $F_{\rm dyad}$ such that:

1. every occupied half-open dyadic square of depth $n$ has mass $2^{-F_{\rm dyad}(n)}$;
2. $\mu(B(x,r))\le C r^d$ for every $x$ and $0<r\le1$;
3. $\dim_H E=d$ and $\dim_P E=\overline{\dim}_{\rm B}E=D$;
4. if $F_{\rm dyad}$ is interpolated linearly, then

$$
\sup_{0\le x\le1}
\left|\frac{F_{\rm dyad}(N_jx)}{N_j}-x-g(x)\right|\longrightarrow0.
$$

In particular the single-collapse and two-collapse matching profiles in the hard-gap proof are both realized along infinitely many scales of a *single* Frostman probability with the desired exact dimensions.

### Construction of the cumulative branching function

Choose integers $N_0=0<N_1<N_2<\cdots$ so that

$$
\frac{N_{j-1}}{N_j}<c,
\qquad
\frac{N_{j-1}}{N_j}\longrightarrow0.
$$

For example, sufficiently fast superexponential growth works. On each interval $[N_{j-1},N_j]$, define

$$
F(t)=\max\left\{dt,
N_jh(t/N_j)-(D-d)N_{j-1}\right\}.
\tag{1}
$$

At the left endpoint, the second entry is

$$
DN_{j-1}-(D-d)N_{j-1}=dN_{j-1};
$$

at the right endpoint the maximum equals $dN_j$. Thus the pieces join continuously. Both entries in (1) are nondecreasing and 2-Lipschitz, so the same is true of $F$. Also

$$
dt\le F(t)\le Dt,
\qquad F(N_j)=dN_j.
\tag{2}
$$

For every $0\le t\le N_j$, one has

$$
0\le N_jh(t/N_j)-F(t)\le(D-d)N_{j-1}.
\tag{3}
$$

For $t\ge N_{j-1}$ this follows directly from (1) and $h(t/N_j)\ge dt/N_j$. For $t\le N_{j-1}$, the template is in its initial linear part, so the left expression is $Dt-F(t)$, which is between zero and $(D-d)t$ by (2).

Choose a fixed $c_0\in(0,c]$. At $t=c_0N_j$, equations (2)--(3) imply $F(t)/t\to D$. Together with (2) and the endpoints, this proves

$$
\liminf_{t\to\infty}\frac{F(t)}t=d,
\qquad
\limsup_{t\to\infty}\frac{F(t)}t=D.
\tag{4}
$$

### Dyadic realization

For integers $n\ge0$, set

$$
S(n)=\left\lfloor\frac{F(n)}2\right\rfloor,
\qquad F_{\rm dyad}(n)=2S(n).
$$

Because $F$ is nondecreasing and 2-Lipschitz,

$$
S(n)-S(n-1)\in\{0,1\}.
$$

Let $A$ be the set of integers where this difference is one. Define

$$
C_A=\left\{\sum_{n=1}^{\infty}\varepsilon_n2^{-n}:
\varepsilon_n\in\{0,1\}\ (n\in A),\quad
\varepsilon_n=0\ (n\notin A)\right\},
\qquad E=C_A\times C_A.
$$

On each active binary digit in each coordinate put an independent fair bit, and let $\mu$ be the resulting product probability. The number of occupied depth-$n$ dyadic squares is $2^{2S(n)}$, each of mass $2^{-2S(n)}$. Binary-expansion ambiguities have measure zero: there are infinitely many active digits, and any prescribed infinite tail of those digits has probability zero. Thus the assertion about half-open dyadic square masses is exact.

At integers,

$$
F(n)-2<F_{\rm dyad}(n)\le F(n).
$$

Linear interpolation changes the comparison with the continuous $F$ by at most another two. Consequently (3) gives

$$
\sup_{x\in[0,1]}
\left|\frac{F_{\rm dyad}(N_jx)}{N_j}-h(x)\right|
\le\frac{(D-d)N_{j-1}+4}{N_j}\longrightarrow0.
\tag{5}
$$

### Frostman bound and dimensions

A ball of radius $2^{-n}$ meets at most an absolute constant number of depth-$n$ dyadic squares. Hence

$$
\mu(B(z,2^{-n}))\le C2^{-F_{\rm dyad}(n)}
\le4C2^{-dn}.
\tag{6}
$$

Choosing a neighboring dyadic radius proves the stated $d$-Frostman bound for every radius. The mass-distribution argument gives $\dim_HE\ge d$.

At $n=N_j$, the support is covered by $2^{F_{\rm dyad}(N_j)}\le2^{dN_j}$ squares of diameter $\sqrt2\,2^{-N_j}$. For each $s>d$, the sum of the $s$th powers of these diameters tends to zero. Therefore $\dim_HE\le d$.

The upper box dimension equals $\limsup_nF_{\rm dyad}(n)/n=D$. For the upper bound use all occupied dyadic squares. For the lower bound, (6) before its last inequality implies that every radius-$2^{-n}$ ball has mass at most $C2^{-F_{\rm dyad}(n)}$, so at least $C^{-1}2^{F_{\rm dyad}(n)}$ such balls are required to cover $E$.

For completeness, the packing lower bound does not require any uniform-separation assumption on the dyadic cylinders. Use the standard modified-upper-box characterization

$$
\dim_PE=\inf_{E\subset\bigcup_iE_i}\sup_i\overline{\dim}_{\rm B}E_i,
\tag{7}
$$

where the sets in the countable cover can be taken bounded. Given any such cover, some $E_i\cap E$ has positive $\mu$ outer measure. If that set is covered by $M$ radius-$2^{-n}$ balls, outer subadditivity and the preceding ball estimate give

$$
\mu^*(E_i\cap E)\le MC2^{-F_{\rm dyad}(n)}.
$$

Thus $\overline{\dim}_{\rm B}E_i\ge D$. Equation (7) gives $\dim_PE\ge D$; the opposite bound follows from $\dim_PE\le\overline{\dim}_{\rm B}E=D$.

The characterization (7) is recalled, for example, in Falconer's primary research paper [A capacity approach to box and packing dimensions of projections of sets and exceptional directions](https://research-repository.st-andrews.ac.uk/bitstream/handle/10023/17263/CapacityProjections_Falconer.pdf?sequence=1), in its discussion of packing dimension through countable upper-box covers.

## 2. The matching profiles satisfy the hypotheses

The single-collapse profile is

$$
g(x)=\min\{bx,1+a-x\}.
\tag{8}
$$

Its initial linear interval extends to

$$
p=\frac{1+a}{1+b}.
$$

It has endpoint $a$, is 1-Lipschitz, and has the required barriers. The realization theorem applies for every $0<a<b\le1$.

The matching two-collapse profile in the proven parameter region is

$$
g(x)=\min\{bx,at+|x-t|,1+a-x\},
\tag{9}
$$

where $t$ is the positive parameter specified in the hard-gap proof. That proof checks the barriers and endpoint. The second and third entries are strictly positive at zero, whereas the first is zero; continuity therefore supplies a nontrivial initial interval on which (9) equals $bx$. It too satisfies the realization theorem.

## 3. The limiting cost survives the realization

The uniform approximation in (5) also approximates the limiting optimal chain cost. Here is a direct stability proof.

For a 1-Lipschitz function $g$ on $[0,1]$, let $\Psi_g(n)$ be the infimum of costs of admissible finite chains from $n<1$ to zero. If $n<n'<1$, truncating a chain at $n$ proves

$$
\Psi_g(n)\le\Psi_g(n').
$$

Conversely, an admissible chain from $n'$ down to $n$ can be constructed by successively doubling the complementary distance $1-x$, ending exactly at $n$. The total cost is at most the negative variation on $[n,n']$, hence at most $n'-n$. Therefore

$$
0\le\Psi_g(n')-\Psi_g(n)\le n'-n.
\tag{10}
$$

In particular the limiting cost $\Phi_0(g)=\lim_{n\uparrow1}\Psi_g(n)$ exists, and

$$
0\le\Phi_0(g)-\Psi_g(1-\zeta)\le\zeta.
\tag{11}
$$

Merging consecutive admissible edges does not increase cost: for $l<m<n$,

$$
c_g(l,n)\le c_g(l,m)+c_g(m,n).
$$

After all possible neighboring mergers, every two edges more than double $1-n$. Thus at starting point $1-\zeta$ it suffices to use at most

$$
K(\zeta)=2\left\lceil\log_2(1/\zeta)\right\rceil+4
$$

edges. A perturbation $\|g-h\|_\infty\le\epsilon$ changes each edge cost by at most $2\epsilon$. Infimizing over the bounded-length chains and using (11) gives

$$
|\Phi_0(g)-\Phi_0(h)|\le2\zeta+2K(\zeta)\epsilon.
\tag{12}
$$

First fixing $\zeta$, then letting $\epsilon\to0$, then letting $\zeta\to0$, proves continuity. The interpolated normalized dyadic profiles are 1-Lipschitz, because their slopes are $-1$ or $1$. Therefore their costs converge along $N_j$ to the matching template cost.

This realizes the previously proved sharp costs within one actual Frostman measure, rather than only within an abstract class of Lipschitz functions.

## 4. Finite regularization cannot remove the profile at those scales

Let a homogeneous measure have depth-$k$ cube masses exactly $2^{-F_{\rm dyad}(k)}$. Fix a depth $N$, a union $X$ of depth-$N$ cubes with $w=\mu(X)>0$, and $\sigma=\mu|_X/w$. Suppose a regularized mass exponent $f(k)$ satisfies, for every occupied depth-$k$ cube,

$$
2^{-f(k)-eN}\le\sigma(Q)\le2^{-f(k)}.
\tag{13}
$$

Then

$$
F_{\rm dyad}(k)+\log_2w-eN\le f(k)\le F_{\rm dyad}(k).
\tag{14}
$$

For the lower bound, combine the left side of (13) with

$$
\sigma(Q)\le\mu(Q)/w=2^{-F_{\rm dyad}(k)}/w.
$$

For the upper bound, there are at most $2^{F_{\rm dyad}(k)}$ occupied cubes, each of mass at most $2^{-f(k)}$, and their masses sum to one. This proves (14).

In particular, if $w\ge2^{-\gamma N}$, the profile is changed by at most $(\gamma+e)N$. At the realization scales $N_j$, every such regular component remains close to the same template when the regularization losses are small. This excludes the simple repair of discarding the matching profile by selecting only large regular components.

This does not exclude using extra geometric information within the components, changing the analytic estimate, or correlating choices across different frequencies.

## 5. A quantitative obstruction to all-scale single collapse

A single global profile cannot resemble (8) at every large scale. More precisely, let $G:[0,\infty)\to\mathbb R$ be any function and define its normalized prefixes

$$
g_N(x)=\frac{G(Nx)}N.
$$

Let $g$ be (8). Suppose both $\|g_N-g\|_\infty\le\epsilon$ and $\|g_M-g\|_\infty\le\epsilon$, where $0<M<N$, and put $r=M/N$. From the endpoint of the smaller profile and the value of the larger profile at $r$,

$$
|g(r)-ra|\le\epsilon(1+r).
\tag{15}
$$

If $r\le p=(1+a)/(1+b)$, (15) becomes

$$
r(b-a)\le\epsilon(1+r),
$$

so, provided $\epsilon<b-a$,

$$
r\le L_\epsilon:=\frac{\epsilon}{b-a-\epsilon}.
\tag{16}
$$

If $r\ge p$, it becomes

$$
(1+a)(1-r)\le\epsilon(1+r),
$$

and hence

$$
r\ge U_\epsilon:=\frac{1+a-\epsilon}{1+a+\epsilon}.
\tag{17}
$$

Consequently any two near occurrences satisfy the dichotomy

$$
\boxed{\quad M/N\le L_\epsilon\quad\text{or}\quad M/N\ge U_\epsilon.\quad}
\tag{18}
$$

For sufficiently small positive $\epsilon$, one has $0<L_\epsilon<U_\epsilon<1$. Write

$$
\ell_\epsilon=\log(1/L_\epsilon),
\qquad w_\epsilon=\log(1/U_\epsilon).
$$

In logarithmic scale, no two near occurrences can have separation strictly between $w_\epsilon$ and $\ell_\epsilon$. In any interval of length less than $\ell_\epsilon$, the near-occurrence set therefore has diameter at most $w_\epsilon$ and Lebesgue measure at most $w_\epsilon$. If $G$ is continuous, the near-occurrence set is measurable, and partitioning long logarithmic intervals gives

$$
\limsup_{L\to\infty}\frac1L
\left|\left\{t\in[0,L]:\|g_{e^t}-g\|_\infty\le\epsilon\right\}\right|
\le\frac{w_\epsilon}{\ell_\epsilon}
=O_{a,b}\!\left(\frac{\epsilon}{\log(1/\epsilon)}\right).
\tag{19}
$$

For the diameter claim, any two points in the same interval have separation less than $\ell_\epsilon$, and (18) forces it to be at most $w_\epsilon$; no connectedness assumption is needed. For (19), first use intervals of length $\ell_\epsilon-\delta$, then let $\delta\downarrow0$.

A simpler obstruction holds for every template in the realization theorem: if $\lambda\le c$ and both scales $N$ and $\lambda N$ have error at most $\epsilon$, then

$$
\lambda(b-a)\le(1+\lambda)\epsilon.
$$

Thus sufficiently accurate near occurrences cannot occupy every large scale for either template.

## 6. What this does and does not settle

The construction proves that consistency across scales, exact Frostman regularity, and exact Hausdorff/packing dimensions do **not** rule out infinitely many matching profiles. Large-component finite regularization also does not remove them at the realization scales. Therefore an argument requiring a uniform strict profile-cost bound at *every* sufficiently large frequency cannot improve the established threshold merely by asserting that its extremizers are unrealizable.

The sparsity estimate (19) is a distinct fact. It does not make a sequence of shell bounds of size $2^{cN_j}$ summable when $c>0$, however fast $N_j$ grows. Nor are the profiles selected by finite regularization of an arbitrary measure automatically normalized prefixes of one global function; applying (19) in that setting would require an additional coherence theorem.

There may still be a stronger method exploiting scale correlations, source energy at the bad scales, geometric information invisible to the branching counts, or a different norm/decomposition. The note establishes no weakest Hausdorff--packing condition for distance sets.

## 7. A further Fourier-energy obstruction

A separate note, [Near-extremal pin profiles and source Fourier-energy saturation at the same scales](2026-09-30-profile-fourier-saturation.md), proves a related statement for fixed separated source and pin restrictions of this construction. For every positive profile tolerance and exponent loss, there are infinitely many common scales at which the pin profile is near the template and the source's raw annular Fourier energy nearly attains the Frostman exponent. Its proof uses Gaussian pair counting, low-frequency and high-frequency tail bounds, and a nearby-annulus selection; it does not assume that the final branching block stays flat through the endpoint.

That observation still does not control the refined good-packet geometry or provide a distance-set counterexample.
