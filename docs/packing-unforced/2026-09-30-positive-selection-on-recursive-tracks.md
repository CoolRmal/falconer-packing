# Positive pair selection on the fixed recursive train tracks

Date: 2026-09-30. This note proves an all-scale positive selection for the fixed compact example in the source-restriction obstruction. It does not improve the dimension criterion, and does not prove a raw L² estimate on an independently chosen product of source and pin subsets.

## 1. A concrete separated pair

Let K and μ be the fixed recursive construction with

$$
\dim_H K=\frac{11}{10},\qquad
\overline{\dim}_{\rm B}K=\dim_PK=\frac{13}{11},
$$

and with μ t-Frostman for every 0<t<11/10.

Choose two first-stage child squares Q_A,Q_B with both a horizontal and a vertical separation. For example, use a track whose Cantor digits are all zero and a track whose digits are all 1536, use a central horizontal child in each, and use vertical slat indices zero and N_S/2. Their horizontal separation is greater than 1/3, their vertical separation is 1/32 up to their tiny child diameters, and both contain positive μ mass. Set

$$
A=K\cap Q_A,\quad B=K\cap Q_B,\qquad
\sigma=\frac{\mu|_A}{\mu(A)},\quad
\nu=\frac{\mu|_B}{\mu(B)}.
\tag{1}
$$

These are independent separated restrictions, with both source and pins on K. Both remain t-Frostman for every t<11/10, and the source retains the covering estimate N(A,r)≤Cr^{-13/11}.

For a completely explicit strict exponent choice, use

$$
s_0=\frac{241}{220},\qquad u_0=\frac{13}{11},
\qquad 2s_0-1-u_0=\frac1{110}>0.
\tag{2}
$$

The coherent integrability proposition in the manuscript therefore applies to σ and ν. If q>1 is its averaged angular exponent and

$$
\vartheta=\frac{q-1}{2q-1},
$$

the raw joint distance law has a nonnegative density

$$
F\in L^p(\nu\times dt),
\qquad
1<p<\left(1-\frac{2\vartheta}{241}\right)^{-1}.
\tag{3}
$$

For ν-almost every pin y, the pinned law of σ has density F(y,·) of mass one. In particular,

$$
|\Delta_y(A)|>0
$$

for ν-almost every y∈B. Thus independent transverse source and pin cylinders already give positive pinned length by the existing coherent theorem. Statement (3) does not assert L².

## 2. One fixed positive pair restriction with a bounded density

The following elementary lemma produces a positive restriction that works simultaneously at every resolution.

**Lemma.** Suppose σ and ν are probabilities and their joint distance law has nonnegative density F∈L^p(ν×dt), p>1. Write

$$
C_p=\int F^p\,d\nu\,dt.
$$

For each threshold H>0 there is a Borel kernel a_H(x,y)∈{0,1} such that, with η_y=a_H(·,y)σ,

$$
\iint (1-a_H(x,y))\,d\sigma(x)d\nu(y)
\le C_pH^{1-p},
\tag{4}
$$

and the selected joint distance law has density

$$
G_H(y,t)=F(y,t)1_{\{F(y,t)\le H\}}.
\tag{5}
$$

Consequently, for ν-almost every y,

$$
0\le G_H(y,t)\le H,\qquad
\|G_H(y,\cdot)\|_2^2\le H,
\tag{6}
$$

and all probability mollifiers satisfy the same L² bound at every positive resolution.

**Proof.** Choose a Borel representative of F and set

$$
a_H(x,y)=1_{\{F(y,|x-y|)\le H\}}.
\tag{7}
$$

Because the joint pushforward is F(ν×dt), changing F on a null set changes a_H only on a σ×ν null set. For any nonnegative Borel test ψ,

$$
\begin{aligned}
\iint \psi(y,|x-y|)a_H(x,y)\,d\sigma(x)d\nu(y)
&=\int \psi(y,t)1_{\{F(y,t)\le H\}}F(y,t)\,d\nu(y)dt.
\end{aligned}
$$

This proves (5), including its conditional pinned version after disintegration. The deleted pair mass equals

$$
\int F1_{\{F>H\}}\,d\nu\,dt
\le H^{1-p}\int F^p\,d\nu\,dt.
$$

Finally, G_H²≤HG_H and every selected pinned mass is at most one. This proves (6); convolution contraction gives the uniform mollified bound. The same kernel (7) is used at every resolution. ∎

Applying this lemma to (1)–(3) proves a fixed positive source–pin selection with arbitrarily small total pair loss and uniformly bounded actual pinned densities.

For instance choose

$$
H=(4C_p)^{1/(p-1)}.
$$

The average retained source mass is at least 3/4. By Markov's inequality, a pin set G⊂B of ν-measure at least 1/2 has retained source mass at least 1/2. On G,

$$
|\Delta_y(A)|\ge\frac1{2H},\qquad
\|G_H(y,\cdot)\|_2^2\le H.
\tag{8}
$$

The length lower bound uses the actual positive source restriction η_y, whose distance support is contained in Δ_y(A).

## 3. What this does and does not resolve

This establishes a positive all-scale selection on the fixed recursive example, despite the failure of every positive source-only restriction against the full pin measure μ. It also shows that two independent transverse cylinders already have positive pinned length. The bounded-density construction itself is elementary once the raw joint law is absolutely continuous: for any density F∈L¹, the mass of F1_{F>H} tends to zero as H tends to infinity. The L^p input supplies the explicit power bound (4).

Conversely, if positive selections with arbitrarily small total pair loss have absolutely continuous selected joint laws, then the original law is absolutely continuous, because the selected laws approach it in total variation and the absolutely continuous measures are closed under this convergence. Therefore the existence of these near-full pair selections is not a new route to a dimension improvement unless their estimates can be obtained before establishing absolute continuity.

The selection (7) depends jointly on source and pin. A positive-measure subset of a product need not contain a positive product rectangle; this argument does not yield independent positive submeasures σ′≤σ and ν′≤ν with a raw L² distance law.

## 4. Why the finite transverse estimate does not by itself prove that stronger claim

The recursive measure factors as

$$
\mu=\mu_x\times\mu_y,\qquad K=K_x\times K_y,
$$

because the track/horizontal-child and vertical-slat indices are independently chosen at every stage. On a pair of transversely separated coarse cylinders, both partial derivatives of the distance function are bounded away from zero. At the end of any one finite block, the elementary slat count gives a bounded conditional mollified density, after rescaling by the parent length.

However, applying that statement independently at each generation only yields multiplicative constants, without a summable perturbation estimate. The fixed child contraction is cδ with c=2^{-10}, whereas neighboring horizontal cell centers are 4δ apart. This leaves genuine subcell gaps. The finite bound is a statement at that block's resolution, not an assertion that its limit measure already has a bounded projection density.

The needed additional estimate would control interactions between distinct source parents after many blocks, or show that the change caused by replacing each last-scale cell by its next block is summable in L² on a fixed positive source–pin product. Neither follows from the one-block bound or from the existing positive-selection theorem. This note makes no raw L² claim for transverse independent cylinders.

For comparison, the recent product-set parabolic method of Li, Liang and Shen, *New York Journal of Mathematics* 32 (2026), Theorem 1.1, assumes ambient dimension at least three. It does not supply a planar L² estimate for this example: [primary paper](https://nyjm.albany.edu/j/2026/32-11p.pdf).
