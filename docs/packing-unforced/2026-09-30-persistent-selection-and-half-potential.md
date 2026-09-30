# Persistent positive selection and a half-order transverse potential

Date: 2026-09-30.

This note continues the natural-language proof investigation. It leaves the earlier audited train-track note unchanged. There are two substantive conclusions:

- In the finite train-track model, a half-order transverse potential yields a sharper $L^2$ selection theorem. Deleting only the pin's own track succeeds exactly when $u\ge4/3$, matching the earlier neighboring-track counterexample below $4/3$.
- A tempting dimension-only extension with vanishing total deleted mass and a uniformly bounded full retained collision integral is false for **every** vanishing deletion rate. A valid candidate may allow a fixed small total loss, with persistent deletion as one implementation, or use a weaker norm / a different frequency estimate.

No improved Hausdorff–packing distance curve is proved in this note.

## 1. A sharper finite-family estimate

Use the geometry and notation of [Positive good-part selection for train tracks](2026-09-30-positive-train-track-selection.md):

$$
1<s<4/3,\quad 3-2/s\le u\le2,\quad
\alpha=u-1,\quad\beta=(s-1)/2,\quad p=\beta/\alpha,
$$

$$
a=\delta^p,\qquad w=\delta^{1/2},\qquad
h=\delta^{s/2},\qquad r_0=h/w=\delta^\beta,
\qquad m=N_T^{-1}\asymp\delta^\beta.
$$

For a pin $y$, let $r_i=|c_i-y_1|$ be the horizontal offset of a source track. If $r_i\gg w$, the proved cell/slat count gives its mollified density $f_i$ the bounds

$$
\|f_i\|_1=m,
\qquad
\|f_i\|_\infty\le C m(1+r_0/r_i).
\tag{1}
$$

The cell/slat count remains valid for every $r_i\gg w$: the radial width is $O(r_iw+\delta)=O(r_iw)$ because $r_iw\gg w^2=\delta$, even when $r_iw<h$. One must keep the term $1+r_iw/h$ counting visible slats instead of simplifying it to $O(r_iw/h)$.

Consequently

$$
\|f_i\|_2\le C m\sqrt{1+r_0/r_i},
$$

and Minkowski yields

$$
\left\|\sum_{i\in\mathcal I}f_i\right\|_2
\le C\left(1+\sqrt{r_0}\sum_{i\in\mathcal I}m r_i^{-1/2}\right).
\tag{2}
$$

This is an upper bound for the full positive collision norm, including cross-track terms. It uses a half-order transverse potential rather than the first-order potential implicit in the pointwise density estimate.

### Potential estimate

The track-center counting measure satisfies

$$
\sum_{c_i\in J}m\le C(|J|^\alpha+a^\alpha).
$$

For a cutoff $\rho\ge ca$ and tracks with $r_i\ge\rho$, decomposition into dyadic annuli gives

$$
\sum_{r_i\ge\rho}m r_i^{-1/2}
\le
\begin{cases}
C_\alpha\rho^{\alpha-1/2},&0<\alpha<1/2,\\
C\log(2/\rho),&\alpha=1/2,\\
C_\alpha,&1/2<\alpha\le1.
\end{cases}
\tag{3}
$$

For the lower cutoff comparable to $a$, the term $a^\alpha$ is absorbed into the radius term. Each dyadic annulus contributes at most $C(2^j\rho)^{\alpha-1/2}$, proving (3). The same estimate holds after deleting the own track, because every remaining track is at offset at least $ca\gg w$.

**Proposition 1.** The following pin-dependent positive selections give uniformly bounded $L^2$ mollified pinned densities for the finite family.

- If $\alpha\ge1/3$ (equivalently $u\ge4/3$), delete only the pin's own source track. The lost mass is $m\asymp\delta^\beta$.
- If $0<\alpha<1/3$, delete every track with offset less than a sufficiently large constant times

$$
\rho_*=r_0^{1/(1-2\alpha)}=\delta^{\beta/(1-2\alpha)}.
\tag{4}
$$

The lost mass is at most

$$
C\rho_*^\alpha=C\delta^{\alpha\beta/(1-2\alpha)}.
\tag{5}
$$

**Proof.** For $1/3\le\alpha<1/2$, the own-track deletion and (3) give

$$
\sqrt{r_0}\,a^{\alpha-1/2}
=\delta^{\beta(3/2-1/(2\alpha))}\le1.
$$

At $\alpha=1/3$ the exponent is exactly zero, and (3) has no logarithmic loss because $\alpha<1/2$. For $\alpha=1/2$, the remaining factor is $\sqrt{r_0}\log(2/a)$, which is bounded; for $\alpha>1/2$ it is at most $C\sqrt{r_0}$. Equation (2) proves the first assertion.

For $\alpha<1/3$, one has $\rho_*\gg a\gg w$, because

$$
\frac{\beta}{1-2\alpha}<\frac{\beta}{\alpha}=p.
$$

The choice in (4) gives $\sqrt{r_0}\rho_*^{\alpha-1/2}=1$, so (2)--(3) again give a uniform bound. The track-center mass estimate proves (5).

For $u<4/3$, the prior note proves that deleting only the own track leaves a lower bound $c\delta^{3\beta-p}\to\infty$. Thus $u=4/3$ is the exact transition for that particular deletion rule. This is a statement about the finite train-track family, not a new threshold for distance sets.

### A stronger necessary deletion cost below $u=4/3$

The following lower bound helps assess whether (5) is optimal. Assume $0<\alpha<1/3$. If an arbitrary positive selection $\eta_y\le\mu_\delta$ has uniformly bounded averaged mollified squared $L^2$ norm, then its averaged deleted mass obeys

$$
e_\delta\ge c_C\delta^{2\alpha\beta/(1-\alpha)},
\tag{6}
$$

where the constant may depend on the asserted norm bound $C$.

To prove this, choose $\rho\gg a$. Ahlfors regularity and the maximal-net construction give total track mass at offsets $ca\le r_i\le\rho$ between $c\rho^\alpha$ and $C\rho^\alpha$, uniformly in the pin's own track. There are at most $C\rho^\alpha/m$ such tracks. A track at offset $r_i$ has its mollified radial law supported on a union of $N_S$ intervals of total length at most $CN_Sr_iw$. If $q_i$ is its retained source mass, Cauchy–Schwarz gives

$$
\|f_i^{\rm retained}\|_2^2\ge c r_0 q_i^2/r_i.
$$

Positivity allows these lower bounds to be summed. If $r_y$ is the total deleted source mass at the pin, weighted Cauchy–Schwarz yields

$$
\|f_y^{\rm retained}\|_2^2
\ge c r_0\frac{(c\rho^\alpha-r_y)_+^2}{\sum_{ca\le r_i\le\rho}r_i}
\ge c' r_0m\rho^{-1-\alpha}(c\rho^\alpha-r_y)_+^2.
\tag{7}
$$

Average and use Jensen. If $e_\delta\le(c/2)\rho^\alpha$, this gives a lower bound $c''r_0m\rho^{\alpha-1}$. Set

$$
\rho=A_C(r_0m)^{1/(1-\alpha)}.
$$

Choose the fixed constant $A_C>0$ small enough that the latter lower bound exceeds the proposed norm bound $C$. For sufficiently small $\delta$, this radius still satisfies $\rho\gg a$ because $\alpha<1/3$. Therefore $e_\delta>(c/2)\rho^\alpha$, which is (6).

The sufficient exponent in (5) and the necessary exponent in (6) differ for $\alpha<1/3$. They agree with the own-track deletion exponent $\beta$ at $\alpha=1/3$. No exact optimal deletion rate below that point is claimed.

## 2. A dimension-only vanishing-loss candidate is false

Here is a precise candidate one might try to obtain by extending the finite-family selection argument.

**Candidate (false).** Fix $1<s<4/3$ and $3-2/s\le u\le2$. Let $b(\varepsilon)>0$ be a prescribed function tending to zero. For every fixed pair of separated compactly supported probabilities $\mu,\nu$ that are $s$-Frostman and satisfy the $u$-covering bounds, there are positive kernels $\eta_{\varepsilon,y}\le\mu$ such that

$$
\int\bigl(1-\eta_{\varepsilon,y}(\mathbb R^2)\bigr)\,d\nu(y)
\le b(\varepsilon),
\tag{8}
$$

and

$$
\sup_{0<\varepsilon<\varepsilon_0}
\int\|\varphi_\varepsilon*(d_y)_*\eta_{\varepsilon,y}\|_2^2\,d\nu(y)
<\infty.
\tag{9}
$$

The supremum in (9) is allowed to depend on the full measures, not merely their Frostman constants. The candidate still fails, even if (8)--(9) are required only along a sequence of scales tending to zero.

The reason is a general weak-compactness lemma, independent of train tracks.

**Lemma 2.** Let $\mu,\nu$ be compactly supported probabilities. Let $\varepsilon_j\to0$, and let measurable positive kernels $\eta_{j,y}\le\mu$ have averaged deleted mass tending to zero. If the corresponding mollified densities are bounded in $L^2(d\nu\,dt)$, then the *original joint distance law*

$$
\Lambda(dy,dt)=\nu(dy)\,(d_y)_*\mu(dt)
$$

has a density in $L^2(d\nu\,dt)$.

**Proof.** All radial supports lie in a fixed bounded interval after mollification. Write $F_j(y,t)=\varphi_{\varepsilon_j}*(d_y)_*\eta_{j,y}(t)$. A bounded subsequence converges weakly in the Hilbert space $L^2(d\nu\,dt)$ to some $F$. The total variation difference between the measures with density $F_j$ and the fully mollified joint law of $\mu$ is at most the averaged deleted mass, because convolution and pushforward contract total variation. That difference tends to zero. Full mollifications converge weakly to $\Lambda$. Testing against continuous compactly supported functions identifies $\Lambda=F\,d\nu\,dt$. This proves the lemma.

The fixed glued pair in [the off-cluster obstruction](2026-09-30-off-cluster-collision-obstruction.md) has

$$
\int\|\varphi_{\varepsilon_j}*(d_y)_*\mu\|_2^2\,d\nu(y)\longrightarrow\infty.
$$

Its original joint law is therefore not in $L^2$: otherwise Young's convolution inequality would bound every displayed norm by the original joint $L^2$ norm. Lemma 2 disproves the candidate for **every** vanishing function $b$, with no requirement that it be a power or summable. The finite-$I_s$ variant of the same construction supplies the corresponding obstruction when finite energy at the stated exponent is also required.

The original glued construction has $\dim_H\operatorname{supp}\mu=\dim_P\operatorname{supp}\mu=s$. Taking the union of source and translated pin supports preserves these dimensions. Thus this failure can occur even with equal Hausdorff and packing dimensions, where the distance conclusion is already available. It is a failure of the overly strong full-$L^2$ target for a prescribed probability, not of positive-length pinned distances.

## 3. A valid persistent-selection criterion

The vanishing-loss condition in the false candidate is stronger than the needed distance-set conclusion. One valid positive version allows a fixed small total loss. Keeping earlier deletions as the resolution becomes finer is a useful implementation, but nesting is not required by the criterion below.

**Proposition 3.** Let $\mu,\nu$ be compactly supported probabilities and $\varepsilon_j\to0$. Suppose $\eta_{j,y}\le\mu$ are positive measurable kernels with

$$
\int\eta_{j,y}(\mathbb R^2)\,d\nu(y)\ge m_0>0,
\tag{10}
$$

and the mollified densities $F_j$ have uniformly bounded joint $L^2$ norms. Then the original joint law $\Lambda$ has a nonzero absolutely continuous submeasure of mass at least $m_0$. In particular a positive-$\nu$ family of pins has a positive-length distance set from $\operatorname{supp}\mu$.

**Proof.** Take a weak $L^2$ subsequential limit $F$. Positivity passes to this limit, and testing against the indicator of a fixed radial interval containing all supports proves $\int F\,d\nu\,dt\ge m_0$. The mollified submeasures are dominated by the full mollifications. Testing their difference against any nonnegative continuous compactly supported function and passing to the limit gives

$$
F\,d\nu\,dt\le\Lambda.
$$

The marginal in $y$ and uniqueness of disintegration imply $F(y,t)\,dt\le(d_y)_*\mu$ for $\nu$-almost every $y$. Since $\int F>0$, this absolutely continuous component is nonzero for a positive-$\nu$ set of pins. It is supported on their compact distance sets, so those sets have positive Lebesgue measure.

**Fixed-exponent extension.** Both Lemma 2 and Proposition 3 hold with any fixed $1<q<\infty$ in place of two. Use reflexivity of $L^q(d\nu\,dt)$ instead of Hilbert-space weak compactness. Bounded continuous tests and the mass indicator belong to $L^{q'}$ on the common finite joint support, so the identification, domination, and mass arguments are unchanged. The exponent and norm bound are fixed across the sequence; there is no assertion for exponents tending to one.

Section 5 of [the subquadratic transfer note](2026-09-30-subquadratic-profile-transfer.md) proves a fixed train-track joint law has no weak $L^q$ density for

$$
q>\frac{2-s}{3-2s},\qquad 1<s<4/3.
$$

Hence vanishing-loss selections uniformly bounded in strong $L^q$ are impossible for those fixed exponents as well. This quantitative obstruction uses the construction and proof in that companion note; it gives no obstruction for exponents sufficiently close to one.

A standard persistent implementation would choose measurable discarded interaction sets $A_k\subset\operatorname{supp}\mu\times\operatorname{supp}\nu$ with

$$
\sum_{k\ge k_0}(\mu\times\nu)(A_k)<1,
$$

and retain

$$
\eta_{j,y}=\mu\big|_{\{x:(x,y)\notin\bigcup_{k_0\le k\le j}A_k\}}.
\tag{11}
$$

The retained mass has a fixed positive lower bound. Unlike (8), the total deleted mass need not tend to zero; old bad interactions remain removed. A uniform retained collision bound would then prove the distance conclusion by Proposition 3.

The bound must genuinely use the accumulated selection. If one proved a uniform *full-law* collision bound after only the current-scale deletion, whose mass tends to zero, Lemma 2 would reintroduce the contradiction.

### What the positive selection criterion amounts to

For fixed $\mu,\nu$, existence of some positive source–pin restriction of positive total mass with joint $L^2$ distance density is equivalent to the original joint law having a nonzero absolutely continuous component. One direction follows by domination. For the other, write the absolutely continuous component as $f\,d\nu\,dt$, discard a null set carrying the singular component, and restrict further to $0<f\le M$ for a large finite $M$ with positive retained mass. Lift this measurable restriction through $(y,x)\mapsto(y,|x-y|)$. The resulting positive source–pin restriction has a bounded joint distance density and positive mass.

Similarly, allowing arbitrarily small fixed loss is equivalent to absolute continuity of the full joint law. The $L^2$ bound may deteriorate as that fixed loss decreases; a bound uniform in the loss would again force the entire joint law into $L^2$. This equivalence explains why the geometric existence of a persistent good part is a substantial mathematical task, rather than a consequence of a generic measure decomposition.

## 4. Remaining proof target

The half-order estimate (2) is a concrete gain for the train-track test family and gives an exact threshold for its simplest interaction deletion. Its proof depends on geometric facts stronger than Hausdorff and packing dimension: ordered slats, transverse radial derivatives, and counts of slats meeting a radial interval.

To improve the dimensional theorem by this route, one would need a dimension-only construction of persistent discarded interaction sets in (11), together with a quantitative replacement for (2) controlling the retained positive cross-cluster collision integral. The fixed-measure counterexample rules out a version with vanishing *total* loss and a uniform full-law $L^2$ bound; it does not rule out persistent selection, frequency-local estimates, or $L^p$ control below two. Establishing such a geometric decomposition remains open here.
