# Selected-cap embedding: superposition audit and a weighted variant

Date: 2026-09-30.

This note checks the actual proposition in output/pdf/packing-unforced-embedding.tex and its application in output/pdf/packing-unforced-transfer.tex. The adversarial test is whether fine labels selected differently in different children create a missing angular or scale factor. No published source was edited.

The direct proof below gives the printed estimate with arbitrary child-dependent complex coefficients of modulus at most one, under a weighted tube condition. In particular it proves the original zero-one statement and a concrete soft-selection version. I found no counterexample under the printed hypotheses. No improved dimension bound is claimed.

## 1. A weighted form of the embedding

Use the proposition's notation: child and parent side lengths are respectively $$a\le b$$, and

$$
Q^+=L^{2j+2}Q,\qquad
\widetilde Q=LQ^+,\qquad
P^+=L^{2j+4}P,
$$

$$
w_Q=\sigma(Q^+),\qquad M=\sigma(P^+),\qquad
\Lambda\le C L^{4j+4}.
$$

Assume the same frequency rectangles, bounded-overlap containing balls, and direction-mismatch hypotheses as in the printed proposition. Replace its selectors by complex constants $$c_{Q,\theta}$$ with $$|c_{Q,\theta}|\le1$$. For every label and every translate $$U$$ of a width-by-length $$a$$-by-$$b$$ dual rectangle in its actual Fourier direction, assume

$$
\sum_{\{Q:\widetilde Q\cap U\ne\varnothing\}}
w_Q|c_{Q,\theta}|^2
\le \Lambda H\frac ab M.
\tag{W}
$$

The conclusion is

$$
\begin{aligned}
&\sum_Qw_Q
\int_{Q^+}\left|\sum_\theta c_{Q,\theta}f_\theta\right|^2dm_{Q^+}\\
&\quad\le C L^{8j+14}HM
\sum_\theta\int_{P^+}|f_\theta|^2dm_{P^+}
+C_mMa^{-2}L^{-m}\sum_\theta\|f_\theta\|_2^2.
\end{aligned}
\tag{1}
$$

As in the printed statement, the function for a fixed label must be independent of the child. The coefficients are constants on each child's averaging integral; they are not functions of the integration variable.

### Local orthogonality for arbitrary phases

The cutoff used in the manuscript yields

$$
\left\|v_Q\sum_\theta c_{Q,\theta}f_\theta\right\|_2^2
\le C B_0\sum_\theta |c_{Q,\theta}|^2\|v_Qf_\theta\|_2^2.
\tag{2}
$$

Indeed, let the radius of the original containing balls be $$r=C_0/a$$. The cutoff's Fourier support has radius at most $$1/a\le r$$. The new supports lie in doubled balls. If a point belongs to a number of these doubled balls, their original balls all lie inside the ball of radius $$3r$$ about that point. Integrating the original overlap bound shows that their number is at most $$9B_0$$. Plancherel and pointwise Cauchy--Schwarz prove (2). This argument permits arbitrary phases and has no factor counting labels.

Schwartz decay outside the further enlarged child and normalization of the two averages give, for every decay order,

$$
\begin{aligned}
&\int_{Q^+}\left|\sum_\theta c_{Q,\theta}f_\theta\right|^2dm_{Q^+}\\
&\quad\le C L^2\sum_\theta |c_{Q,\theta}|^2
\int_{\widetilde Q}|f_\theta|^2dm_{\widetilde Q}
+C_pa^{-2}L^{-p}\sum_\theta\|f_\theta\|_2^2.
\end{aligned}
\tag{3}
$$

The main coefficient is exactly the ratio of the two averaging areas.

### Positive weighted measures and the dimensional cancellation

Define

$$
\tau_\theta=\sum_Qw_Q|c_{Q,\theta}|^2m_{\widetilde Q}.
$$

Condition (W) and the child overlap imply

$$
\tau_\theta(U)\le\Lambda H(a/b)M,\qquad
\tau_\theta(\mathbb R^2)\le\Lambda M.
\tag{4}
$$

The reproducing kernel for the frequency rectangle satisfies

$$
|k_\theta(z)|\le\frac{C_p}{ab}
\left(1+\frac{|z\cdot u_\theta^\perp|}{a}
+\frac{|z\cdot u_\theta|}{b}\right)^{-p},
\qquad \|k_\theta\|_1\le C.
$$

Partitioning space into dual rectangles and summing their decay gives

$$
\int|k_\theta(x-y)|\,d\tau_\theta(x)
\le\frac C{ab}\Lambda H\frac ab M
=C\frac{\Lambda HM}{b^2}.
\tag{5}
$$

This computation shows the cancellation of the aspect ratio and the single occurrence of the threshold.

The support of the averaging measure is at distance at least $$Lb$$ from the complement of the enlarged parent. Outside that parent the kernel integral in (5) is instead at most

$$
C_p\frac{\Lambda M}{ab}L^{-p}.
$$

The reproducing identity and Cauchy--Schwarz consequently give

$$
\int|f_\theta|^2d\tau_\theta
\le C\frac{\Lambda HM}{b^2}\int_{P^+}|f_\theta|^2dy
+C_p\frac{\Lambda M}{ab}L^{-p}\|f_\theta\|_2^2.
\tag{6}
$$

Multiplying (3) by the child weights, summing, and applying (6) yields the main coefficient

$$
L^2\Lambda\frac{|P^+|}{b^2}
\le C L^{2+4j+4+4j+8}
=C L^{8j+14}.
$$

The error is bounded by a constant times

$$
Ma^{-2}L^{4j+6-p}\sum_\theta\|f_\theta\|_2^2,
$$

using $$1/(ab)\le1/a^2$$. Increasing the arbitrary decay order proves (1).

## 2. The original tests imply (W), and so does soft selection

For the original zero-one selectors, take a dual rectangle meeting at least one selected enlarged child. Choose one such child. Every other contributing smaller averaging cube lies inside its prescribed test tube:

- Transverse displacement in the actual Fourier direction is at most a fixed multiple of $$L^{2j+3}a$$.
- Longitudinal displacement is at most a fixed multiple of $$L^{2j+3}b$$.
- A direction change of size at most $$C_0a/b$$ adds at most a fixed multiple of $$C_0L^{2j+3}a$$ transversely.

The test dilation $$L^{4K+20}$$ exceeds all these factors. The smaller cubes lie in the same enlarged parent, and their overlap is at most the stated multiplicity. The selected test therefore implies (W). Exactly the same proof works for arbitrary coefficients of modulus at most one when the original test holds whenever the coefficient is nonzero.

A more useful variant does not require a hard selected test. Assume $$M>0$$ and set

$$
c_{Q,\theta}
=\min\left\{1,
\left(\frac{H(a/b)M}
{\sigma(T_{Q,\theta}\cap P^+)}\right)^{1/2}\right\}.
\tag{7}
$$

If the denominator is zero, define the coefficient to be one. It then has zero child weight anyway. These coefficients satisfy (W), even when their individual tubes are heavy.

To prove this, fix a dual rectangle and let its contributing index set be the children whose further enlargements meet it. Let

$$
A_U=\bigcup_{\{Q:\widetilde Q\cap U\ne\varnothing\}}Q^+,
\qquad m_U=\sigma(A_U).
$$

The same geometry applies with **any** contributing child as the chosen anchor. Hence every one of its test tubes contains the entire union above and

$$
\sigma(T_{Q,\theta}\cap P^+)\ge m_U.
$$

If the union has zero mass, (W) is immediate. Otherwise (7) gives

$$
\begin{aligned}
\sum_{\{Q:\widetilde Q\cap U\ne\varnothing\}}
w_Qc_{Q,\theta}^2
&\le
\min\{1,H(a/b)M/m_U\}
\sum_{\{Q:\widetilde Q\cap U\ne\varnothing\}}w_Q\\
&\le
\Lambda m_U\min\{1,H(a/b)M/m_U\}\\
&\le\Lambda H(a/b)M.
\end{aligned}
$$

This proves the claimed soft-selection version.

The coefficients in (7) equal one on every formerly good tube and lie between zero and one on heavy tubes. They therefore do not worsen the existing first-norm deletion estimates. Along a chain the inherited coefficient is their product, and

$$
0\le1-\prod_jc_j\le\sum_j(1-c_j).
$$

All fine descendants of a standard label must continue to use its effective coefficient, as they use its effective mark in the manuscript. With that convention the source-packet reconstruction and inherited identity have the same form, now with scalar weights. Future weighted functions remain independent of the current child and have the same Fourier support and bounded spectral densities.

Thus soft selection is a legitimate alternative decomposition with the **same proven cost**. The present argument supplies no better power of the threshold or improved dimension inequality. Such an improvement would require information stronger than the current tube-pair energy estimate.

## 3. Fine labels really have bounded ball overlap in the application

At a spatial level,

$$
a_j=2^{-n_j},\qquad \delta_j=\frac1{Ra_j}.
$$

For a circle radius in the fixed-ratio annulus, consecutive label centers in frequency are separated at scale

$$
r\delta_j\asymp_T1/a_j.
$$

Their tangential widths have that same scale. A ball of a fixed multiple of that radius therefore meets only boundedly many centers. At fine levels the label retains both its standard parent and its dyadic interval. Each interval meets only boundedly many standard supports, since standard support lengths and standard center spacing are comparable. This adds only a bounded multiplicity.

Fixed frequency smoothing does not alter this packing estimate: $$a_j\le1$$, so its fixed radius is at most a constant times $$1/a_j$$. Terminal refinement never passes below angular width $$1/R$$. Refining beyond that scale could create unbounded multiplicity after smoothing, but it does not occur in the printed construction.

The normal width is also the required one. Curvature contributes

$$
O_T(r\delta_j^2)=O_T\!\left(\frac1{Ra_j^2}\right).
$$

Admissibility gives $$a_{j+1}\le Ra_j^2$$, so this is at most a constant times $$1/a_{j+1}$$. Fixed smoothing is absorbed because $$a_{j+1}\le1$$. Thus the rectangle dual to the child-width, parent-length tube is valid even strictly below the standard angular scale.

The direction mismatch is controlled by

$$
\max\{\delta_j,R^{-1/2}\}\le a_j/a_{j+1}.
$$

The fine interval may differ from its effective standard direction by the standard width, but that width is within the permitted aspect ratio. No derivative bounds on hard angular indicators enter these support, packing, or weighted-kernel arguments.

## 4. A genuine false variant identifies the essential hypothesis

The transfer's identity has the form

$$
F_{Q,\alpha}=\sum_\theta c_{Q,\theta}F_{P,\theta}.
$$

The function for a fixed parent and angular label consists of terminal descendants surviving the marks at that parent and its spatial ancestors. It is independent of the current child. Only the current coefficient depends on that child, and it is constant on the child's averaging integral. Overlap of standard spectral supports leaves this algebra unchanged because their labels retain unique parents.

The constant-on-child requirement is essential. Take equal child and parent scales, one averaging square, a fixed nonzero band-limited envelope, and

$$
f_\theta(x)=e^{2\pi i\xi_\theta\cdot x}h(x)
$$

with widely separated frequency centers. Their containing balls can be disjoint and their common frequency rectangle orientation fixed. If one allowed coefficients varying with the averaging variable, then

$$
c_\theta(x)=e^{-2\pi i\xi_\theta\cdot x}
$$

would make their sum the number of labels times the envelope. Its squared average grows quadratically in that number, while the sum of their squared norms grows linearly. At equal child and parent scales the tube test with threshold one is automatic. Such a spatially varying-selector version is therefore false.

This counterexample is excluded by the printed proposition and by the exact inherited identity. It shows precisely why one cannot replace the parent function by an arbitrary child-dependent, spatially demodulated function.

## 5. Other direct stress tests and scope

If the pin measure is one atom and a selected child has positive weight, its test tube contains that atom. The original selected condition then forces

$$
H\ge b/a.
$$

It cannot be violated by insisting on a threshold of order one at high eccentricity. This threshold pays exactly the longitudinal scale appearing in the reproducing-kernel computation. Duplicating one frequency function under many labels likewise increases the containing-ball overlap bound; it is not a counterexample with fixed overlap constant.

The proof above covers arbitrary relative phases between fine labels and arbitrary changes of their constant selectors from child to child. It finds no missing angular-label count or additional scale ratio in the actual embedding. Its new weighted version permits the explicit soft coefficients (7), but it does not on its own improve the numerical distance theorem. The packet estimates, the limiting identification of the pinned measure, and the separate profile optimization remain distinct ingredients.
