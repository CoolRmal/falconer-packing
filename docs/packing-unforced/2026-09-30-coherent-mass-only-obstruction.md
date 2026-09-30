# Limits of mass-only refinements of the coherent comparison

Date: 2026-09-30. This is a negative calculation for specific numerical comparison bounds, not a lower bound on the actual distance-law error or a distance-set counterexample. The separate critical-covering Moran note gives the positive endpoint refinement obtained during this investigation.

## 1. Keeping masses and angular moments

Write τ=1+2γ and

$$
E_Q=r^{2\tau-1}I_\tau(\mu_Q),\qquad
D_Q=F_Q+F_{\operatorname{parent}(Q)},\qquad
\eta_q=\frac{q-1}{2q-1},\quad \beta_q=\frac1{2q-1}.
$$

The coherent proof, before Cauchy–Schwarz over source cells, gives the per-cell error bound

$$
C\min\{1,\sqrt{A_QE_Q}+D_QA_Q^{1-q}\}
$$

for independently chosen thresholds A_Q≥1. Choosing the optimal threshold when E_Q≤D_Q² and using the trivial bound otherwise gives

$$
\|f_{n+1}-f_n\|_1
\le C\sum_Qp_Q\min\{1,D_Q^{\beta_q}E_Q^{\eta_q}\}.
\tag{1}
$$

Since Σp_QD_Q≤4B and β_q+2η_q=1, Hölder gives

$$
\sum_Qp_Q D_Q^{\beta_q}E_Q^{\eta_q}
\le (4B)^{\beta_q}
\left(\sum_Qp_Q\sqrt{E_Q}\right)^{2\eta_q}.
\tag{2}
$$

Thus separate optimization of the angular cutoffs recovers the mass-sensitive criterion from research/mass_sensitive_coherent_fragment.tex. It can improve an individual nonuniform measure; it does not automatically improve its dimension-only consequence.

## 2. A sharper mass-dependent energy estimate has the same strict threshold

An s-Frostman probability gives

$$
\mu_Q(B(x,t))\le \min\{1,Ct^s/p_Q\}.
$$

Integrating this bound over all t yields, for 0<τ<s,

$$
I_\tau(\mu_Q)\le C_{s,\tau}p_Q^{-\tau/s}.
\tag{3}
$$

This improves the cruder radius-dependent conditional estimate at fixed τ when p_Q is much smaller than r^s. It implies

$$
T_n^2
:=r^{2\tau-1}\left(\sum_Qp_Q\sqrt{I_\tau(\mu_Q)}\right)^2
\le C r^{2\tau-1}
\left(\sum_Qp_Q^{1-\tau/(2s)}\right)^2.
\tag{4}
$$

If the occupied count is at most Cr^{-u}, concavity gives

$$
T_n^2\le C r^{2\tau-1-u\tau/s}.
\tag{5}
$$

For u≤2 and s>1, the exponent τ(2−u/s)−1 is increasing in τ. Its supremum over τ<s is exactly

$$
2s-1-u.
$$

Thus this sharper energy estimate, even together with the full mass sum, gives the same strict dimension-only threshold.

## 3. A pointwise obstruction independent of the replacement source masses

Let K have a fixed dyadic tree, and suppose every occupied depth-(n+1) cell has at most L_n occupied depth-2n descendants. For every probability η supported on K and every positive-η-mass depth-(n+1) cell Q, partition its conditional probability η_Q among those descendants. If their conditional masses are a_R, then

$$
\sum_Ra_R^2\ge L_n^{-1}.
$$

Pairs in one descendant are separated by at most √2·2^{-2n}. Consequently

$$
I_\tau(\eta_Q)\ge
2^{-\tau/2}\,2^{2n\tau}L_n^{-1}
\tag{6}
$$

for every τ∈(1,2), with infinite energy allowed. Since r=2^{-n},

$$
r^{2\tau-1}I_\tau(\eta_Q)
\ge 2^{-\tau/2}\frac{2^n}{L_n}.
\tag{7}
$$

This lower bound holds in every positive-mass coarse cell separately. In particular,

$$
T_n(\eta)^2\ge 2^{-\tau/2}\frac{2^n}{L_n},
\tag{8}
$$

independently of all source-cell masses.

For a spatially homogeneous dyadic tree with cumulative branching F,

$$
L_n=2^{F(2n)-F(n+1)},\qquad
T_n(\eta)^2
\ge c\,2^{n+F(n)-F(2n)}.
\tag{9}
$$

The homogeneous midpoint realizations in output/pdf/packing-unforced-hybrid-obstruction.tex have exact Hausdorff and packing dimensions d,D, and along infinitely many even endpoints N=2n satisfy

$$
F(n)=Dn+o(n),\qquad F(2n)=2dn+o(n).
$$

Thus (9) grows when D>2d−1. At D=2d−1, the separate catch-up construction in that fragment improves both errors to O(1), making (9) bounded below by a positive constant. These conclusions hold for every replacement probability η supported on the corresponding fixed set, not just the natural homogeneous measure or its cylinder restrictions.

The angular densities are probability densities relative to normalized arclength, so each F_Q≥1 and D_Q≥2. When the right side of (7) is bounded below, the numerical right-hand side in the fully retained per-cell bound (1) also stays bounded below. Cell masses, separate angular moment numbers, clipping at the trivial probability bound, and Rényi-entropy bookkeeping therefore cannot make these particular comparison certificates summable.

This statement does not bound the true first-norm difference from below. It leaves open better use of the actual angular-energy correlation, different spatial partitions or support diameters, and a genuinely stronger projection-comparison estimate.

## 4. Why the new endpoint covering class is consistent

The critical-covering examples constructed in research/2026-09-30-critical-covering-moran-examples.md have a deficit of order √n in their upper covering exponent. They do not satisfy the zero-deficit midpoint identities used in (9). The variable-exponent argument exploits precisely this additional quantitative information. It does not contradict the mass-only obstruction above, and it does not follow merely from the equality D=2d−1.
