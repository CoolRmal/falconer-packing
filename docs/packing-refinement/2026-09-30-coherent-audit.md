# Independent audit and a stronger coherent convergence estimate

30 September 2026. This note audits `output/pdf/packing-bound-original-branch.tex` and derives a quantitative strengthening. It does not assume the conclusions of earlier audit notes. It verifies the analytic calculation on its stated hypotheses; it is not an external referee report or a claim of global optimality.

## Conclusion

I find no mathematical gap in the coherent angular/affine comparison proving the strict source condition

$$
\dim_P E<2\dim_H E-1,\qquad \dim_H E>1,\qquad \dim_H F>1.
$$

The proof's convergence criterion can be weakened: if the radial-projection input supplies an exponent

$$
1<q\le 2,
$$

then the sufficient energy-summability exponent can be increased from

$$
\frac{q-1}{2q-1}\quad\hbox{to}\quad\frac{q-1}{q}.
$$

This is an actual stronger convergence theorem, proved below. It gives improved logarithmic endpoint criteria. It does **not** improve the universal condition stated solely in terms of Hausdorff and packing dimensions. No argument in this note establishes that the dimensional condition is globally optimal.

## 1. The angular calculation

Let a probability measure lambda be supported in a disk of radius comparable to r, and put

$$
a=1+2\gamma,\qquad 0<\gamma<\tfrac12,\qquad I_a(\lambda)<\infty.
$$

Writing the scalar Fourier transform of its projected density as

$$
f_\tau(\theta)=\widehat\lambda(\tau\theta),
$$

angular differentiation produces a linear combination of

$$
\tau\widehat{x_k\lambda}(\tau\theta),\qquad k=1,2.
$$

The signed Riesz identity is valid here because the absolute spatial energy of the coordinate-weighted measure is finite. In particular,

$$
\int_{\mathbb R^2}|\widehat{x_k\lambda}(\xi)|^2|\xi|^{a-2}\,d\xi
\le C r^2 I_a(\lambda).
$$

For scalar frequencies with magnitude at least the reciprocal of r, define

$$
A_\tau=|\tau|^{2\gamma}\|f_\tau\|_2^2,
\qquad
B_\tau=|\tau|^{-2+2\gamma}\|f_\tau\|_{H^1}^2.
$$

The polar-coordinate Jacobian gives

$$
\int A_\tau\,d\tau\le C I_a(\lambda),
\qquad
\int B_\tau\,d\tau\le C r^2 I_a(\lambda).
$$

In the differentiated part of the second integral, the derivative's two powers of frequency restore the exact Riesz weight. In the undifferentiated part, the inverse square of the frequency is at most the square of r. The weights in angular interpolation cancel exactly:

$$
A_\tau^{1-\gamma}B_\tau^\gamma
=\|f_\tau\|_2^{2(1-\gamma)}\|f_\tau\|_{H^1}^{2\gamma}.
$$

Integration and Hölder therefore give

$$
\|F\|_{H^\gamma(S^1;L^2(\mathbb R))}^2
\le C r^{2\gamma}I_a(\lambda).
$$

The low frequencies cost at most a constant divided by r. The diameter bound implies that the energy on the right is at least a constant times the reciprocal of r after multiplication by the displayed power, so it absorbs this contribution.

For a Hilbert-valued measurable representative define

$$
G(\theta)^2=
\int_{S^1}\frac{\|F(\theta)-F(z)\|_2^2}
{d(\theta,z)^{1+2\gamma}}\,dz.
$$

The integral of this quantity is bounded by the fractional Sobolev seminorm. For any two angles where it is finite and the projected density is valid, average the triangle inequality over their connecting arc of length delta. The estimate

$$
\|F(\theta)-F(\phi)\|_2
\le C\delta^\gamma\bigl(G(\theta)+G(\phi)\bigr)
$$

then holds for **every** such pair. This removes a single angular null set and is sufficient for correlated angles. It does not assert continuity of the projected densities.

Finally define

$$
S(\theta)=\sup_{|v|\le Cr^2}
\|F(\theta)(\cdot-v)-F(\theta)\|_2.
$$

Strong continuity of translation permits taking this supremum over rational v, so it is measurable. Plancherel and moving the supremum inside a nonnegative Fourier integral give

$$
\int S(\theta)^2\,d\theta
\le C r^{4\gamma} I_a(\lambda).
$$

These estimates hold for arbitrary finite-energy probabilities, including singular ones. They use neither angular independence nor independence of angle and radial displacement.

## 2. Affine geometry and positivity

Take compactly supported source and pin probabilities with separated supports. At every dyadic node choose a source center with finite radial-projection moment. For a parent P of side r and child Q, use the same source conditional probability on Q for both affine maps. Recenter at the child center b and write the parent and child angular directions as theta and phi. Then

$$
d(\theta,\phi)\le Cr,
$$

and after subtracting the common translation equal to the distance from b to the pin, the remaining scalar shift is

$$
v=|b-y|(\theta\cdot\phi-1),\qquad |v|\le Cr^2.
$$

Both projected densities have mass one. Their supports, after this recentering and the small translation, lie in an interval of length at most a constant times r. Thus an angular second-norm bound converts to a first-norm bound with factor proportional to the square root of r. The first-norm difference is also bounded by two, independently of all energies.

The affine pushforwards are positive probability measures with jointly measurable densities. Their maps approximate distance uniformly with an error of order the square of the source scale. Consequently convergence of their densities in first norm identifies the limit with the actual positive joint pinned-distance law. This identification does not require an inference from a signed wave-packet approximation.

## 3. A stronger energy-summability theorem

Let mu and nu be separated compact probabilities satisfying Frostman bounds with exponents greater than one. The radial input provides densities and a finite moment

$$
(\Theta_x)_*\nu=\rho_x\,d\sigma,
\qquad
B=\int \|\rho_x\|_q^q\,d\mu(x)<\infty.
$$

We may reduce the supplied exponent if necessary and assume it is at most two. Normalize circle measure to mass one. Choose node centers as in the manuscript, so, writing the node moment as M,

$$
\sum_{Q\text{ at level }n}p_Q M_Q\le 2B.
$$

Fix gamma as in Section 1 and assume the node energies are finite. For one child Q, the pointwise first-norm error is bounded by

$$
\min\bigl(2,H_Q(\theta)+H_Q(\phi)\bigr),
$$

where a nonnegative measurable function can be chosen as

$$
H_Q(\omega)=C r^{1/2+\gamma}G_Q(\omega)
+C r^{1/2}S_Q(\omega).
$$

The constants absorb the uniformly bounded angular displacement factor. The preceding estimates imply

$$
\int H_Q^2\,d\sigma\le C z_Q,
\qquad z_Q=r^{1+4\gamma}I_{1+2\gamma}(\mu_Q).
$$

Use the elementary inequality

$$
\min(2,h+k)\le\min(2,h)+\min(2,k),\qquad h,k\ge0.
$$

Let the conjugate exponent be q-prime. Since it is at least two,

$$
\int \min(2,H_Q)^{q'}\,d\sigma
\le 2^{q'-2}\int H_Q^2\,d\sigma.
$$

Apply Hölder separately to each angular marginal. The expected first-norm error for this child is at most

$$
C_q\bigl(M_P^{1/q}+M_Q^{1/q}\bigr)z_Q^{\beta},
\qquad \beta=\frac{q-1}{q}.
$$

No exceptional pins were discarded. Sum over children with their original masses. A second application of Hölder gives

$$
\begin{aligned}
\sum_Q p_Q M_Q^{1/q}z_Q^\beta
&\le \left(\sum_Qp_QM_Q\right)^{1/q}
\left(\sum_Qp_Qz_Q\right)^\beta,\\
\sum_Q p_Q M_P^{1/q}z_Q^\beta
&\le \left(\sum_Qp_QM_P\right)^{1/q}
\left(\sum_Qp_Qz_Q\right)^\beta.
\end{aligned}
$$

The second moment sum is exactly the weighted parent sum because child masses add to their parent's mass. Hence the positive affine joint densities satisfy

$$
\boxed{
\|f_{n+1}-f_n\|_{L^1(\nu\times dt)}
\le C_q B^{1/q}Z_n^{\beta},
\qquad
Z_n=2^{-n(1+4\gamma)}
\sum_{Q\text{ at level }n+1}p_QI_{1+2\gamma}(\mu_Q).
}
$$

Therefore the strictly weaker sufficient criterion

$$
\boxed{\sum_n Z_n^{(q-1)/q}<\infty}
$$

implies absolute continuity of the actual pinned source law for almost every pin. The proof is telescoping first-norm convergence followed by the uniform affine-to-distance approximation and uniqueness of disintegration. The old exponent is smaller, so its summability implies this one after omitting finitely many scales.

An even more informative sufficient criterion retains the individual child terms:

$$
\sum_n\sum_{Q\text{ at level }n+1}
p_Q\bigl(M_{\operatorname{parent}(Q)}^{1/q}+M_Q^{1/q}\bigr)
\left[2^{-n(1+4\gamma)}I_{1+2\gamma}(\mu_Q)\right]^{(q-1)/q}<\infty.
$$

This is measure dependent and is not a new theorem about the two dimensions alone.

## 4. A logarithmic endpoint consequence

Suppose for some s strictly between one and two the source obeys the stronger growth estimate

$$
\mu(B(x,r))\le C r^s[\log(e/r)]^{-b},\qquad 0<r<r_0,
$$

and its occupied dyadic-square count obeys

$$
N(r)\le C r^{-(2s-1)}[\log(e/r)]^k.
$$

Here b is greater than one, and k is any real number for which the count bound holds. For a nonvacuous new dimensional endpoint one can restrict s to at most three halves. Assume the pin measure has Frostman exponent greater than one, and let q in the preceding range be any available radial-projection exponent.

At the critical energy parameter the logarithmic growth gives finite energy. Layer-cake integration within a source square yields

$$
p_Q I_s(\mu_Q)
\le C[\log(e/r)]^{1-b}.
$$

Indeed the small-radius integral is bounded by a constant times

$$
\int_0^{Cr}\frac{dt}{t[\log(e/t)]^b},
$$

and the boundary term is smaller. Set gamma equal to half of s minus one. The angular lemma is applicable at this value because the critical energy is now finite. Consequently

$$
Z_n\le C n^{k+1-b}.
$$

The strengthened theorem proves raw pinned absolute continuity provided

$$
\boxed{b>1+k+\frac{q}{q-1}.}
$$

This improves the logarithmic exponent demanded by the earlier truncation argument by exactly one. It is a rigorous endpoint statement under extra quantitative hypotheses. Equalities of Hausdorff and packing dimensions alone do not imply these hypotheses.

## 5. Why this has not improved the dimension-only line

For a source satisfying an ordinary s-Frostman bound and a covering count of order the negative u-th power of scale, the manuscript's local bound is

$$
I_a(\mu_Q)\le C r^{s-a}/p_Q,
\qquad 1<a<s.
$$

It yields

$$
Z_n\le C r^{s-u+a-1}.
$$

A sharper mass-sensitive energy estimate also follows from the global Frostman bound:

$$
I_a(\mu_Q)\le C p_Q^{-a/s}.
$$

To verify it, integrate the unnormalized ball bound

$$
\mu(Q\cap B(x,t))\le\min(p_Q,Ct^s)
$$

and split at a radius proportional to the s-th root of the node mass. Jensen then gives

$$
\sum_Qp_QI_a(\mu_Q)\le C N(r)^{a/s},
\qquad
Z_n\le C r^{2a-1-u a/s}.
$$

This exponent improves the finite-a numerical estimate when u exceeds s. Nevertheless its supremum as a approaches s is again

$$
2s-1-u.
$$

Thus both methods require the same strict dimension inequality when used with geometric summability. Improving the summability exponent cannot change the sign of this power. Taking source Frostman exponents up to its Hausdorff dimension and covering exponents down to its packing dimension recovers the stated strict line and no more.

This is a limitation of these estimates. It is not a proof that every argument based on coherent positive approximations must obey the line, and it is not a necessity theorem for positive pinned distance measure.

## Addendum: independent check of the new forced-chain bound

I also checked the new profile argument proposed in `2026-09-30-profile-optimization.md`. The bound is valid as a combinatorial statement. Its application to harmonic analysis is a separate obligation; this check does not verify that application.

Let the profile g be continuous, piecewise linear on a grid of mesh T, and one-Lipschitz, with

$$
g(0)=0,\qquad ax\le g(x)\le bx,\qquad 0<a\le b\le\tfrac12.
$$

Assume N and its half are grid points. Start at a grid point strictly below N and at least its half. The cost of an edge from n down to m is

$$
c_g(m,n)=g(m)-\min_{[m,n]}g,
$$

and its admissibility condition is

$$
2n-m\le N.
$$

There exists an admissible decreasing chain through the half-depth point and then zero whose total cost is at most

$$
\boxed{
N\left[\frac{(1+2b-4a)_+}{8}
+\frac{b-a}{2(1+a)}\right]+O(T).
}
$$

The number of edges is bounded by a constant times

$$
1+\log\frac{N}{N-n_0}.
$$

Here is the verification, including the stopping issue.

Set the half-depth point to l and the three-quarter-depth point to r. On the interval starting at l define

$$
H(x)=\tfrac12x+(b-\tfrac12)\tfrac N2.
$$

This is an upper envelope because

$$
H(x)-bx=(\tfrac12-b)(x-l)\ge0.
$$

On the interval starting at r put

$$
L(x)=H(2x-N)-g(x)
=x-\tfrac N2+(b-\tfrac12)\tfrac N2-g(x).
$$

It is nondecreasing since its derivative is one minus the derivative of g. Almost everywhere,

$$
(-g')_+\le\tfrac12(1-g').
$$

Consequently, for an interval lying wholly in the region where L is nonnegative,

$$
c_g(m,n)\le\int_m^n(-g')_+\,dx
\le\frac{L(n)-L(m)}2.
$$

Starting at the prescribed depth, make maximal admissible jumps, with the new depth equal to the larger of a stopping threshold and twice the old depth minus N. Stop either just above the last grid point where L is nonpositive, or at the first grid point at or above r if no such zero exists. The total cost is at most the positive part of L at the starting depth divided by two. A transition of one mesh interval adds at most T. The estimate at the top endpoint is

$$
\frac{L(N)_+}{2}
\le\frac{(1+2b-4a)_+N}{8}.
$$

If L stays positive down to the three-quarter-depth point, **stop the positive phase there**; it is not necessary for a zero of L to exist. On a grid, cross from the ceiling of that point to its floor if they differ, paying at most T. One may then jump to l. For sufficiently many grid intervals, this rounding edge is admissible; the finitely many remaining depths are absorbed by increasing the absolute constant in the mesh error.

If the construction has entered the region where L is nonpositive at a depth n greater than r, put

$$
m_0=2n-N>l.
$$

The envelope is valid at this point, and

$$
g(m_0)\le H(m_0)\le g(n).
$$

The leftmost grid minimum of g on the interval from this point to n therefore lies strictly before n. Jump to that minimum. The edge is admissible and has zero cost. If its endpoint is still above r, monotonicity of L ensures that the next edge starts in the same nonpositive region. Continue until the depth is at most r. The endpoint remains at least l.

The direct edge from this endpoint to l is admissible. To bound its cost, write the value of g at l as v. The Lipschitz and lower-barrier bounds imply, for every x at least l,

$$
g(x)\ge\max\{ax,v-(x-l)\}
\ge\frac{a(v+l)}{1+a}.
$$

Thus the terminal edge costs at most

$$
\frac{v-al}{1+a}\le\frac{(b-a)N}{2(1+a)}.
$$

The edge from l to zero is admissible and free because g is nonnegative.

The positive-phase edges double the complementary depth except at the last edge. For the zero phase, greedily merge consecutive edges whenever their union remains admissible. A union of zero-cost edges has zero cost: the leftmost endpoint remains a minimum of the entire union. Failure to merge two consecutive resulting edges means the complementary depth more than doubles over those two edges. These observations give the claimed logarithmic bound on their number.

For approximate barriers with uniform error eN, clip the profile at each grid point to the interval between the two linear barriers and reinterpolate. The clipped/interpolated profile is still one-Lipschitz and differs from the original by at most eN, provided the original is piecewise linear on the same grid. Each edge cost changes by at most twice this error. The preceding bound therefore acquires an additive

$$
2KeN+O(T).
$$

No additional approximation loss is needed merely from interpolation in this setting. If the starting profile is not already linear on the grid, the usual additional error proportional to KT is valid.

Finally, substitute

$$
a=s-1,\qquad b=u-1,\qquad 1<s\le u\le\tfrac32.
$$

Except for the degenerate corner at three halves, the positive-part argument is positive because it is at least three minus twice s. Comparing the new cost with s minus one gives precisely

$$
\boxed{u<\frac{s(12s-7)}{2s+4}.}
$$

This improves the previous forced-chain upper bound in the stated parameter range. It is a sufficient upper bound on profile-chain cost; it has not been proved to be the optimal such upper bound. Nor does this combinatorial calculation by itself prove a pinned-distance theorem without a complete verified transfer from chain cost to the Fourier estimate.
