# Independent audit of the sharp gap certificates

30 September 2026. I reviewed `research/2026-09-30-sharp-two-gap-bound.md`, Sections 1–7, and the matching constructions in `research/2026-09-30-unforced-multiple-collapse.md`. I also rechecked the source statement of [Keleti–Shmerkin, Lemma 5.4](https://arxiv.org/html/1801.08745), including its endpoint orientation after reversal.

**Verdict:** no substantive mathematical defect found in either upper certificate, its stated parameter domain, or the matching profile constructions. The one literal wording correction reported to the author is to specify $0\le n_0<1$, rather than merely $n_0<1$, so the starting point lies in the profile domain. This is a written-proof audit, not Lean certification or a claim of optimality for the distance problem.

## Hard components and positive gaps

For a finite piecewise affine profile, the original-coordinate hard set is a finite union of closed intervals, including the endpoints. The published hard-point identity, after reversing the coordinate, has precisely the correction $-a$. Omitting that correction would invalidate the argument; it is retained correctly.

The gap lemma is valid. If a point inside a complementary gap had value below the right endpoint, a minimum between that point and the right endpoint would itself be hard. Its future window before the endpoint is controlled by its minimum property; the remainder is controlled by hardness of the endpoint. This contradicts its location in the gap. Thus every gap has nonnegative endpoint drop, and telescoping gives the limiting optimal cost as the sum of those drops.

For a positive gap $(q,p)$ with drop $\delta$, hardness at $q$ forces $p>(1+q)/2$. The Lipschitz inequality then gives

$$
\delta\le p-\frac{1+q}{2}.
$$

This proves the half-length tail bound. Summing negative variation on the disjoint gaps proves the independent endpoint-sensitive variation bound. The convex combination with weights $1-2\chi$ and $2\chi$ is legitimate exactly when $0\le\chi\le1/2$. The certificate's hypothesis $R(a,b)\le0$ supplies that condition, and its numerator is strictly positive on the stated domain.

## The two-gap certificate

Every one of the seven inequalities used in the certificate follows from a barrier, the positive-gap estimate, endpoint order, or the Lipschitz inequality between the first two retained positive gaps. Omitting zero-drop gaps does not affect those inequalities.

I independently expanded the weighted left side in all eight variables $q_1,p_1,u_1,v_1,q_2,p_2,u_2,v_2$. Its coefficients are exactly those of

$$
\delta_1+\delta_2-\frac{p_2}{2}+\chi v_2.
$$

All seven cancellation identities hold as rational identities in $a,b$. Every weight is nonnegative under the two explicitly stated domain conditions. The weighted right side is exactly $-b/(1+2b)-\chi/2$. Adding the blended tail produces the asserted $C_2(a,b)$ with no omitted endpoint term.

The separate treatment of zero or one positive gap is necessary and correct. Its single-gap bound is at most $C_2$ on the low-side domain. Thus the proof covers an arbitrary finite number of gaps, not merely profiles with two collapses.

## The high-side certificate

The additional inequality $v_1\le u_2$ is valid: passing between the first two positive gaps, hard components have nonnegative endpoint increases and all intervening gaps have zero endpoint drop. It asserts only a net endpoint increase, not pointwise monotonicity across that entire interval.

The eight-inequality certificate was expanded independently. Its weighted left side is exactly $\delta_1+\delta_2-p_2/2$. Its right side, after adding the half-length tail, is exactly $(b-a)/(1+2b)$. All weight signs hold when

$$
0<a<b\le\frac12,\qquad b\ge\frac{1+2a}{4+2a}.
$$

In particular, the penultimate numerator at the transition is

$$
\frac{(1+a)(1-2a)(1+2a)}{a+2}>0,
$$

and the final weight has exactly the stated transition sign. No $R(a,b)$ condition is needed on this branch.

## Matching lower profiles and exact constants

The single-collapse profile has the claimed initial hard component and limiting cost. For the two-collapse profile, I checked the ordering of its affine pieces, the window comparison on the initial component, the absence of hard points in the first gap, and the comparison with the final descent on the second component. These give the two stated nondegenerate hard intervals. At the transition, the first drop becomes zero, consistently with the agreement of the two formulas.

Exact symbolic checks reproduce the stated costs and margins at

$$
(a,b)=(1/10,1/5),\quad(1/10,21/100),\quad(9/100,181/1000),
$$

including $C_2(1/10,1/5)=9/98$ and margin $2/245$. Both substitutions at $\alpha=(3-\sqrt7)/4$ are correct, as is the factorization of $C_2(a,2a)-a$.

## Finite starts, limiting profiles, and the transfer interface

Truncation of a crossing edge preserves admissibility and decreases cost, proving the monotonicity of finite-start infima. Maximal admissible bridges cost at most their total length, giving the stated error of at most the distance to the endpoint. Thus the hard-point limiting bound controls every finite start.

General edge compression is valid, with cost difference $g(m)-\max(A,B)\ge0$ for the two interval minima $A,B$. It supplies an edge bound independent of the number of affine pieces. Compactness of endpoint lists then gives actual minimizing chains and passes the bound to continuous Lipschitz profiles. The grid-rounding and barrier-clamping errors are the same per-edge estimates already used in the analytic transfer argument.

Accordingly these certificates supply precisely the bounded-chain and stability properties needed by that transfer. This audit does not re-prove the separate Fourier/deletion theorem. Sharpness here is sharpness of the universal profile cost on the certified domains, not a necessary Hausdorff–packing condition for pinned distance positivity.

## Audit of the assembled manuscript fragment

I then reviewed the actual source `output/pdf/packing-unforced-hard-gaps.tex` line by line, after the statement label was changed to `hardgap:statement` and the final single-collapse witness was extended to $0<a<b\le1$. The assembled source passes the mathematical audit. No substantive transcription error or missing hypothesis was found.

The explicit reversal is correct:

$$
\Phi_\zeta(g)=T_\zeta(f)-g(1-\zeta),\qquad
T(f)-\zeta\le T_\zeta(f)\le T(f)+2\zeta.
$$

The finite partitions correspond bijectively to the original chains, the endpoint correction telescopes with the stated sign, and the two comparison errors follow from halving and truncation of the interval crossing $\zeta$. This also covers the empty chain at $n_0=0$. The subsequent monotonicity and bridging argument independently gives the sharper finite-start error used in the manuscript. Compactness applies only after the uniform chain compression, so it does not presume a bound on the number of affine pieces.

For the expanded lower-bound proof, exact symbolic recomputation confirms the identities for $r-L$, $(1+r)/2-L$, $br-at$, $(1+q)/2-P$, and the final cost. The parameter restriction implies $q_0\le t<q<P<1$ and $0<r<L<t$. Thus every claimed affine interval is correctly ordered. The future endpoint at $r$ is already on the first descent; on $(r,L)$ it either remains on that descent or reaches the valley, in both cases witnessing failure of hardness. On $[L,t)$ the immediate decrease suffices. The second hard interval uses only the initial rise and the final descent, with the displayed comparison $3(q-x)/2$. The future endpoint at $q$ is strictly beyond $P$, which validates its use to exclude all of $(q,P]$.

At the boundary $t=q_0$, $br=at$ and the first gap has zero endpoint drop; the same hard-set argument remains valid and the two cost formulas agree. The isolated endpoint one contributes zero. The final single-collapse calculation stays valid for every $0<a<b\le1$, as required for the wider model obstruction.

Both weighted certificates in the TeX source have the same ordering, coefficients, and right sides as the independently verified research note. The continuous-profile approximation preserves the endpoint normalization, both barriers, and the Lipschitz constant; interval minima converge with the endpoint lists. Grid rounding and barrier clamping have the stated per-edge errors. Thus the fragment supplies an actual finite admissible chain, with uniform length and stability, rather than only a limiting total-drop inequality.
