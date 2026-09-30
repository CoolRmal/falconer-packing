# Exact audit of the high branch of the two-gap certificate

30 September 2026. This is an independent algebraic audit. It verifies the proposed nonnegative-weight certificate, its exact parameter domain, the matching optimization witnesses, and the resulting cutoff when combined with the previously proved low branch. The separate hard-gap representation and its applicability to arbitrary profiles are being checked independently; they are not consequences of a linear-programming calculation.

## 1. Constraints and exact coefficient verification

Set

$$
A=1+2a,\qquad B=1+2b,\qquad
b_{\mathrm c}(a)=\frac{1+2a}{4+2a}=\frac A{A+3}.
$$

The variables, in order, are

$$
(q_0,u_0,p_1,v_1,q_1,u_1,p_2,v_2).
$$

The eight inequalities are

$$
\begin{aligned}
u_0-bq_0&\le0,\\
u_0-v_1-p_1+q_0/2&\le-1/2,\\
ap_1-v_1&\le0,\\
u_1-v_2-p_2+q_1/2&\le-1/2,\\
ap_2-v_2&\le0,\\
u_1-v_1-q_1+p_1&\le0,\\
p_2&\le1,\\
v_1-u_1&\le0.
\end{aligned}
\tag{1}
$$

Their proposed weights, in this same order, are

$$
\begin{aligned}
\lambda_1&=\frac1B,&
\lambda_2&=\frac{2b}B,&
\lambda_3&=\frac{2b}{AB},&
\lambda_4&=\frac{4b(1+a)}{AB},\\
\lambda_5&=\frac{A-2b}{AB},&
\lambda_6&=\frac{2b(1+a)}{AB},&
\lambda_7&=\frac{(6+8a)b-A^2}{2AB},&
\lambda_8&=\frac{(4+2a)b-A}{AB}.
\end{aligned}
\tag{2}
$$

Direct calculation gives the following complete coefficient table for the weighted left side:

| Variable | Weighted coefficient | Simplified value |
|---|---|---|
| $$q_0$$ | $$-b\lambda_1+\lambda_2/2$$ | $$0$$ |
| $$u_0$$ | $$\lambda_1+\lambda_2$$ | $$1$$ |
| $$p_1$$ | $$-\lambda_2+a\lambda_3+\lambda_6$$ | $$0$$ |
| $$v_1$$ | $$-\lambda_2-\lambda_3-\lambda_6+\lambda_8$$ | $$-1$$ |
| $$q_1$$ | $$\lambda_4/2-\lambda_6$$ | $$0$$ |
| $$u_1$$ | $$\lambda_4+\lambda_6-\lambda_8$$ | $$1$$ |
| $$p_2$$ | $$-\lambda_4+a\lambda_5+\lambda_7$$ | $$-1/2$$ |
| $$v_2$$ | $$-\lambda_4-\lambda_5$$ | $$-1$$ |

The weighted right side is

$$
-\frac{\lambda_2}2-\frac{\lambda_4}2+\lambda_7
=-\frac A{2B}.
\tag{3}
$$

Thus, whenever all weights are nonnegative, (1) proves

$$
u_0-v_1+u_1-v_2+\frac{1-p_2}{2}
\le\frac12-\frac A{2B}
=\frac{b-a}{1+2b}
=:C_1(a,b).
\tag{4}
$$

All eight coefficient identities and (3) were also checked as exact bivariate rational-polynomial identities after clearing the common positive denominator, using Python's integer and rational arithmetic. No numerical linear-programming tolerance enters the certificate.

## 2. Exact nonnegativity domain

Assume

$$
0<a<\frac12,\qquad b_{\mathrm c}(a)\le b\le\frac12.
\tag{5}
$$

The first, second, third, fourth, and sixth weights are positive. The fifth is positive because

$$
A-2b\ge A-1=2a>0.
$$

The last weight is nonnegative if and only if

$$
b\ge b_{\mathrm c}(a).
$$

The seventh is nonnegative if and only if

$$
b\ge\frac{A^2}{4A+2}.
$$

The last threshold is weaker than the one for the eighth weight, since

$$
\frac A{A+3}-\frac{A^2}{4A+2}
=\frac{A(2-A)(A+1)}{(A+3)(4A+2)}>0
\qquad(1<A<2).
\tag{6}
$$

Therefore every multiplier in (2) is nonnegative on (5), and the lower endpoint of that domain is exact for this multiplier vector. At the lower endpoint only the eighth multiplier vanishes; the seventh remains positive.

For use as a profile statement, one must additionally retain the standard hypothesis

$$
a\le b.
$$

It does not follow from (5) for all values below one half: indeed

$$
b_{\mathrm c}(a)-a
=\frac{1-2a-2a^2}{4+2a}
$$

changes sign at $$(\sqrt3-1)/2$$. In the physical range $$0<a\le1/4$$, this issue never occurs because $$b_{\mathrm c}(a)>a$$. The algebraic certificate itself remains valid on (5); the additional condition is needed to speak about profiles between the ordered barriers.

## 3. Matching witnesses and what “sharp” means here

The upper estimate (4) is sharp even for the finite relaxation (1). For any $$0<a\le b$$, let

$$
q=\frac AB,
\qquad
(q_0,u_0,p_1,v_1,q_1,u_1,p_2,v_2)
=(q,bq,1,a,1,a,1,a).
\tag{7}
$$

All eight constraints are equalities and the objective is $$bq-a=C_1(a,b)$$. The second gap is degenerate. For the genuine profile problem, the single-collapse profile

$$
g(x)=\min\{bx,\,1+a-x\}
\tag{8}
$$

has hard set $$[0,q]\cup\{1\}$$ and limiting cost $$bq-a=C_1(a,b)$$. Its two affine pieces both majorize the lower barrier, and the corner lies after $$q$$. Thus the dual bound matches the known profile lower bound when the hard-gap formula is used.

There is also a concrete obstruction to extending the same value below the transition. For

$$
0<a<b<b_{\mathrm c}(a),
$$

put

$$
q=\frac AB,\qquad
t=\frac{(1-b)q}{1-a},\qquad
r=\frac{2(1+a)t-1}{B}.
$$

The assignment

$$
(q_0,u_0,p_1,v_1,q_1,u_1,p_2,v_2)
=(r,br,t,at,q,bq,1,a)
\tag{9}
$$

satisfies all eight inequalities. The first seven are equalities, and the last one follows from

$$
bq-at=\frac{(b-a)q}{1-a}>0.
$$

Its objective is

$$
C_2(a,b)
=\frac{(b-a)(2+a-2b-4ab)}{(1-a)(1+2b)^2}.
$$

The exact difference is

$$
C_2-C_1
=\frac{(b-a)[1+2a-(4+2a)b]}{(1-a)(1+2b)^2}>0.
\tag{10}
$$

The first drop in (9) is precisely this positive difference; the second drop is $$C_1$$. These data arise from the two-collapse profile already analyzed in `research/2026-09-30-unforced-multiple-collapse.md`. Thus the obstruction below the transition is not merely a negative multiplier: the relaxation and the actual profile have a matching value strictly larger than $$C_1$$.

This establishes sharpness of the profile calculation on the audited domains, once combined with the separate geometric reduction. It does **not** establish a necessary dimension condition for distance positivity.

## 4. Cutoff of the high branch

For $$0<a<1/2$$,

$$
C_1(a,b)<a
\quad\Longleftrightarrow\quad
b<\frac{2a}{1-2a}.
\tag{11}
$$

The cutoff on the right belongs to the high-branch region exactly when

$$
\frac{2a}{1-2a}\ge b_{\mathrm c}(a)
\quad\Longleftrightarrow\quad
8a^2+8a-1\ge0
\quad\Longleftrightarrow\quad
a\ge\beta:=\frac{\sqrt6-2}{4}.
\tag{12}
$$

At the transition,

$$
b_{\mathrm c}(\beta)
=\frac{2\beta}{1-2\beta}
=\frac{\sqrt6-1}{5},
\qquad
1+b_{\mathrm c}(\beta)=\frac{4+\sqrt6}{5}.
$$

Consequently, with $$a=d-1$$ and $$b=D-1$$, the high-branch strict sufficient cutoff is

$$
D<\frac1{3-2d}
$$

as soon as $$d\ge1+\beta$$, using the low branch below its transition and the already established high-slope estimate above $$b=1/2$$. The strict inequality must be preserved. In particular, at $$d=5/4$$ this argument gives $$D<2$$; it does not include $$D=2$$ at equality. The separate theorem for $$d>5/4$$ is a different input.

## 5. The join with the certified low branch

The previously proved low branch assumes

$$
R(a,b)=4(1+a)b^2-4(a+2)b+1+3a\le0,
\qquad b\le b_{\mathrm c}(a).
$$

Its derivative with respect to the upper slope is

$$
\partial_b C_2
=\frac{2+11a+8a^2-(8+14a+8a^2)b}
{(1-a)(1+2b)^3}.
$$

For $$0<a<1$$ and $$b\le b_{\mathrm c}(a)$$, the numerator is strictly positive: at its largest allowed argument it equals

$$
\frac{18a(1+a)}{4+2a}>0.
$$

Thus $$C_2$$ is strictly increasing on the low-branch domain. Formula (10) proves that $$C_2=C_1$$ at the transition. There is no jump in the cost or in the resulting strict cutoff.

For completeness, put

$$
\alpha=\frac{3-\sqrt7}{4}.
$$

Throughout the joining range $$\alpha\le a\le\beta$$, all parameters $$2a\le b\le b_{\mathrm c}(a)$$ meet the extra certificate condition. Indeed,

$$
R(a,2a)=16a^3+8a^2-13a+1,
$$

which is negative at $$\alpha$$ and strictly decreasing on this short interval; its derivative is $$48a^2+16a-13<0$$. Also

$$
\partial_bR=8(1+a)b-4(a+2)\le-4
\qquad(b\le1/2).
$$

At the other endpoint of the low-branch interval one can check directly that

$$
R(a,b_{\mathrm c}(a))
=\frac{3(1+a)^2(a-1)}{(a+2)^2}<0.
$$

After clearing its positive denominator, the equation $$C_2=a$$ is

$$
-(2+8a-4a^2)b^2+(2-a+8a^2)b-3a=0.
$$

Its unique root in $$[2a,b_{\mathrm c}(a)]$$ for $$\alpha\le a\le\beta$$ is

$$
b_2(a)=
\frac{2-a+8a^2-
\sqrt{64a^4+32a^3-63a^2-28a+4}}
{4+16a-8a^2}.
\tag{13}
$$

Existence and uniqueness follow from the strict monotonicity just proved and the endpoint signs; thus the radical is real on the stated interval. At the left endpoint $$b_2(\alpha)=2\alpha$$; at the right endpoint $$b_2(\beta)=b_{\mathrm c}(\beta)$$. In the interior the strict inequalities hold. As an exact check,

$$
b_2(1/10)=\frac5{23},\qquad
1+b_2(1/10)=\frac{28}{23}.
$$

Combining this audit with the certified geometric low branch and the older line criterion gives the continuous sufficient cutoff

$$
\mathcal B(d)=
\begin{cases}
2d-1,&0<d-1\le\alpha,\\
1+b_2(d-1),&\alpha<d-1<\beta,\\
(3-2d)^{-1},&\beta\le d-1\le1/4.
\end{cases}
$$

This last inference is explicitly conditional on the separate hard-gap geometry and analytic transfer. Every algebraic sign, join, and strict cutoff used in that inference is verified above.

## 6. Audit of the assembled dimension fragment

I subsequently read `output/pdf/packing-unforced-hard-dimension.tex` line by line, together with the actual statement in `packing-unforced-proof.tex` and the lower-witness statements in `packing-unforced-hard-gaps.tex`. The following records the additional checks, using line numbers from that reading.

### Guards on the entire physical range

Lines 12–23 correctly prove the guard in the low-root range. The identity

$$
R(\alpha,2\alpha)=3(11\alpha-1)<0
$$

agrees with the radical form in the earlier note. The derivative in the lower slope of $$R(a,2a)$$ is strictly negative throughout $$[\alpha,1/6]$$, not only until the first joining point. Thus the same argument legitimately applies in lines 65–73: if $$a_c\le a\le1/4$$ and the otherwise potentially missing interval $$2a\le b\le b_c(a)$$ is nonempty, then

$$
4a^2+6a-1\le0,
\qquad
a\le\frac{\sqrt{13}-3}{4}<\frac16.
$$

This places it exactly inside that larger guard range. Monotonicity in the upper slope then gives the stated strict cost bound, with equality only at the actual second join. No uncovered lower-slope interval occurs as the Hausdorff slope increases from the join to one quarter.

### Radical, smaller root, and joins

Lines 25–63 are consistent with the cleared quadratic in Section 5 of this note. The derivative of the rational cost is strictly positive at both endpoint roots as well as in the interior. At a root, multiplication by the positive denominator preserves the derivative sign. A double root of the cleared quadratic would have zero derivative, so the discriminant is strictly positive on the full closed parameter interval. The quadratic is concave downward; its root having positive derivative is the smaller root. This verifies both the radical sign and the chosen square-root branch without assuming them from a numerical plot.

### Exponent slack and the Borel reduction

Lines 79–98 use only points strictly below the curve. Outside the coherent region, they have $$b\ge2a$$, $$a>\alpha$$, and a strict cost margin. A small decrease in $$a=d-1$$ and increase in $$b=D-1$$ preserves $$b> a$$ and the cost margin.

If the original point is at the cost-formula transition, this perturbation moves into the high branch: $$b_c$$ increases with $$a$$, so decreasing $$a$$ decreases its transition while increasing $$b$$ raises the upper slope. Continuity across the join therefore suffices. At the standard-slope boundary, the same reasoning moves into the already proved high-slope branch. Within the low branch its guard is strict, so it also survives a sufficiently small perturbation.

For all theorem parameters $$D<B_{\rm H}(d)$$ and $$d\le5/4$$, one has $$D<2$$. Hence an upper exponent $$u>D$$ with $$u<2$$ is available even at $$d=5/4$$. Likewise a lower exponent $$1<s<d$$, with $$s<5/4$$, is available. A further exponent strictly between $$s$$ and $$d$$ supplies the Frostman measures used by the existing Borel reduction. Thus the proof is not relying on either an endpoint energy or an upper-box estimate at exactly the packing dimension.

The conclusion about the family of pins is relative to the selected Frostman pin probability. It does not mean positive planar Lebesgue measure of the pins. The unqualified phrase “positive-measure family of pins” in lines 95–96 was flagged for clarification to avoid that unintended reading.

### Exact iff for the stated method, on all physical parameters

For $$0<a\le1/4$$ and $$a\le b\le1$$, the predicate

$$
b<2a\quad\text{or}\quad\mathcal M(a,b)<a
$$

has exactly the threshold claimed in lines 100–140, subject to the profile results assembled just before it. All converse cases check:

- When $$0<a\le\alpha$$, the two-collapse witness under upper slope $$2a$$ is admissible, since $$2a<b_c(a)$$ on this interval. Its cost is at least $$a$$ by the exact baseline sign. The same profile remains admissible for every larger upper slope. This proves the obstruction on the entire half-strip $$b\ge2a$$, including equality at $$a=\alpha$$.
- When $$\alpha<a<a_c$$, the two-collapse witness and strict upper-slope monotonicity give cost at least $$a$$ between the root and the transition. Above the transition, the single-collapse witness already has cost greater than $$a$$ because its own cutoff lies below that transition.
- When $$a\ge a_c$$, the single-collapse witness has cost at least $$a$$ precisely when $$b\ge b_F(a)$$. At $$a=1/4$$, the endpoint $$b=1$$ gives equality. Therefore the strict inequality at the physical corner is correctly excluded.

The sufficient direction follows from the coherent criterion or the explicit universal cost bound, respectively. Compression supplies a profile-independent edge-count bound at each fixed start, so this use is consistent with the definition of the limiting universal cost. The statement makes no interchange between a supremum and an unsupported limit.

The assembled scope paragraph correctly identifies this as optimality of the specified disjunction of two tests. No planar counterexample, necessary distance-set condition, or optimal Falconer threshold follows from those extremizing profiles. The comparison with the preceding curve is also valid: wherever its universal cost is strictly below the lower slope, so is the minimax cost, and its coherent and high-slope branches are included already.

### Assembly issues reported to the parent

Three small textual/assembly issues were found and reported; none changes the verified algebra.

1. In `packing-unforced-proof.tex` line 84, the initial assembled root formula contained literal `sqrt{...}` rather than the TeX command `\sqrt{...}`. The latter is required to print the stated radical.
2. The label `hardgap:section` appeared both on the main section and on the fragment's opening subsection. One label should be renamed or removed.
3. The single-collapse witness in `packing-unforced-hard-gaps.tex` was initially stated only for upper slopes at most one half, while the dimension fragment's converse applies it up to one. Its proof is unchanged for every $$0<a<b\le1$$: the profile has slopes $$b$$ and $$-1$$, still obeys both barriers, and still has hard set

$$
\left[0,\frac{1+2a}{1+2b}\right]\cup\{1\}.
$$

Extending that witness's stated domain to one closes the textual domain gap in the all-physical-parameters iff. This extension needs no new analytic or profile estimate. The separate ambiguous pin-measure wording is discussed above.

No other algebraic gap, lost parameter interval, strictness failure, or unsupported distance-optimality claim was found in the assembled dimension argument. This audit does not replace the separate review of the hard-component identity and its finite-chain reduction.
