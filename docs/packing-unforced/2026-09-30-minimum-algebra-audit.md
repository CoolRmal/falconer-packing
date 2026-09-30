# Independent algebra audit of the minimum refinement

30 September 2026. This audit checks the algebra and dimension inference in
`output/pdf/packing-unforced-minimum.tex`, the rational formulas in
`tmp/pdfs/publish_minimum_docs.py`, and the proof of the refined theorem in
`output/pdf/packing-unforced-proof.tex`. It is separate from the geometric
profile audit and from the analytic transfer audit. No claim of optimality,
external refereeing, or Lean verification follows from these checks.

## Rational formulas and positive denominators

Throughout,

$$
\frac18\le a\le\frac16,\qquad 2a\le b\le\frac12.
$$

The three expanded rational expressions for the affine-intersection values
agree exactly with the intersections defined in the appendix:

$$
\begin{aligned}
J_E&=\frac{(1-a)(b-a)(6b-1)}{24b^2-14ab+3a-4b},\\
J_F&=\frac{(b-a)(8b-a-2a^2-2ab)}
 {2(2b-a)(8b+3a-2ab)},\\
J_V&=\frac{(b-a)(12a^2b-4a^2-18ab^2-ab+a+4b)}
 {4(2b-a)(3a+2b-8ab)}.
\end{aligned}
$$

I checked these identities by expanding and clearing denominators using exact
rational polynomial arithmetic. The calculation checks coefficient equality,
not only sample values. The denominator signs can also be verified directly:
$$2b-a\ge3a>0,$$
$$8b+3a-2ab=8b+a(3-2b)>0,$$
$$3a+2b-8ab=3a+2b(1-4a)>0.$$
For the remaining denominator, since $$3-14b<0$$ and $$a\le b/2$$,

$$
24b^2-14ab+3a-4b
\ge b\left(17b-\frac52\right)>0.
$$

All four level polynomials printed in the appendix are exactly the numerator
of the corresponding rational function minus $$a$$, after multiplication by
its displayed positive denominator. In particular the level equation for
$$J_E=a$$ is

$$
(6-30a)b^2+(20a^2-a-1)b+a-4a^2=0.
$$

## Strict monotonicity and the unique root

The derivative of $$J_E$$ is exactly

$$
\partial_bJ_E=
\frac{a(1-a)(60b^2-12b+1-4a)}
 {(24b^2-14ab+3a-4b)^2}>0.
$$

The bracket is increasing in $$b\ge1/4$$. At $$b=2a$$ it is
$$240a^2-28a+1\ge5/4$$ on the stated range. The two positive factors in
$$E_2=(b-a)(1+6b-4a)/(6(2b-a))$$ are strictly increasing as well.

For $$J_F,J_V$$ the intersection argument is valid with the corrected
derivative appearing in the current appendix. If

$$
J=\frac{\sigma L_0+\lambda S}{\sigma+\lambda},
$$

where $$\sigma$$ and $$L_0$$ are independent of $$b$$, then

$$
J'=\frac{\sigma\lambda'(S-L_0)
             +\lambda(\sigma+\lambda)S'}{(\sigma+\lambda)^2}.
$$

Here $$\sigma>0$$, $$\lambda\ge0$$, $$\lambda'<0$$,
$$S<L_0$$, and $$S'>0$$. Thus the derivative is strictly positive,
including at $$b=1/2$$ where $$\lambda=0$$. An earlier displayed derivative
omitted the $$\lambda^2S'$$ term; the current file includes it, and the
correction strengthens the positivity argument.

Consequently

$$
V(a,b)=\max\{\min(E_2,J_E),\min(J_F,J_V)\}
$$

is continuous and strictly increasing in $$b$$. The finite minimum and maximum
operations preserve strict increase: between two distinct ordered arguments,
take the minimum of the four strictly positive increments.

The endpoint calculations in the appendix are correct. At $$b=2a$$,

$$
E_2=\frac{1+8a}{18}<a,\qquad
J_V-a=\frac{3(1-8a)(1-2a)}{4(7-16a)}\le0,
$$

with equality in the second inequality only when $$a=1/8$$. At that endpoint
$$J_F=19/148>1/8$$, so $$V(1/8,1/4)=1/8$$. In the interior,
$$V(a,2a)<a$$. At $$b=1/2$$,

$$
J_E=J_F=J_V=\frac{1-2a}{4},\qquad
E_2=\frac{1-2a}{3},
$$

so $$V(a,1/2)\ge a$$, with equality only for $$a=1/6$$.
The intermediate value theorem and strict monotonicity therefore give exactly
one root $$b_*(a)\in[2a,1/2]$$, interior for interior $$a$$. Joint continuity,
compactness, and uniqueness give continuity of this root at every parameter,
including both endpoints. No numerical root computation is used for this
conclusion.

## Exact new example and its exact cutoff

Exact rational arithmetic gives

$$
E_2(3/20,7/20)=\frac5{33},\quad
J_E=\frac{187}{1255},\quad
J_F=\frac{1000}{6919},\quad
J_V=\frac{937}{6424}.
$$

The rational comparisons select $$V=J_E$$, and

$$
\frac3{20}-\frac{187}{1255}=\frac1{1004}>0.
$$

At $$a=3/20$$, the level equation for $$J_E=a$$ reduces to

$$
\frac32b^2-\frac7{10}b+\frac3{50}=0.
$$

Its larger root is

$$
b_0=\frac{7+\sqrt{13}}{30}\in\left(\frac7{20},\frac9{25}\right).
$$

The other branch values do not obstruct identification of the root of $$V$$:

$$
E_2(3/20,b_0)-\frac3{20}
 =\frac{2\sqrt{13}-7}{60}>0,
$$

and strict monotonicity gives

$$
J_F(3/20,b_0)<J_F(3/20,9/25),\qquad
J_F(3/20,9/25)-\frac3{20}=-\frac{136}{51015}<0.
$$

Therefore $$\min(E_2,J_E)=a$$ and $$\min(J_F,J_V)<a$$ at $$b_0$$.
Uniqueness proves

$$
b_*(3/20)=\frac{7+\sqrt{13}}{30},\qquad
B_{\mathrm M}(23/20)=\frac{37+\sqrt{13}}{30}.
$$

All displayed entries in the numerical root table were independently
recomputed and agree to their printed precision. They remain illustrations,
not inputs to the proof.

## Dimension inference

For $$9/8<d<7/6$$ and $$2d-1\le D<1+b_*(d-1)$$, putting
$$a=d-1$$ and $$b=D-1$$ yields

$$
\frac18<a<\frac16,\qquad2a\le b<\frac12,
\qquad V(a,b)<a.
$$

Continuity and the strict gap allow $$s<d$$ and $$u>D$$ sufficiently close
to $$d,D$$ that

$$
\frac18<s-1<\frac16,\quad
2(s-1)<u-1<\frac12,\quad
V(s-1,u-1)<s-1.
$$

These are exactly the open exponent conditions used in the finite-profile
transfer. Its starting grid point is immediately below
$$(1-\zeta)N$$ with fixed $$0<\zeta<1/8$$. Hence it satisfies the new
profile lemma's requirement $$n_0\ge7N/8$$ for all sufficiently large $$N$$;
the finitely many smaller scales do not enter the asymptotic summation.
The bounded edge count and perturbation estimates have the required uniformity.

The curve joins are exact: at $$d=9/8$$ both neighboring expressions give
$$5/4$$, and at $$d=7/6$$ both give $$3/2$$. The existing coherent criterion
handles the first branch and any middle-branch input with $$D<2d-1$$;
the existing unforced criterion handles $$7/6\le d\le5/4$$. Thus the new
profile bound, if combined with the stated analytic transfer, gives the
dimension theorem with the strict inequality printed in the manuscript.

**Result:** no remaining algebraic, root-definition, endpoint, or exponent-slack
gap was found in the current version. This conclusion is confined to the
checks specified above; it is not a claim that the sufficient curve is the
weakest possible condition for distance sets.
