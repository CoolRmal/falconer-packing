# Independent audit of fractional far-bisector crowding

Date: 2026-09-30. Audited sources: `research/2026-09-30-fractional-far-bisector-crowding.md` and `output/pdf/packing-unforced-crowding.tex`. No source modifications were needed. All conclusions below concern one fixed positive selected source–pin law. They establish conditional analytic criteria, not a new implication from Hausdorff and packing dimensions.

## 1. The fixed law and near contribution

The source probability is s-Frostman, with s greater than one. Source and pin supports are compact and separated, and all their distances lie between fixed positive constants. With a fixed angular selection kernel, write

$$
\Pi_A(dx,dy)=a_A(x,y)\,d\mu(x)d\nu(y),
\qquad 0\le a_A\le1,
\qquad 0<M:=\Pi_A(\mathbb R^2\times\mathbb R^2)\le1.
$$

The conditional radial measures and their joint law are

$$
\lambda_y=(d_y)_*(a_A(\cdot,y)\mu),
\qquad
\Lambda_A(dy,dt)=d\nu(y)\lambda_y(dt).
$$

For a fixed exponent and its corresponding positive decay exponent,

$$
\frac1{s+1}<\alpha<1,
\qquad
r_\varepsilon=\varepsilon^\alpha,
\qquad
\kappa_0=\min\{\alpha(s+1)-1,\alpha(s-1)\}>0,
$$

decompose the distance crowding into partners at source distance at most the cutoff and its complement:

$$
H_\varepsilon=N_\varepsilon+F_\varepsilon,
\qquad
H_\varepsilon(x,y)=
\varepsilon^{-1}\lambda_y([|x-y|-\varepsilon,|x-y|+\varepsilon]).
$$

The previously proved near estimate gives

$$
\int N_\varepsilon\,d\Pi_A\le CA\varepsilon^{\kappa_0}.
$$

For every fixed exponent between zero and one, concavity on the same finite measure gives

$$
\int N_\varepsilon^\gamma\,d\Pi_A
\le M^{1-\gamma}(CA\varepsilon^{\kappa_0})^\gamma
\longrightarrow0.
$$

There is no change of pair weighting here. This is the essential reason that the existing near estimate remains useful below the quadratic norm.

## 2. Fractional moments do give the actual selected density

With the probability box kernel of width epsilon, put

$$
\phi_\varepsilon(t)=\varepsilon^{-1}
\mathbf1_{[-\varepsilon/2,\varepsilon/2]}(t),
\qquad f_\varepsilon(y,t)=\phi_\varepsilon*\lambda_y(t).
$$

If a radial point r contributes to this convolution at t, its defining interval lies in the interval of radius epsilon centered at r. Tonelli therefore proves the exact inequality

$$
\int f_\varepsilon^{1+\gamma}\,d\nu\,dt
\le\int H_\varepsilon^\gamma\,d\Pi_A
\le\int F_\varepsilon^\gamma\,d\Pi_A
   +M^{1-\gamma}(CA\varepsilon^{\kappa_0})^\gamma.
$$

A uniform bound along any sequence tending to zero gives weak compactness in the fixed reflexive space of exponent one plus gamma. Continuous tests identify the limit with the unchanged law. In particular, if the far moments are bounded by L, the density has norm power at most L. The fixed bounded radial support permits the constant test for mass preservation. Disintegration then gives positive-length pinned supports on a positive-measure set of pins.

The proof requires neither convergence of source masks nor a new source measure. The fixed angular kernel is present in both source factors throughout.

## 3. Exact normalization and the tail calculation

For dyadic source separation u, define

$$
\theta_{x,x'}=\frac{x-x'}{|x-x'|},\qquad
c_{x,x'}=\frac{|x|^2-|x'|^2}{2|x-x'|},
$$

and, after normalizing the source diameter to at most one,

$$
Q_{\varepsilon,u}(x,y)=
\frac1{\varepsilon u^{s-1}}
\int_{u/2<|x-x'|\le u}
a_A(x',y)
\mathbf1_{\{|y\cdot\theta_{x,x'}-c_{x,x'}|
                    \le C_0\varepsilon/u\}}\,d\mu(x').
$$

The factor is exactly epsilon times the source separation to the power s minus one. If all source–pin distances are at most b, the choice of constant two b is valid: the squared-distance identity and the lower annulus radius give

$$
2|x-x'|\,|c_{x,x'}-y\cdot\theta_{x,x'}|
\le2b\varepsilon
\quad\Longrightarrow\quad
|c_{x,x'}-y\cdot\theta_{x,x'}|\le2b\varepsilon/u.
$$

Consequently,

$$
F_\varepsilon(x,y)
\le\sum_{\substack{u\le1\ \mathrm{dyadic}\\u>r_\varepsilon}}
u^{s-1}Q_{\varepsilon,u}(x,y).
$$

The annulus overlapping the cutoff can include additional near partners; their nonnegative contribution only enlarges the right side.

Assume fixed constants and fixed exponents, independent of resolution and source separation, satisfy

$$
\Pi_A\{Q_{\varepsilon,u}>t\}
\le C_*u^{-\kappa}t^{-\beta},
\qquad t\ge1,
\qquad C_*\ge1,\quad\kappa\ge0,\quad\beta>0.
$$

The level-set mass is also at most one. For a fixed fractional exponent smaller than both one and beta, split layer cake at

$$
T_u=(C_*u^{-\kappa})^{1/\beta}\ge1.
$$

Then

$$
\begin{aligned}
\int Q_{\varepsilon,u}^\gamma\,d\Pi_A
&\le\gamma\int_0^{T_u}t^{\gamma-1}\,dt
  +\gamma C_*u^{-\kappa}\int_{T_u}^\infty
                      t^{\gamma-\beta-1}\,dt\\
&=\frac\beta{\beta-\gamma}
 C_*^{\gamma/\beta}u^{-\kappa\gamma/\beta}.
\end{aligned}
$$

Thus the source-scale loss is the fraction gamma over beta of kappa, rather than kappa itself. Subadditivity of the fractional power yields

$$
\int F_\varepsilon^\gamma\,d\Pi_A
\le\frac\beta{\beta-\gamma}C_*^{\gamma/\beta}
\sum_{u\le1\ \mathrm{dyadic}}
u^{\gamma(s-1-\kappa/\beta)}.
$$

The series converges under precisely the stated strict condition

$$
\boxed{\kappa<\beta(s-1).}
$$

This proves the conditional criterion for every fixed

$$
0<\gamma<\min\{1,\beta\}.
$$

No bound on beta or kappa in terms of the two set dimensions has been proved.

## 4. Why the currently available first moments do not close the argument

Angular domination and the s-Frostman source estimate supply only

$$
\int Q_{\varepsilon,u}\,d\Pi_A
\lesssim A\left(1+\frac{u^2}{\varepsilon}\right).
$$

If the pin probability is t-Frostman, with t greater than one, covering the bounded bisector strip gives instead

$$
\int Q_{\varepsilon,u}\,d\Pi_A
\lesssim\left(\frac u\varepsilon\right)^{2-t}.
$$

Indeed the strip width is epsilon over u, so its pin mass is bounded by that width to the power t minus one. Multiplication by the source annulus mass and division by the definition's normalization gives exactly the displayed power.

For a fixed positive u and pin exponent below two, both available bounds permit divergence as resolution tends to zero. Markov only changes them into tails with the same divergent coefficient. Jensen on a fractional moment raises the coefficient to a positive power; it does not make it independent of resolution.

This is a logical insufficiency of these estimates, not a theorem that the desired tail is false: an upper bound that grows with resolution can hold for variables which have excellent tails or for variables which are constant at a value tending to infinity. Hence neither first-moment inequality alone implies the needed uniform tail. The endpoint pin exponent two is different: its strip bound is uniform and is not part of this stated obstruction.

## 5. Audit of the root crowding fragment and its scope

The fragment `output/pdf/packing-unforced-crowding.tex` correctly proves that a fixed positive mass below some finite far-crowding threshold produces a nonzero absolutely continuous component of the selected law. Its kernel correlation inequality, domination after weak convergence, and quantitative pin estimates check. In its notation, retained mass m and threshold T give quadratic norm at most Tm and a pin set of measure at least one quarter of m with distance length at least

$$
\frac{m^2}{16T}.
$$

Its exact mass formula also checks. Writing the absolutely continuous mass relative to the product of pin measure and radial Lebesgue measure as the following quantity, one has for every resolution sequence

$$
m_{\rm ac}
=\sup_{T>0}\liminf_j\Pi_A\{F_{\varepsilon_j}\le T\}
=\sup_{T>0}\limsup_j\Pi_A\{F_{\varepsilon_j}\le T\}.
$$

For the upper bound, every threshold's limsup supplies a dominated quadratic density of that mass. For the reverse bound, disintegration identifies the fibrewise absolutely continuous density, and differentiation gives the full crowding limit equal to twice that density almost everywhere for its own mass. The inequality between far and full crowding and Fatou then recover the entire absolutely continuous mass as the threshold increases.

The fragment explicitly and correctly limits this equivalence to the chosen law. Positive length of its distance support is not characterized: a singular measure can be supported on a positive-length set. No claim about the weakest dimension condition follows from the equivalence.

Finally, the logarithmic criterion is valid. The box-kernel calculation bounds the entropy of the mollified density by the far logarithmic moment plus the vanishing near first moment. Far-crowding tightness first proves full absolute continuity, and differentiation plus Fatou proves the claimed entropy bound. The scalar logarithmic-density example is a valid comparison between integrability conditions, not a geometric counterexample or dimensional improvement.

**Audit result:** no substantive error found in either source. The new analytic requirement remains a proved conditional criterion with an explicitly missing geometric estimate.
