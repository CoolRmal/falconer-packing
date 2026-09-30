# Positive far-annulus selections and a logarithmic criterion

30 September 2026. This note records a weaker analytic target for the natural-language proof. It does **not** improve the Hausdorff–packing dimension curve. The complete proofs are in `packing-unforced-crowding.tex` in the manuscript source.

## What changes in the target

Keep the fixed positive angular restriction from the preceding angular-selection proof, with selected pair measure

$$
d\Pi_A(x,y)=a_A(x,y)\,d\mu(x)d\nu(y).
$$

Let the selected pinned laws and their joint law be

$$
\sigma_y=(d_y)_*(a_A(\cdot,y)\mu),\qquad
\Lambda_A(dy,dt)=d\nu(y)\,\sigma_y(dt).
$$

At resolution epsilon, define full normalized annular crowding, its near-source part, and its far-source part by

$$
\begin{aligned}
H_\epsilon(x,y)
 &=\epsilon^{-1}\int a_A(x',y)
    \mathbf1_{\{||x-y|-|x'-y||\le\epsilon\}}\,d\mu(x'),\\
N_\epsilon(x,y)
 &=\epsilon^{-1}\int_{|x-x'|\le\epsilon^\alpha}a_A(x',y)
    \mathbf1_{\{||x-y|-|x'-y||\le\epsilon\}}\,d\mu(x'),\\
F_\epsilon&=H_\epsilon-N_\epsilon.
\end{aligned}
$$

The previously proved geometric estimate gives

$$
\int N_\epsilon\,d\Pi_A\le C\epsilon^\kappa\to0,
\qquad
\frac1{s+1}<\alpha<1,
\qquad
\kappa=\min\{\alpha(s+1)-1,\alpha(s-1)\}>0.
$$

## Positive mass, rather than a bounded whole collision integral

**Proved criterion.** It suffices to find a finite positive threshold and a sequence tending to zero such that

$$
T>0,\qquad \epsilon_j\to0,\qquad
m:=\limsup_j\Pi_A\{F_{\epsilon_j}\le T\}>0.
$$

The selected joint law then dominates an actual positive density with

$$
\int g\,d\nu\,dt=m,\qquad
\int g^2\,d\nu\,dt\le Tm.
$$

There is a family of pins with the quantitative bounds

$$
\nu(G)\ge\frac m4,\qquad
|\Delta_y(\operatorname{supp}\mu)|\ge\frac{m^2}{16T}
\quad(y\in G).
$$

To prove it, retain precisely the pairs with far crowding at most the threshold. The box mollifier has correlation kernel bounded by the normalized collision indicator. Dropping only the second good-pair indicator bounds the selected squared norm by

$$
T\Pi_A\{F_{\epsilon_j}\le T\}
   +\int N_{\epsilon_j}\,d\Pi_A.
$$

Pass to a subsequence attaining the limsup and use weak compactness in the joint quadratic space. Domination by the full mollified selected law gives a positive submeasure of the original fixed law. The near term tends to zero. Disintegration, Markov, and Cauchy–Schwarz give the pin bounds. Neither a nested selection nor a limit of the individual good-pair sets is assumed.

## Exact scope of the criterion

Write the mass of the absolutely continuous component of the selected law as

$$
m_{\rm ac}=\| (\Lambda_A)_{\rm ac}\|.
$$

For every sequence tending to zero, the manuscript proves the exact identity

$$
\begin{aligned}
m_{\rm ac}
&=\sup_{T>0}\liminf_j\Pi_A\{F_{\epsilon_j}\le T\}\\
&=\sup_{T>0}\limsup_j\Pi_A\{F_{\epsilon_j}\le T\}.
\end{aligned}
$$

The upper inequality is the positive-submeasure criterion. For the lower inequality, disintegrate the joint Lebesgue decomposition. On its absolutely continuous part, one-dimensional differentiation gives convergence of full crowding to twice the density. Far crowding is at most full crowding. Fatou and then increasing the threshold recover all absolutely continuous mass.

Thus this is an exact criterion for a **nonzero absolutely continuous component of the chosen law**. It does not characterize positive length of the distance support: a singular measure can have a support of positive Lebesgue measure. It also does not identify a weakest inequality between dimensions.

## A logarithmic sufficient bound

A stronger, still subquadratic target is

$$
\sup_j\int\log(1+F_{\epsilon_j})\,d\Pi_A\le C_0<\infty.
$$

It gives full absolute continuity and the entropy estimate

$$
\Lambda_A=f(y,t)\,d\nu(y)dt,\qquad
\int f\log(1+f)\,d\nu\,dt\le C_0.
$$

The proof first uses the logarithmic tail bound and the exact mass identity. For a box-smoothed radial density, its value near a selected source radius is at most full crowding at that source pair. Tonelli then bounds its entropy by the logarithmic crowding moment. Finally,

$$
\log(1+F_\epsilon+N_\epsilon)
\le\log(1+F_\epsilon)+N_\epsilon,
$$

and differentiation and Fatou pass to the actual density.

This hypothesis is strictly weaker, at the level of general scalar laws, than any fixed positive fractional crowding moment. The normalized density

$$
f(t)=\frac{2\,\mathbf1_{(0,e^{-1})}(t)}{t(\log(1/t))^3}
$$

has finite entropy and uniformly bounded self-crowding logarithmic moments, but belongs to no power space with exponent greater than one. The manuscript proves these assertions directly. This scalar comparison is not presented as a planar Frostman example.

## What remains to be proved

Beyond the existing dimension curve, the missing geometric estimate is positive mass below a fixed far-crowding threshold. Uniformly tight tails, a logarithmic moment, or the fractional incidence-tail estimate in the companion note would each suffice. None of these new bounds has yet been derived from Hausdorff and packing dimensions in that larger region.

The new argument therefore weakens the **analytic estimate sought**, not the proved **dimension hypothesis**. All statements here concern natural-language proofs; no Lean formalization was changed.
