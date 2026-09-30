# Focused stress check of one inflation step

Date: 30 September 2026.

Scope: the one-step estimate in `output/pdf/packing-unforced-transfer.tex`,
including arbitrary child-dependent selections, enlarged-cube weights, and
auxiliary Fourier labels finer than a standard source cap. This is not a new
audit of the profile optimization or of the full distance theorem.

## Finding

I found no finite-measure counterexample satisfying the actual one-step
hypotheses. The estimate follows from the weighted bandlimited embedding
proved below. The proof makes explicit that local orthogonality is uniform
over **every subset** of the cap family: omitted caps do not need to be
restored before the good-tube estimate is applied.

The genuinely necessary hypotheses are that each parent-cap function is
independent of its child, that a child's selection is constant throughout
the averaging cube, and that its weight and its good-tube mass use the same
parent restriction. The current inherited identity and normalization supply
all three.

## 1. A precise finite-measure embedding statement

Fix one parent, with underlying side length $$b$$, child side $$a\leq b$$,
and a dilation parameter $$L=R^h\geq2$$. Let the child cubes be a subfamily
of an $$a$$-grid. Write $$Q^+$$ for their prescribed concentric enlargements,
$$\widetilde Q=LQ^+$$ for an additional localization enlargement, and
$$P^+$$ for the parent averaging cube. Assume all $$\widetilde Q$$ lie in
an inner portion of $$P^+$$ at Euclidean distance at least $$Lb$$ from its
boundary. The actual manuscript dilations satisfy this for large $$R$$.

Let $$\sigma$$ be any finite positive measure, including an atomic measure.
Set

$$w_Q=\sigma(Q^+),\qquad M=\sigma(P^+).$$

Let $$\Lambda$$ bound the pointwise overlap of the cubes $$Q^+$$. In the
application, $$\Lambda\leq L^{C_K}$$ and $$|P^+|/b^2\leq L^{C_K}$$.

For each cap label $$\theta$$ there is one function $$f_\theta\in L^2$$,
common to all children. Its Fourier support lies in a translate of a rectangle
of widths $$C/a$$ tangentially and $$C/b$$ normally, in its own direction.
These supports also lie in equal-radius frequency balls of radius $$C/a$$
with overlap bounded by a fixed constant. The children select arbitrary
subsets, denoted by numbers $$\varepsilon_{Q,\theta}\in\{0,1\}$$.

Assume that for any dual rectangle $$U$$ of dimensions $$a\times b$$, the
weights of the selected children whose localization enlargements meet it obey

$$
\sum_{\substack{Q:\varepsilon_{Q,\theta}=1\\
                     \widetilde Q\cap U\ne\varnothing}}w_Q
\leq A H\frac ab M,
\tag{1}
$$

where $$A\leq L^{C_K}$$ and $$H\geq1$$. Then

$$
\sum_Qw_Q\int_{Q^+}
 \left|\sum_\theta\varepsilon_{Q,\theta}f_\theta\right|^2\,dm_{Q^+}
\lesssim L^{C_K}HM
 \sum_\theta\int_{P^+}|f_\theta|^2\,dm_{P^+}
 +\mathcal R.
\tag{2}
$$

For every desired decay power, the remainder can be bounded by that power
of $$R^{-1}$$ times a polynomial global-norm bound. Thus it is a rapid error
in the application. No Frostman condition is needed for this statement.

## 2. Orthogonality for arbitrary selected subsets

Choose a Schwartz function $$v_Q$$ that is bounded away from zero on $$Q^+$$,
decays at the scale of $$Q^+$$, and whose Fourier support is a small ball of
radius comparable to the reciprocal side length of $$Q^+$$. Such a function
is obtained by rescaling an inverse Fourier transform of a smooth compactly
supported bump, chosen nearly constant on a fixed unit cube.

Multiplication by $$v_Q$$ only enlarges each frequency ball by a fixed factor,
so their overlap remains uniformly bounded. For an arbitrary selected subset,
Plancherel and bounded overlap give

$$
\left\|v_Q\sum_{\theta:\varepsilon_{Q,\theta}=1}f_\theta\right\|_2^2
\leq C\sum_{\theta:\varepsilon_{Q,\theta}=1}\|v_Qf_\theta\|_2^2.
\tag{3}
$$

There are only selected labels on the right. The same constant works for all
subsets, since deleting frequency supports cannot increase their overlap.
After restricting the left side to $$Q^+$$ and truncating the Schwartz tail
on the right at $$\widetilde Q=LQ^+$$, (3) implies

$$
\int_{Q^+}\left|\sum_\theta\varepsilon_{Q,\theta}f_\theta\right|^2dm_{Q^+}
\leq CL^2\sum_{\theta:\varepsilon_{Q,\theta}=1}
 \int_{\widetilde Q}|f_\theta|^2dm_{\widetilde Q}
 +C_m a^{-2}L^{-m}\sum_\theta\|f_\theta\|_2^2.
\tag{4}
$$

The exponent $$m$$ is arbitrary. Constants can absorb the prescribed
polynomial dilations. Summing the remainder with the weights is harmless
because $$\sum_Qw_Q\leq\Lambda M$$. In particular, arbitrary variation of
the selected subset from one child to the next causes no additional factor.

## 3. The good-tube condition gives a weighted embedding

For each fixed label define the positive averaging measure

$$
\tau_\theta
=\sum_{Q:\varepsilon_{Q,\theta}=1}w_Qm_{\widetilde Q}.
$$

Equation (1) implies, for every dual rectangle,

$$\tau_\theta(U)\leq AH(a/b)M.\tag{5}$$

Modulate $$f_\theta$$ to move the center of its Fourier rectangle to zero.
Choose a smooth Fourier bump equal to one on that rectangle, with inverse
transform $$k_\theta$$. Then $$f_\theta=f_\theta*k_\theta$$ and, in the
tangential and normal coordinates of that rectangle,

$$
|k_\theta(z)|\leq\frac{C_m}{ab}
 \left(1+\frac{|z_{\rm tan}|}{a}+\frac{|z_{\rm nor}|}{b}\right)^{-m},
\qquad \|k_\theta\|_1\leq C.
$$

Cauchy–Schwarz gives

$$
|f_\theta(x)|^2
\leq C\int |f_\theta(y)|^2|k_\theta(x-y)|\,dy.
$$

Integrating against $$\tau_\theta$$ and covering space by translates of the
dual rectangle, (5) and the summable kernel decay yield

$$
\int |k_\theta(x-y)|\,d\tau_\theta(x)
\leq C\frac{AHM}{b^2}
\quad\text{for every }y.
\tag{6}
$$

The factor $$a/b$$ in the tube mass divided by the tube area $$ab$$ is
exactly $$b^{-2}$$. This is the cancellation that makes the threshold occur
linearly.

For $$y\notin P^+$$, the support margin of $$\tau_\theta$$ makes the same
kernel bounded by an arbitrary negative power of $$L$$ times
$$1/(ab)$$. Also $$\tau_\theta(\mathbb R^2)\leq\Lambda M$$. Therefore

$$
\int |f_\theta|^2\,d\tau_\theta
\leq C\frac{AHM}{b^2}\int_{P^+}|f_\theta|^2\,dy
 +C_m\frac{\Lambda M}{ab}L^{-m}\|f_\theta\|_2^2.
\tag{7}
$$

Converting the parent integral to its normalized average costs
$$|P^+|/b^2\leq L^{C_K}$$. Combining (4) and (7) proves (2).
Since $$a\geq R^{-1}$$ in the application, all displayed inverse-volume
factors are polynomial in $$R$$. With fixed $$h>0$$, choosing $$m$$ large
enough gives any required rapid-decay power after the remaining polynomial
sums and norm bounds.

## 4. Why the actual coarsened marks imply (1)

Fix an auxiliary Fourier label and a dual rectangle $$U$$ meeting at least
one selected $$\widetilde Q_0$$. The direction of its effective marking
label differs from its Fourier direction by at most a constant times
$$a/b$$. Over length $$b$$ that rotation changes transverse position by at
most a constant times $$a$$.

Every $$Q^+$$ with $$\widetilde Q\cap U\ne\varnothing$$ lies in the
effective test tube centered at $$Q_0$$ after its prescribed dilation. The
test dilation dominates both the additional localization factor and the
child enlargement factor. All these cubes also lie in $$P^+$$. Consequently

$$
\sum_{\substack{Q:\varepsilon_{Q,\theta}=1\\
                     \widetilde Q\cap U\ne\varnothing}}\sigma(Q^+)
\leq\Lambda\,\sigma(T_{Q_0,\mathrm{eff}}^+\cap P^+)
\leq\Lambda H(a/b)\sigma(P^+).
$$

This proves (1), allowing additional fixed geometric dilation factors in
$$A$$. Crucially, positivity alone is not being used to identify arbitrary
weights with tube masses: the weights are precisely masses of the enlarged
children under the same measure as the good-tube test.

For the actual dilations, write $$L=R^h$$. The child cube has side
$$L^{2j+2}a$$, its localization has side $$L^{2j+3}a$$, and the parent
averaging cube has side $$L^{2j+4}b$$. Since $$a\leq b$$, their support
margin is at least $$Lb$$ for sufficiently large $$R$$. The test dilation
$$L^{4K_0+20}$$ contains all the needed child neighborhoods and rotated
dual rectangles. Thus the support and containment hypotheses of the finite
embedding are supplied by the stated construction, including when adjacent
chain scales are close.

## 5. Concrete finite probes

These numerical probes illustrate the estimate; the preceding proof does not
depend on them.

For a genuinely finer-than-standard Fourier family, take
$$R=4096$$, $$a=1/32$$, $$b=1$$, and 64 plane-wave frequencies on a circle
of radius $$R$$ with consecutive angular spacing $$1/128$$. Standard cap
width is $$1/64$$, so effective labels group adjacent fine pairs. The
normalized Gram matrix on an $$a$$-square has entries

$$
G_{kl}=\operatorname{sinc}(a(\xi_{k,1}-\xi_{l,1}))
       \operatorname{sinc}(a(\xi_{k,2}-\xi_{l,2})),
$$

with $$\operatorname{sinc}(x)=\sin(\pi x)/(\pi x)$$. Its eigenvalues were
between approximately $$0.8887961$$ and $$1.0292336$$. Across 500 randomly
selected unions of adjacent pairs, no compressed matrix had a larger norm.
In fact the latter assertion holds exactly for all subsets: a principal
compression of a positive semidefinite matrix cannot increase its operator
norm. Translating the child square just conjugates this Gram matrix by a
diagonal unitary matrix.

To test the threshold dependence with atomic pins, use a periodic unit-square
toy model with 32 equally weighted atoms in one vertical column, one in each
child row. Take the horizontal Dirichlet function

$$
f(x)=32^{-1/2}\sum_{k=0}^{31}e^{2\pi i k(x-x_0)}.
$$

Its unit-parent squared average is one. Its squared average over the child
column of width $$1/32$$ centered at $$x_0$$ is approximately
$$24.76345$$. The selected vertical test tube has all the pin mass, so its
good threshold requires $$H=32$$. The one-step ratio is therefore about
$$0.773858H$$. This shows that linear dependence on the threshold is already
the correct scale in a simple finite example; arbitrary atomic concentration
does not create a second factor of the threshold.

## 6. Limits of this conclusion

The finite embedding would not apply if selections varied pointwise inside
the child integration, if unrelated weights were substituted for the enlarged
cube masses, or if the alleged parent functions secretly depended on their
children. Those changes can destroy the relevant frequency-support or mass
conditions. They do not occur in the current exact inherited identity.

This check establishes the one-step implication from the stated geometric
and Fourier hypotheses. It does not independently establish that a complete
distance-set construction supplies those hypotheses at every frequency, or
that the resulting dimension condition is optimal.
