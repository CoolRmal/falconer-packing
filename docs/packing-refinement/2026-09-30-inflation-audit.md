# Independent audit of the finite-profile analytic transfer

Date: 30 September 2026.

Scope: the good/bad decomposition, inherited cap algebra, Fourier inflation,
and shell reconstruction in `output/pdf/packing-bound-finite-profile.tex`.
This is a mathematical audit of a manuscript, not a Lean proof, an external
referee report, or a proof that the resulting dimension condition is optimal.
The combinatorial chain bound is outside this audit.

## Verdict

I did not find a fatal analytic error in the transfer with the **forced
terminal depth** $$n_{K-1}=N/2.$$ Its principal Fourier step really uses just
the curvature inequality $$r_{j+1}\leq r_j^2,$$ inherited cap deletion, and
the stated conditional good-tube bound. It does not require Liu's original
fixed sequence of squaring scales.

The manuscript should make the packet intersection convention precise:
"a packet meeting a cube" must mean an appropriately enlarged packet tube
meeting that cube. The corresponding rapid-decay claim for the un-enlarged
tube is not literally valid. This is repairable by the same fixed enlargement
used in Liu's Lemma 4.2, and changes none of the exponents.

Removing the forced terminal depth is **not** justified by the current
proof. Merely replacing the finest packets by thinner angular caps introduces
a potentially substantial packet multiplicity in the bad-part first norm;
see the final section. This is a specific issue beyond checking the curvature
condition.

## Primary source checked

[Bochen Liu, *Lebesgue measure of distance sets with regular pins and
multi-scale Mizohata–Takeuchi-type estimates*, version 3, 16 July 2026]
(https://arxiv.org/pdf/2603.15328v3).

The relevant inputs are its Section 2 localization principles, Lemma 3.1
(packet first-norm localization), Lemma 4.2 (cap reconstruction), Lemma 4.3
(inherited-cap identity), and the proof of Lemma 4.4 (inflation).
The last two are sufficiently explicit to check how a variable chain enters.
Liu's Theorem 1.1 itself assumes equal Hausdorff and packing dimension of the
pin set; it does not by itself certify the manuscript's unequal-dimension
criterion.

## What the analytic proof actually needs

At a frequency $$R=2^N,$$ fix a finite chain

$$
R^{\zeta+o(1)}=r_0<r_1<\cdots<r_{K-1}=R^{1/2}<r_K=R,
\qquad r_{j+1}\leq r_j^2,
$$

with $$K$$ bounded independently of $$R.$$ Let the pin probability be
$$\sigma,$$ and let $$Q_j$$ have side $$r_j/R.$$ The relevant datum at edge
$$j$$ is a threshold $$H_j\geq1$$ such that a retained angular cap at
$$Q_j\subset Q_{j+1}$$ has

$$
\sigma_{Q_{j+1}^{+}}(T_{Q_j,\theta}^{+})
\leq H_j\frac{r_j}{r_{j+1}}.
\tag{1}
$$

Here $$T_{Q_j,\theta}^{+}$$ is a sufficiently enlarged version of the
$$r_j/R\times r_{j+1}/R$$ tube centered at $$Q_j,$$ and the same enlarged
parent $$Q_{j+1}^{+}$$ must be used in deletion and in inflation. Enlargements
are powers $$R^{C_Kh}$$ with $$h>0$$ chosen after $$K.$$

Provided the bad packet first norms are summably small, the analytic loss is

$$
R^{C\zeta+C_Kh}\prod_{j<K}H_j.
\tag{2}
$$

This statement separates the harmonic analysis from the optimization of the
profile exponent. Nothing in this calculation shows that a proposed upper
bound on the product is a sharp upper bound over all admissible chains.

## Check of the conditional deletion estimate

Let $$\lambda$$ be the pin probability restricted and normalized on one
enlarged parent of underlying size $$b,$$ and let $$\rho=a/b$$ for the
child size $$a.$$ On a $$\rho$$-net of directions, use a tube cover with
bounded multiplicity in each direction. Double counting yields

$$
\sum_T\lambda(T)^2
\lesssim
\iint\min\{\rho^{-1},b/|y-z|\}\,d\lambda(y)d\lambda(z),
\tag{3}
$$

up to the prescribed enlargement powers. The diagonal term is correctly
truncated; this argument does not require finite untruncated conditional
one-energy.

For a fixed pin $$y,$$ write $$v_y$$ for the angular density of the source
measure seen from $$y.$$ A maximal-density cutoff at $$L$$ gives

$$
\int_{\{Mv_y>L\}}v_y\lesssim_q L^{1-q}\|v_y\|_q^q.
\tag{4}
$$

For a heavy pin tube with $$\lambda(T)>H\rho,$$ the associated source tube,
if used by any retained pair, has source mass at most $$CL\rho.$$ This follows
because its angular image from the pin of that pair is contained in an
interval of length $$C\rho$$ centered within $$C\rho$$ of the retained
direction. Source–pin separation is essential here. Consequently the mass of
retained pairs using heavy tubes is bounded by

$$
CL\rho\sum_{\lambda(T)>H\rho}\lambda(T)
\leq\frac{CL}{H}\sum_T\lambda(T)^2.
\tag{5}
$$

These estimates support the manuscript's choice
$$H_j=R^{D_2h+C\Gamma}2^{c_j}$$ when the conditional truncated energy is at
most $$R^{C\Gamma+o(1)}2^{c_j}.$$ The source-heavy set is only an auxiliary
device for estimating bad mass. It is not a new arbitrary deletion in the
Fourier sum; this distinction is necessary for the inherited-cap identity.

## Check of the one-step Fourier inequality

Fix a parent cube $$P=Q_{j+1}$$ and a parent angular label. Partition finest
cap labels into a nested finite tree. Define each intermediate function as
the sum of labels surviving all ancestor marks from that scale onward.
Then the identity

$$
F_{Q_j,\alpha}
=\sum_{\theta\subset\alpha:\,\theta\text{ good at }Q_j}
 F_{P,\theta}
\tag{6}
$$

is exact. In particular, $$F_{P,\theta}$$ on the right is independent of the
child cube. Smooth multiplier supports may overlap boundedly, while labels
have a unique parent. These are compatible requirements.

The Fourier supports in (6) occupy bounded-overlap balls of radius
$$O(R/r_j).$$ Local orthogonality at physical scale $$r_j/R$$ therefore
reduces the square of the sum to the sum of squares with the usual small
power loss. A cap of width $$1/r_j$$ on a circle of radius comparable to
$$R$$ lies in a rectangle of tangential width $$O(R/r_j)$$ and normal width
$$O(R/r_j^2).$$ The latter is at most $$O(R/r_{j+1})$$ by curvature
admissibility. Convolution by the fixed compact frequency cutoff adds a
bounded width, also absorbed because $$r_{j+1}\leq R.$$

Thus $$F_{P,\theta}$$ is locally constant, with small-power enlargements and
rapidly decreasing tails, on tubes of dimensions
$$r_j/R\times r_{j+1}/R.$$

For any such tube touching good children, the sum of the weights of their
enlarged cubes is bounded by

$$
R^{C_Kh}H_j\frac{r_j}{r_{j+1}}\sigma(P^+).
\tag{7}
$$

Indeed, one of the good children's test tubes contains the relevant tube and
all contributing enlarged children after the fixed power enlargements;
their cube overlap costs another $$R^{C_Kh}.$$ Applying (1) then proves (7).
Local constancy converts the pointwise square to an average on an enlarged
dual tube. The ratio of parent area to tube area contributes
$$r_{j+1}/r_j,$$ canceling the ratio in (7). Summing the tube cover costs only
its enlargement multiplicity. Therefore

$$
\sum_{Q_j\subset P}\sigma(Q_j^+)
 \int |F_{Q_j,\alpha}|^2\,dm_{Q_j^+}
\lesssim R^{C_Kh}H_j\sigma(P^+)
 \sum_{\theta\subset\alpha}\int|F_{P,\theta}|^2\,dm_{P^+}
+\operatorname{RapDec}(R).
\tag{8}
$$

The addition of omitted bad children or tubes occurs only on the nonnegative
upper-bound side. It does not change a Fourier function. This is the same
logical operation as in the final step of Liu's Lemma 4.4.

No extra factor proportional to the number of children or regularized
components occurs in (8).

## Packet reconstruction and summation

For the standard finest caps, a packet has width $$R^{-1/2+h}.$$ A separated
source–pin pair lies in at most $$R^{Ch}$$ enlarged packet tubes: there are
only $$R^{Ch}$$ finest angular labels within that width of the connecting
line. At intermediate scales,

$$
R^{-1/2}\leq\frac1{r_j}\leq\frac{r_j}{r_{j+1}},
$$

so packet-direction uncertainty and cap uncertainty are contained in the
enlarged conditional test tube. The pair-counting bound therefore gives the
bad first-norm estimate used in the manuscript.

For precision, packets must be removed when their enlarged tubes intersect
the initial pin cube, as in Liu's condition involving $$2T\cap Q.$$ Being
outside an un-enlarged tube does not give rapid decay close to its boundary.
With this convention, Liu's Lemma 4.2 identifies the circular extension of
the retained packets with the surviving cap sum on the initial cube.

The fixed cutoff near the source is legitimate: outside that fixed
neighborhood, every annular cap multiplier applied to the source measure is
rapidly small, together with each fixed number of derivatives. Its shortest
available transverse decay scale is $$R^{-1/2},$$ which still gives arbitrary
polynomial decay at fixed positive separation. Summing polynomially many
packets and cubes preserves rapid decay.

At the final scale, all deletion labels have been exposed, and Plancherel
followed by Cauchy–Schwarz in the fixed frequency smoothing gives

$$
\sum_\theta\|F_\theta\|_2^2
\lesssim R^{-1}\int_{S^1}|\widehat\mu(r\omega)|^2\,d\omega.
\tag{9}
$$

Together with (2), this has exactly the exponent displayed in the manuscript.
Applying the pinned quadratic identity separately for each pin allows the
source function to depend on that pin. Integration in circle radius and the
source energy estimate give

$$
\int\|(d_y)_*G_{R,y}\|_2^2\,d\nu(y)
\lesssim R^{1-s+\sum_jc_j/N+\eta}I_s(\mu).
\tag{10}
$$

Original pin restrictions at each frequency are important: their weighted
sum is the original pin measure off a small remainder. On that remainder
one must use the whole annular kernel's bounded first norm, as the manuscript
does. Summable bad first norms and summable good second norms then identify
the resulting joint density with the original distance law by separated
smooth tests. A fixed compact source cutoff makes the radial variable range
bounded, so second-norm convergence also implies first-norm convergence
there. No passage to a changing limiting pin measure is involved.

## A barrier to the proposed adaptive terminal scale

Suppose the last angular radius is changed to
$$r_*=R^\beta>R^{1/2}.$$ The finest cap width becomes $$1/r_*,$$ while its
natural spatial packet width is $$r_*/R.$$ Even when the geometric
cap-to-pair inequalities

$$
\frac{r_*}{R}\leq\frac{r_j}{r_{j+1}}
\tag{11}
$$

hold at all earlier steps, the absolute packet counting used in the bad-part
bound now sees as many as

$$
\frac{r_*/R}{1/r_*}=\frac{r_*^2}{R}=R^{2\beta-1}
\tag{12}
$$

angular labels for one separated pair. This is a genuine power, not an
arbitrarily small enlargement loss, when $$\beta-1/2$$ is fixed. Nearby
directions through that pair realize this geometric multiplicity; one cannot
replace it by $$R^{o(1)}$$ merely by redrawing the tube cover.

Writing $$\ell=N(1-\beta)$$ for the terminal physical depth, (11) is the gap
restriction $$n_j-n_{j+1}\leq\ell.$$ Thus both this restriction **and** the
additional bad-part multiplicity need treatment in an adaptive-terminal
proposal. Increasing deletion thresholds to compensate for (12) may incur a
new main exponent in the good-part estimate. A cancellation argument, a
different packet decomposition, or a sharper first-norm estimate would be
needed to avoid that exponent. No such argument is established here.

This obstruction applies to the current proof method; it is not a
counterexample to any pinned-distance theorem.

## Addendum: generic-cost transfer theorem

The following version makes explicit what a replacement chain lemma has to
provide. It is independent of the particular old formula for the chain cost.

**Theorem.** Let $$\mu,\nu$$ be compactly supported probability measures in
the plane with positively separated supports. Suppose that for some
$$s>1$$ and $$q>1$$,

$$
I_s(\mu)<\infty,
\qquad
B:=\int\left\|\frac{d(\pi^y_*\mu)}{d\theta}\right\|_q^q\,d\nu(y)
<\infty.
\tag{13}
$$

Fix a number $$c\geq0.$$ Assume the following finite-profile hypothesis.
For every sufficiently small $$\zeta>0$$ there is an integer
$$K_\zeta<\infty$$ such that, for every sufficiently small $$\delta>0,$$
one can choose an integer $$T,$$ a number $$\tau>0,$$ and constants
independent of $$N$$ with the following properties for all sufficiently
large multiples $$N$$ of $$2T.$$ Put $$R=2^N.$$

1. There are finitely many disjoint Borel pin pieces $$X_i$$ with original
   weights $$w_i=\nu(X_i)$$ and original normalized restrictions
   $$\sigma_i=w_i^{-1}\nu|_{X_i},$$ such that

   $$
   \nu\!\left(\mathbb R^2\setminus\bigcup_iX_i\right)\leq C_\delta R^{-\tau},
   \qquad w_i\geq C_\delta^{-1}R^{-\delta}.
   \tag{14}
   $$

2. For each piece there is a profile $$f_i$$ on the $$T$$-grid with
   $$f_i(0)=0,$$ slopes in $$[0,2],$$ and with every active depth-$$k$$
   dyadic cube satisfying

   $$
   C_\delta^{-1}R^{-\delta}2^{-f_i(k)}
   \leq\sigma_i(Q)\leq C_\delta2^{-f_i(k)}.
   \tag{15}
   $$

3. Put $$g_i(k)=f_i(k)-k.$$ Each piece admits a decreasing $$T$$-grid
   chain, with at most $$K_\zeta$$ edges,

   $$
   n_{i,0}>n_{i,1}>\cdots>n_{i,K_i}=0,
   \quad n_{i,K_i-1}=N/2,
   \quad |n_{i,0}-(1-\zeta)N|\leq C_\delta T,
   \quad 2n_{i,j}-n_{i,j+1}\leq N.
   \tag{16}
   $$

   Its costs obey

   $$
   c_{i,j}:=g_i(n_{i,j+1})-
        \min_{[n_{i,j+1},n_{i,j}]}g_i\geq0,
   \qquad
   \sum_{j<K_i}c_{i,j}\leq(c+\delta)N+C_\delta.
   \tag{17}
   $$

Then, if $$c<s-1,$$

$$
(d_y)_*\mu\ll\mathcal L^1
\quad\text{for }\nu\text{-almost every }y.
\tag{18}
$$

The assertion remains valid if the lower bound in (15), the component bound
in (14), or the error in (17) has a fixed multiple of $$\delta$$ in place
of $$\delta.$$ It is the ability to make that loss arbitrarily small,
after fixing $$\zeta,$$ that matters. Likewise, a bound
$$cN+o(N)$$ with the other losses arbitrarily small is sufficient.

**Proof.** Fix $$\eta>0$$ so that $$c+\eta<s-1.$$ Choose $$\zeta$$ so
small that the initial localization exponent is below $$\eta/4,$$ then
fix the corresponding bound $$K=K_\zeta.$$ The rest of the proof has
constants depending on this fixed $$K$$ and the fixed $$q.$$

For an edge with parent depth $$m$$ and child depth $$n,$$ let
$$b=2^{-m},a=2^{-n},\rho=a/b.$$ If $$P$$ is an active parent cube and
$$P^+$$ is any enlargement by a factor at most $$R^{C_Kh},$$ its mass is
at least the mass of $$P.$$ Therefore (15), and a bounded cover of a ball
by dyadic cubes at each $$T$$-grid scale, give

$$
\sigma_{i,P^+}(B(z,2^{-k}))
\leq C_{\delta,T}R^{\delta}2^{f_i(m)-f_i(k)}
\quad(m\leq k\leq n).
\tag{19}
$$

Intermediate integer depths can either be included using monotonicity, at
cost $$2^{O(T)},$$ or the annular sum can be grouped into $$T$$-blocks.
Thus (19) implies

$$
J_{\sigma_{i,P^+}}(\rho)
\leq C_{\delta,T}(N+1)R^{\delta}2^{c_{i,j}}.
\tag{20}
$$

Distances exceeding $$b$$ contribute at most one, and enlargements of the
kernel or tubes contribute only $$R^{C_Kh}.$$ This proves the required
conditional estimate without assuming any lower regularity of an arbitrary
intersection with the boundary of $$P^+.$$

Equation (13) and (14) imply

$$
\int\|v_y\|_q^q\,d\sigma_i(y)
\leq C_\delta B R^\delta.
\tag{21}
$$

Use the cutoffs

$$
L=R^{A_1h},
\qquad H_{i,j}=R^{A_2h+2\delta}2^{c_{i,j}},
\tag{22}
$$

where $$A_1,A_2$$ are sufficiently large in terms of $$K,q$$ and the
geometric enlargement constants. The logarithm in (20) can be absorbed by
$$R^\delta$$ for large $$R.$$ Equations (3)–(5), (20), and (21) show that
the source-heavy and pin-heavy pair masses, summed over all edges and
parents with weights $$\sigma_i(P^+),$$ are bounded by

$$
C R^{C_Kh+\delta-A_1h(q-1)}
+C R^{C_Kh+A_1h-A_2h}.
\tag{23}
$$

Choose $$A_1,A_2$$ so that both exponents, when $$\delta\ll h,$$ remain
negative even after the $$R^{C_Kh}$$ packet multiplicity in the bad-part
first norm. The constants $$A_1,A_2$$ are now fixed. Next choose $$h>0$$
so small that all Fourier inflation losses, including $$KA_2h,$$ are below
$$\eta/4.$$ Finally choose $$\delta>0$$ so small that it is compatible
with (23) and all remaining costs involving $$K\delta$$ are below
$$\eta/4.$$ Apply the finite-profile hypothesis with these choices.
This order resolves the apparent dependence between the number of scales,
the deletion exponents, and the allowable profile error.

Use standard annular packets with finest angular width $$R^{-1/2}$$ and
tube width $$R^{-1/2+h}.$$ Remove a marked packet from the source function
for $$Q_0$$ whenever an enlarged packet tube, for example $$2T,$$
intersects $$Q_0.$$ Use a larger fixed tube, for example $$10T,$$ in the
first-norm bound. The exact numerical constants can all be enlarged once
at the start. Lemma 3.1 and Lemma 4.2 of Liu, together with the pair geometry
checked above, now give source functions $$G_{R,i,Q_0}$$ such that

$$
\int\|(d_y)_*(P_R\mu-G_{R,i,Q_0(y)})\|_1\,d\sigma_i(y)
\leq C R^{-\epsilon_1}
\tag{24}
$$

for some fixed $$\epsilon_1>0.$$

The inherited-cap identity (6) and one-step estimate (8) apply on precisely
the chain (16), because $$r_j=R2^{-n_{i,j}}$$ has
$$r_{j+1}\leq r_j^2$$ and $$r_{K_i-1}=R^{1/2}.$$ From (17), (22), initial
localization, and (9),

$$
\int|G_{R,i,Q_0(y)}*\widehat\omega_r(y)|^2\,d\sigma_i(y)
\leq C R^{-1+c+\eta}
 \int_{S^1}|\widehat\mu(r\omega)|^2\,d\omega
+\operatorname{RapDec}(R).
\tag{25}
$$

Small portions of the budget $$\eta$$ can be reserved for the rapidly
decreasing errors; changing it to a slightly smaller initial margin does
not alter the conclusion. With a fixed smooth source cutoff, Liu's pinned
quadratic identity and $$I_s(\mu)<\infty$$ imply

$$
\int\|(d_y)_*G_{R,i,Q_0(y)}\|_2^2\,d\sigma_i(y)
\leq C R^{1-s+c+\eta}I_s(\mu).
\tag{26}
$$

All constants here are uniform in the index $$i$$ and frequency $$R,$$
once $$\zeta,h,\delta,T$$ and the fixed measures have been chosen. All
norms which multiply rapidly decreasing errors have polynomial bounds:
the Fourier input is a probability measure, the number of caps and cubes
is polynomial, and (14)–(15) provide polynomial lower bounds on every
normalization used in the construction.

Define $$G_{R,y}$$ on $$X_i$$ by this construction and set it to zero on
the discarded remainder. Multiply (24) and (26) by $$w_i$$ and sum. The
components are disjoint original restrictions, so no component-counting
loss appears. On the remainder, use $$\|P_R\mu\|_1\leq C_T$$ for the
entire annular kernel, giving an additional error $$C R^{-\tau}.$$
The result is a summable bad first norm and a summable good second norm
over the geometric frequency sequence $$R=2^{2T\ell}.$$

Finite annular sums reconstruct $$\mu$$ in distributions. Their pushforward
identification may be tested against $$\Phi(y,|x-y|),$$ with smooth compact
$$\Phi$$ and the fixed source cutoff. Source–pin separation makes the
resulting test function of $$x$$ smooth; derivatives can be integrated
against the finite measure $$\nu.$$ First-norm convergence then identifies
the limiting joint density with the pushforward of $$\nu\times\mu$$ under
$$ (y,x)\mapsto(y,|x-y|).$$ Disintegration gives (18). This proves the
theorem.

## Applying a replacement chain bound

To use the theorem for a dimension criterion, take a compact source and pin
restriction from a set with a Frostman exponent $$t>s>1,$$ where the pin
support has upper box dimension below $$u.$$ Orponen's radial-projection
estimate supplies (13). Finite regularization supplies (14)–(15) with
arbitrarily small $$\delta,$$ and supplies profiles with barriers

$$
sk-o_\delta(1)N-O_T(1)\leq f_i(k)\leq uk+O_T(1).
\tag{27}
$$

A replacement combinatorial lemma must apply to these **approximate**
barriers. If it is first proved for exact barriers, uniform clamping and
grid interpolation changes every edge cost by at most twice the uniform
profile error. Since the number of edges is bounded independently of
$$N,$$ this gives the required arbitrarily small loss in (17). A constant
depending on $$T$$ is harmless because $$T$$ is fixed before sending
$$N\to\infty.$$

In particular, if the new forced-chain lemma establishes

$$
c=C(s,u):=\frac{2u-4s+3}{8}+\frac{u-s}{2s}
\qquad(1<s\leq u\leq3/2),
\tag{28}
$$

with the bounded-length and approximate-barrier conditions just specified,
then **no new harmonic-analysis estimate is needed** to conclude raw
pinned absolute continuity whenever $$C(s,u)<s-1.$$ The algebra checks:

$$
C(s,u)<s-1
\quad\Longleftrightarrow\quad
u<\frac{s(12s-7)}{2s+4}.
\tag{29}
$$

This cutoff exceeds $$2s-1$$ precisely in the relevant range

$$
s>\frac{13+\sqrt{41}}{16},
\tag{30}
$$

and reaches $$3/2$$ at $$s=(5+\sqrt{97})/12.$$ The differences and crossing
equations are respectively

$$
\frac{s(12s-7)}{2s+4}-(2s-1)
=\frac{8s^2-13s+4}{2s+4},
\qquad 12s^2-10s-6=0.
\tag{31}
$$

I have independently checked (29)–(31) and the analytic transfer above.
The new combinatorial estimate (28) must be checked independently; it was
not proved in this audit. With that estimate supplied, the analytic
construction has no further newly identified gap. This conclusion remains
a written mathematical argument, not a formal proof certificate.
