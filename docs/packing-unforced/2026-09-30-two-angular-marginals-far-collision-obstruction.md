# Two bounded angular marginals do not improve a far-pair strip estimate

30 September 2026. This is a sharp obstruction to a specified pointwise step in the positive angular-selection route. Both measures in the example are fixed and Ahlfors regular, and the same angular selection is used at every scale. It is not a counterexample to positive-length distances, nor to a source-pair-averaged collision estimate.

## 1. Precise statement

For every exponent

$$1<s<2,$$

there are separated compactly supported probability measures mu and nu with

$$
\dim_H\operatorname{supp}\mu=\dim_P\operatorname{supp}\mu
=\dim_H\operatorname{supp}\nu=\dim_P\operatorname{supp}\nu=s,
$$

both s-Ahlfors regular, having the following properties.

1. For every x in the source support, the radial projection of nu from x has density rho_x bounded by one common finite constant A_0.
2. Consequently the fixed angular selection

$$
a_A(x,y)=\mathbf1_{\{\rho_x((y-x)/|y-x|)\le A\}},
\qquad A\ge A_0,
$$

retains all original source–pin pairs (up to the irrelevant choice of density representative).
3. There are two source points x_+,x_- at distance two such that

$$
\nu\left\{y:\left||x_+-y|-|x_--y|\right|\le\varepsilon\right\}
\asymp\varepsilon^{s-1}
\qquad(0<\varepsilon<\varepsilon_0).
\tag{1}
$$

In particular, imposing both angular selection factors does not improve the ordinary s-Frostman strip power even for a uniformly separated source pair. This remains a failure of any uniform faster-power estimate asserted for mu times mu almost every pair: for each small epsilon there is a set of such far pairs of positive product mass on which the lower bound in (1) holds.

## 2. Construction and all regularity assertions

Put gamma=s-1 in (0,1). Let kappa be a gamma-Ahlfors regular probability on a Cantor subset of [0,1/10] containing zero. Let lambda be an (s/2)-Ahlfors regular probability on a Cantor subset of [0,1/10] containing zero. These can be the standard two-map self-similar Cantor measures with contraction ratios 2^{-1/gamma} and 2^{-2/s}, respectively, followed by fixed dilations.

Set

$$
x_+=(1,0),\qquad x_-=(-1,0),
$$

and let mu be the equal mixture of the translates of lambda times lambda by these two points. Set

$$
\nu=\kappa\times\mathcal L^1|_{[2,3]}.
\tag{2}
$$

Products of the stated regular measures are s-Ahlfors regular in the plane: balls contain and are contained in product intervals of comparable radius, giving both bounds. The two source components are separated by a fixed positive distance, so their equal mixture is again s-Ahlfors regular, with adjusted constants. Regularity gives both Hausdorff and packing dimension s. All these measures are independent of epsilon.

Source horizontal coordinates lie in [1,1.1] or [-1,-0.9], and source vertical coordinates lie in [0,0.1]. Pin horizontal coordinates lie in [0,0.1], while pin heights lie in [2,3]. Hence source and pins have fixed positive separation. In particular every source–pin distance lies between two positive fixed constants.

## 3. Bounded angular densities on the entire source support

Fix a source x in either source patch and a horizontal pin coordinate t in [0,0.1]. As the vertical pin coordinate v runs from 2 to 3, the angle

$$
\theta_{x,t}(v)=\arg((t,v)-x)
$$

is injective on its image, and

$$
\left|\frac{d}{dv}\theta_{x,t}(v)\right|
=\frac{|t-x_1|}{(t-x_1)^2+(v-x_2)^2}.
\tag{3}
$$

The right side is bounded above and below by positive constants, uniformly over x,t,v in the specified compact ranges. The pushforward of Lebesgue measure on [2,3] therefore has an angular density bounded by a common constant A_0. Integrating these conditional densities against kappa(t) gives a jointly measurable density rho_x with the same upper bound. This holds for every source point, not just the two distinguished centers.

Choose these bounded representatives in the fixed angular-selection definition. For A at least A_0, both factors a_A(x,y) and a_A(x',y) are identically one on the supports. Thus the example satisfies stronger angular information than any finite averaged Lq assumption, at every fixed exponent q.

## 4. Exact far-pair collision concentration

For y=(t,v) in the pin support, the squared-distance identity gives

$$
\left||x_+-y|-|x_--y|\right|
=\frac{4|t|}{|x_+-y|+|x_--y|}.
\tag{4}
$$

The denominator is between two positive fixed constants. The collision event in (1) therefore contains all pins with |t| at most c epsilon and is contained among pins with |t| at most C epsilon. The lower and upper Ahlfors bounds for kappa at zero prove (1).

The conclusion is not restricted to one null source pair at each scale. Choose a sufficiently small fixed c_0. For

$$
x\in\operatorname{supp}\mu\cap B(x_+,c_0\varepsilon),\qquad
x'\in\operatorname{supp}\mu\cap B(x_-,c_0\varepsilon),
\tag{5}
$$

the distance difference changes from (4) by at most 2c_0 epsilon, uniformly in y, since distance is 1-Lipschitz in its source point. Pins with |t| at most a sufficiently small fixed multiple of epsilon therefore still satisfy the epsilon collision condition. The pin mass is at least c epsilon^{s-1}, uniformly over the pair set (5). Its source product mass is at least c epsilon^{2s} by lower regularity. All these source separations exceed one for small epsilon, so they lie in every far region |x-x'|>epsilon^alpha with alpha>0.

As a result, no estimate of the form

$$
\int a_A(x,y)a_A(x',y)
\mathbf1_{\{||x-y|-|x'-y||\le\varepsilon\}}\,d\nu(y)
\le C\varepsilon^\theta,
\qquad \theta>s-1,
\tag{6}
$$

can hold uniformly in epsilon for mu times mu almost every far source pair, with C depending only on the fixed separation, angular bound, Frostman constants and source dimensions. The failure occurs on a positive-product-mass set at every sufficiently small resolution.

The two rays in the distinguished pair are uniformly transverse. Their angle satisfies

$$
|\sin\angle(y-x_+,y-x_-)|
=\frac{2v}{|y-x_+||y-x_-|}\ge c>0.
$$

Nevertheless their joint angular law need not have a two-dimensional density. In fact the map

$$
y\longmapsto\bigl(\arg(y-x_+),\arg(y-x_-)\bigr)
$$

has Jacobian determinant of magnitude

$$
\frac{2v}{|y-x_+|^2|y-x_-|^2},
$$

bounded above and below on the pin rectangle. It is locally bi-Lipschitz there. Its pushforward of nu is supported on a set of dimension s<2, so is singular with respect to two-dimensional angular Lebesgue measure, although both one-dimensional angular marginals are bounded. Thus pairwise transversality does not justify replacing the two separate angular bounds by a bounded joint angular density.

## 5. What this rules out, and what it leaves open

For a pair at separation u, the standard pin Frostman estimate for its bisector strip is

$$
C_\nu(\varepsilon/u)^{s-1}.
$$

A bounded selected angular marginal gives the separate bound

$$
C A(u+\varepsilon/u).
$$

The construction proves that for u comparable to one, imposing the second selected angular factor cannot improve the first power on the basis of these marginals alone. The same obstruction persists with source packing dimension equal to source Hausdorff dimension. Thus the hoped-for missing radial factor cannot be obtained by applying the two angular inequalities to each source pair separately.

Integrating the ordinary strip bound alone gives only

$$
\mathcal C_{\varepsilon,>r}^A
\lesssim \varepsilon^{s-2}
\iint_{|x-x'|>r}|x-x'|^{1-s}\,d\mu(x)d\mu(x'),
$$

which is not a uniform bound below dimension two. This is a limitation of that estimate, not a lower bound for the full collision integral.

Crucially, the exceptional pair neighborhoods (5) shrink with epsilon. Their displayed lower bound contributes only a decaying quantity of order epsilon^{3s-2} to the normalized full integral. Therefore the example does **not** disprove a far-collision estimate after averaging source pairs, and does not contradict the dimension theorem already proved for equal dimensions. A successful improvement must exploit the distribution of source-pair bisectors, or another genuinely joint geometric quantity, rather than only the two selected angular marginals at an individual pair.
