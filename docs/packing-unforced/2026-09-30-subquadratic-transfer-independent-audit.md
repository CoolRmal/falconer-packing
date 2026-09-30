# Independent audit of the subquadratic regularity upgrade

Date: 2026-09-30.

Audited claim: the existing strict finite-profile criterion implies that the actual joint pinned distance law has a density in some strong space $$L^p$$ with $$p>1$$. The argument varies the deletion thresholds in the actual transfer, rather than changing the source probability. Files checked: the subquadratic research note and the finite-profile, Fourier-transfer, and selected-cap-embedding manuscript sources.

## A real omission, and its repair

The first draft omitted the pin remainder discarded by finite regularization. Its good function is zero for every threshold parameter. Its contribution to the bad first norm is therefore bounded by

$$
C R^{-\epsilon_{\rm reg}},
$$

independently of that parameter. This term is neither rapidly decreasing to arbitrary order nor automatically bounded by the claimed threshold-dependent tail. Consequently the original advertised raw weak exponent based only on the radial-projection exponent and chain length was not established.

There are two valid repairs. The author first explicitly restored this term and reduced the threshold-tail exponent on a fixed polynomial parameter range. The cleaner repair is to apply the decomposition lemma only on the retained pin region and estimate its complement separately. The latter gives the result below.

## Precise corrected conclusion

Let the existing strict cost inequality leave a positive good-shell decay exponent $$\kappa$$. Write

$$
\gamma=\frac{q-1}{q}>0,\qquad
p_0=\frac{K+2\gamma}{K+\gamma}>1,
$$

where the radial-projection exponent and the common finite chain-length bound have already been fixed. Let the discarded pin mass at frequency $$R$$ be at most $$R^{-\epsilon_{\rm reg}}$$. Then the actual joint distance law belongs to every strong space with exponent

$$
1<p<\min\{p_0,\,1+\epsilon_{\rm reg}/2\}.
\tag{1}
$$

This is a nonempty interval. The conclusion does not assert raw weak membership at the original endpoint $$p_0$$.

Here is a direct verification. Let $$X_R$$ be the union of retained regularization components, let $$F_R$$ be the full signed annular pinned density, and put

$$
F_R^{\rm reg}(y,t)=\mathbf1_{X_R}(y)F_R(y,t),
\qquad
F_R^{\rm rem}=F_R-F_R^{\rm reg}.
$$

For the first function, varying the source angular threshold by a factor $$\Lambda^{1/q}$$ and every pin threshold by a factor $$\Lambda$$ gives

$$
F_R^{\rm reg}=G_{R,\Lambda}+B_{R,\Lambda}^{\rm reg},
$$

$$
\|G_{R,\Lambda}\|_2^2
\le C R^{-\kappa}\Lambda^K,
\qquad
\|B_{R,\Lambda}^{\rm reg}\|_1
\le C R^{-c}\Lambda^{-\gamma}+\operatorname{RapDec}(R).
\tag{2}
$$

All these are joint norms for the fixed measure $$d\nu(y)\,dt$$. The remainder in pin space is absent from (2), since both sides have been restricted to the retained region.

The elementary parameterized decomposition lemma, with a sufficiently large fixed polynomial range of parameters, proves

$$
\|F_R^{\rm reg}\|_{L^{p_0,\infty}}
\le C R^{-\kappa\gamma/(K+2\gamma)}.
\tag{3}
$$

All radial supports lie in one fixed bounded interval. Weak membership at this exponent therefore controls the strong norm at every smaller exponent with a fixed multiplicative constant.

On the discarded region one has the independent bounds

$$
\|F_R^{\rm rem}\|_1\le C R^{-\epsilon_{\rm reg}},
\qquad
\|F_R^{\rm rem}\|_\infty\le C R^2.
$$

The first uses the uniformly bounded first norm of the whole annular multiplier, for each pin. The second uses the annular kernel bound and the bounded radial range. Thus

$$
\|F_R^{\rm rem}\|_p^p
\le\|F_R^{\rm rem}\|_\infty^{p-1}
\|F_R^{\rm rem}\|_1
\le C R^{2(p-1)-\epsilon_{\rm reg}}.
\tag{4}
$$

For every exponent in (1), both (3) and (4) give strictly decaying strong norms of their respective shell pieces. Their norms are summable over the fixed-ratio geometric annuli. Adding the smooth low-frequency term therefore produces a joint function in that strong space. Its convergence in the first norm and the original distributional reconstruction identify it with the actual positive joint pinned distance law. This proves the corrected claim.

## Uniformity in the auxiliary parameter

The uniformity required by (2)--(3) survives the actual packet construction.

1. The pin regularization, the profiles, their bounded-length chains, and the smooth standard source packets are fixed before the thresholds vary. Only subsets of a fixed finite family change. No common good function for all parameter values is assumed or needed by the decomposition lemma.
2. The source-heavy set remains an estimating device. Changing its threshold does not impose a new spatial cutoff or require new derivative estimates.
3. On each component the two bad-pair estimates gain respectively the factors $$\Lambda^{(1-q)/q}$$ and $$\Lambda^{1/q-1}$$. Both equal the same negative power used in (2). The original component-weight and geometric losses remain fixed.
4. The selected-cap embedding costs one pin threshold per edge. Hence at most $$K$$ edges give at most the factor $$\Lambda^K$$. A shorter component chain is harmless because the parameter is at least one.
5. Packet, cube, component, and spectral-label counts are bounded by fixed powers of the frequency. Their derivative and global norm bounds are uniform over all retained subsets. On any fixed polynomial parameter range, the inflation of a localization error is still at most a fixed power of the frequency. Arbitrary-order decay can be chosen after that range is fixed.
6. The full shell obeys $$\|F_R\|_1\le C_T$$ and $$\|F_R\|_\infty\le C_T R^2$$. Thus the optimizing parameter in the decomposition lemma is never needed beyond a fixed power with exponent greater than $$(2+\kappa)/(K+\gamma)$$. A fixed extra margin absorbs multiplicative constants. This range is chosen after the original small parameters, so it causes no circular exponent choice.

In particular, the rapidly decreasing errors can be absorbed into the parameter tail on this finite range. It was specifically the discarded pin term, with its fixed small exponent, that required separate treatment.

## Weak summation and remaining scope

The author's weak-norm summation argument is valid when its exponent is greater than one. Direct integration of a weak distribution bound gives the restricted-set estimate

$$
\int_A|f|\,dm
\le C_p\|f\|_{L^{p,\infty}}m(A)^{1-1/p}.
$$

The supremum of its normalized left side is a norm equivalent to the weak quasinorm, so summable weak bounds can be summed without invoking a false triangle inequality for an arbitrary weak quasinorm. Alternatively, the repaired argument above sums strong norms directly below both endpoints in (1).

The upgrade concerns the strict **finite-profile** measure criterion. It does not automatically apply to parts of the overall distance theorem supplied only by the separate coherent argument. Nor does it lower the dimension threshold: the good-shell frequency factor is merely raised to a positive power, retaining its required strict sign.

After the discarded-remainder correction, I found no further defect in this regularity argument. This audit establishes the stated deduction from the existing analytic transfer; it is not a separate formal verification of every packet estimate used in that transfer.
