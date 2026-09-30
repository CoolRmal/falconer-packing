# Weighted decoupling does not improve the proposed terminal cost

30 September 2026. This is a comparison of the exponents in a specified
decoupling construction. It does not exclude other uses of weighted decoupling
or prove a necessary dimension condition for distance sets.

The analytic input is Theorem 1.1(b) of
[Du, Ou, Ren and Zhang, *Weighted refined decoupling estimates and application
to Falconer distance set problem*](https://arxiv.org/html/2309.04501v1).
In the planar case its critical exponent is six. The following calculation
uses its weighted gain at the natural packet scale, rather than discarding
that gain.

## The weighted packet calculation

Normalize a spatial parent to unit size, let its frequency be
$$r=2^L,$$ and write $$\rho=r^{-1/2}.$$
Let the smoothed conditional pin probability have density $$w\le A.$$
Suppose every square of side $$\rho$$ has pin mass at most $$v$$, with
the usual fixed enlargements understood. Retained packets have pin mass
at most $$H\rho$$ in their enlarged tubes.

In the large spatial coordinates $$X=rx$$, the bounded weight is
$$W(X)=w(X/r)/A.$$
Its mass on a square of side $$r^{1/2}$$ is at most
$$r^2v/A.$$
Set
$$\alpha=\frac{2\log(r^2v/A)}{\log r},\qquad Q=rv/A.$$
The hypotheses of the weighted theorem use this value of $$\alpha$$;
its requirement $$\alpha\le2$$ is precisely $$Q\le1$$. Arbitrarily
small power losses handle profile errors and fixed enlargements.

Fix $$2\le p\le6.$$
For one packet-amplitude class, write $$K$$ for its number of packets,
and let $$Y$$ be a union of natural squares meeting at most a dyadic
multiplicity $$M$$ of these packets. The weighted theorem, followed by
Hölder with respect to the pin measure, gives
$$
\int_Y |F|^2w
\lesssim_\epsilon r^\epsilon
 A^{2/p}Q^{2/p-1/3}
 \left(\frac{M\,w(Y)}K\right)^{1-2/p}
 \sum_T\|F_T\|_p^2.
$$
Indeed the squared gain in the weighted theorem is
$$r^{(\alpha-2)(1/p-1/6)}=Q^{2/p-1/3}.$$
Incidence counting gives
$$M w(Y)\lesssim K H\rho.$$
Bernstein for a canonical packet, whose Fourier rectangle has area
$$O(\rho^{-1}),$$ gives
$$\|F_T\|_p^2\lesssim \rho^{-(1-2/p)}\|F_T\|_2^2.$$
The factors of $$\rho$$ cancel. Summing the logarithmically many
classes therefore gives the multiplier
$$
A^{2/p}Q^{2/p-1/3}H^{1-2/p}
$$
in front of the local parent square function, with an arbitrary small
positive frequency loss. This calculation assumes the packet-compatible
selection and radius-independent reconstruction in the separate local
terminal-transfer note. It asserts no transfer for arbitrary spatially
varying Fourier selectors.

## Exact profile comparison

Let $$g:[0,N]\to\mathbb R$$ be 1-Lipschitz. Fix $$0\le m<N$$ and put
$$
L=N-m,\quad n=(N+m)/2,\quad
c=g(m)-\min_{[m,n]}g,
$$
$$
I=L+g(m)-g(N),\qquad J=-L/2+g(N)-g(n).
$$
Regular cube masses give the leading exponents
$$A=2^I,\qquad v=2^{-L/2-g(n)+g(m)},\qquad Q=2^J,\qquad H=2^c.$$
Here $$J\le0$$ follows from the Lipschitz bound between $$n$$ and
$$N$$, so the weighted theorem applies. As throughout the profile
argument, these are leading exponents; the regularization errors and
small positive losses must be restored before an analytic application.

The corresponding terminal cost is
$$
T_p(g;m)=\frac2p I+\left(\frac2p-\frac13\right)J
       +\left(1-\frac2p\right)c.
$$
At the critical exponent,
$$
T_6(g;m)=\frac{I+2c}{3}.
$$
For every $$2\le p\le6$$ the exact difference is
$$
\begin{aligned}
T_p(g;m)-T_6(g;m)
 &=\left(\frac2p-\frac13\right)(I+J-c)\\
 &=\left(\frac2p-\frac13\right)
   \left(\frac L2-g(n)+\min_{[m,n]}g\right)\ge0.
\end{aligned}
$$
To prove the last inequality, choose a minimum point $$z\in[m,n].$$
Lipschitz continuity implies
$$g(n)-g(z)\le n-z\le n-m=L/2.$$
Both factors in the displayed difference are nonnegative. This proves
that optimizing the entire weighted family over $$p\in[2,6]$$ gives
exactly the exponent-six cost. No numerical optimization is used.

This is an exact statement about this one terminal step. The separate
[profile comparison](2026-09-30-local-giow-profile-redundancy.md) now proves
that optimizing this terminal step together with a coarse chain gives
exactly the original limiting chain cost. This weighted family therefore
does not lower the dimensional cutoff.
