# Mathematical fidelity audit of `HardGapAlgebra.lean`

Date: 2026-09-30. This audit compares the statements and explicit multipliers in `formalization/falconer-packing/FalconerPacking/HardGapAlgebra.lean` with the low- and high-side weighted certificates in `output/pdf/packing-unforced-hard-gaps.tex`. It does not rerun Lean; compilation and standard-axiom checks were performed separately. No Lean source was edited in this audit.

## Verdict

The two certificate statements faithfully formalize their corresponding manuscript inequalities. Their hypotheses are sufficient and do not hide an extra geometric assumption. The conclusions are exactly the total of the first two gap drops and the remaining tail bounded by the claimed cost. The third theorem correctly formalizes the strict rational threshold for the single-collapse cost.

These are algebraic certificates. They do not yet formalize the hard-point identity, geometric gap constraints, their derivation for a Lipschitz profile, the one-gap/zero-gap alternatives, matching extremizers, measure regularization, Fourier iteration, or the pinned distance theorem. The module header explicitly preserves this distinction.

## Low-side certificate

Write

$$
s=1+2b,\qquad D=(1-a)s^2,
\qquad N=1+a-4ab+4b^2-2b.
$$

The hypotheses give $0<a<b\le1/2$, hence $D>0$. The transition hypothesis

$$
b(4+2a)\le1+2a
$$

is precisely $b\le b_c(a)$, because $4+2a>0$. The guard definition is exactly the manuscript polynomial $R(a,b)$, and

$$
D-2N=-R(a,b).
$$

Thus the Lean facts `hN` and `hblend` prove the two necessary conditions $0\le\chi=N/D\le1/2$.

The seven geometric multipliers in Lean are, in order,

$$
(1-a)s,\quad (1-2b)s,\quad b(1-a)s,\quad
(2b-a)s,\quad 1+2a-4b-2ab,\quad
\frac{D-N}{2},\quad \frac D2-N.
$$

They are exactly $D$ times the seven manuscript weights, paired with the identical inequalities and identical factors of two in the gap constraints. In particular, the sixth weight applies to

$$
q_2-2p_2+2(u_2-v_2)\le-1,
$$

and the seventh to $p_2\le1$; there is no index or half-factor discrepancy.

The two tail inequalities are multiplied respectively by $D-2N$ and $2N$. Their sum is the manuscript blended tail multiplied by $D$. Clearing the positive denominator yields exactly

$$
(u_1-v_1)+(u_2-v_2)+\mathrm{tail}
\le
\frac{(b-a)(2+a-2b-4ab)}{(1-a)(1+2b)^2}.
$$

No nonnegativity or ordering assumptions on the endpoint variables are silently added. Those would be true in the application, but this certificate follows from the displayed seven inequalities and the two tail inequalities alone. Omitting unnecessary geometric assumptions makes the algebraic statement stronger, not weaker.

## High-side certificate

Write $D_1=(1+2a)(1+2b)>0$. The Lean multipliers are exactly $D_1$ times the manuscript's eight weights, in order:

$$
1+2a,\quad 2b(1+2a),\quad 2b,\quad 4b(1+a),\quad
1+2a-2b,\quad 2b(1+a),\quad
\frac{(6+8a)b-(1+2a)^2}{2},\quad
(2a+4)b-(2a+1).
$$

The additional hypothesis $v_1-u_2\le0$ is exactly the net-increase inequality between successive positive gaps. It is not replaced with an unjustified pointwise monotonicity assumption. The tail is multiplied by $D_1$, as required.

The potentially delicate seventh sign is handled by the exact identity

$$
\begin{aligned}
&\big((6+8a)b-(1+2a)^2\big)(a+2)\\
&\quad=\frac{6+8a}{2}\big(b(4+2a)-(1+2a)\big)
 +(1+a)(1-2a)(1+2a).
\end{aligned}
$$

Both terms on the right are nonnegative under the stated hypotheses. In particular $a<b\le1/2$ supplies $1-2a>0$; no unstated $a\le1/4$ assumption is needed. The eighth sign is precisely the high-side transition condition. The final cancellation and removal of the positive factor $1+2a$ leave the desired conclusion

$$
(u_1-v_1)+(u_2-v_2)+\mathrm{tail}
\le\frac{b-a}{1+2b}.
$$

## Strict threshold

For $a<1/2$ and $b\ge0$, both denominators in the statement are positive, and

$$
\frac{b-a}{1+2b}<a
\quad\Longleftrightarrow\quad
b(1-2a)<2a
\quad\Longleftrightarrow\quad
b<\frac{2a}{1-2a}.
$$

The Lean theorem has exactly these hypotheses and this conclusion. Its domain is slightly broader than the positive dimension parameters, harmlessly so. It makes no claim about the low-side radical threshold or the complete piecewise dimension curve.

## Audit of the four subsequently added statements

The theorem `twoGapCost_sub_singleGapCost` is exactly the manuscript difference formula. Its assumptions make both relevant denominators nonzero and positive. The identity itself is broader than the transition equality and correctly specializes to that equality.

The theorem `twoGapCost_lt_iff` has the correct strict sign after clearing its positive denominator. Expanding the numerator of the two-gap cost minus the lower slope times that denominator gives exactly

$$
(4a^2-8a-2)b^2+(8a^2-a+2)b-3a.
$$

Thus the displayed quadratic criterion is equivalent, not merely one-sided. It does not independently establish the radical root's location or the full parameter region; those remain separate obligations.

The two exact example margins agree with the manuscript fractions:

$$
\frac9{100}-C_2\left(\frac9{100},\frac{181}{1000}\right)
=\frac{1861}{5152900},
$$

$$
\frac3{20}-C_1\left(\frac3{20},\frac25\right)=\frac1{90}.
$$

These are faithful arithmetic identities. Applying the weighted certificates to these examples still requires their transition and guard hypotheses, together with the separate geometric reduction; the example theorem statements do not silently assert those further conclusions.
