# Differences from the arXiv version

The formalization follows `paper/sandpile.tex`, which is arXiv:2609.02829v1
with the corrections below.  The arXiv source will be replaced by the corrected
text.  The unmodified arXiv source is `paper/sandpile-arxiv.tex`, and
`paper/arxiv/` holds its bibliography file and figures, so that either file
compiles as `main.tex` next to them.  Line numbers refer to the corrected file.
Every statement of the paper is unchanged except the minimality clause of
`prop:brownian-os`; the other changes are to definitions, conventions and
proofs.

## 1. Section 2.3, `prop:brownian-os`, line 1090

arXiv:

> is optimal and is dominated by every optimal stopping time.

Corrected:

> is optimal, and for every optimal stopping time $\tau$ it satisfies
> $\tau_h^*\leq\tau$ almost surely.

The optimal time is defined through a right-continuous modification, so it is
determined only up to a null set, and the null set depends on the competitor.
Pathwise domination by every optimal stopping time is false: already for
$h(t,y)=t$, a competitor that equals $\varepsilon$ on a null event and $T$
elsewhere is optimal, and pathwise domination by all such competitors would
force $\tau_h^*=0$ everywhere.

## 2. Section 4.2, proof of `prop:continuum-value-selfsimilar`, line 1993

Added after "the stopping value scales by the same factor.":

> Here $Z$ is the continuous version fixed after
> \eqref{eq:dlt4-linear-gaussian-potential}, which almost surely has
> polynomial growth on $[0,T]\times\R^d$, so
> Proposition~\ref{prop:brownian-os} makes $\mathcal U(T,x)$ a measurable
> functional of the field $Z$ alone. The equality in law of the fields
> therefore gives the equality in law of the values.

The stopping value $\mathcal U_h$ is defined only for a continuous field of
polynomial growth, and the rescaled Brownian motion in the proof is a Brownian
motion from the origin but not the one on the right-hand side.  The passage from
the equality in law of the fields to the equality in law of the values needs
the value to be a measurable functional of the field alone, which is what
`prop:brownian-os` provides once $Z$ is the continuous version.

## 3. Section 4.3.1, the ball fields $\mathcal X_s$, line 2118

arXiv:

> We use continuous modifications of the fields $\mathcal X_s$, which follow
> from the standard $L^2$-translation estimates for Green kernels in balls.

Corrected:

> The fields $\mathcal X_s$ have continuous modifications, which follow from
> the standard $L^2$-translation estimates for Green kernels in balls, and
> throughout $\mathcal X_s$ denotes that version for every $0<s\leq1$.

The crossing statements of Sections 4.3.2 to 4.3.4 are about level sets of the
continuous versions.  For a white-noise family modified on null sets, a ball
field that is not the continuous version can vanish on a whole line, and then
no crossing occurs; the convention fixes the version for every scale, as the
paper does for $Z$ in Section 2.2.

## 4. Section 4.3.2, definition of $H_{\mathcal R}(\ell)$, line 2124

Added after "left-right crossing of $\mathcal R$.":

> This set of samples is not an event a priori, and
> $\P(H_{\mathcal R}(\ell))$ denotes its outer probability.

The existence of a compact connected crossing depends on uncountably many
values of the field, so the set of crossing samples is not measurable on its
face.  Its outer probability lies between the probabilities of genuine events,
chains of polygonal paths through a fixed countable set at the level $\ell$ and
at every lower level, and every estimate of Section 4.3 is a lower bound, which
is the side these events give.

## 5. Section 5.4, proof of `thm:d4-ball-green-crossing`, Step 4, line 3763

arXiv:

> Since a fixed number of square crossings, depending only on $\vartheta$, can
> be glued to form a left-right crossing of $R_r$, a union bound gives
> \eqref{eq:d4ball-gaussian-crossing}.

Corrected:

> To pass to $R_r$, define $\mathcal H_z$ by the same formula for every $z$ in
> the coordinate plane containing $R_r$. Since $h\geq0$ and the variables
> $\xi(y)$ are independent, the FKG inequality shows that this field is
> positively associated, and its law is invariant under the symmetries of
> $\Z^2$. The square bound with $a/4$ in place of $a$, the RSW theorem of
> \citet[Theorem~1]{KohlerSchindlerTassion} applied to the set where
> $\mathcal H\geq-\frac a4\log r$, and monotonicity of crossing values in the
> side lengths give $\P(L_r(\mathcal H)\geq-\frac a4\log r)\geq c_0$ for all
> large $r$, with $c_0>0$ depending only on $\vartheta$. The value
> $L_r(\mathcal H)$ is also $C\sqrt{\log r}$-Lipschitz, so Gaussian
> concentration forces $\E L_r(\mathcal H)\geq-\frac a2\log r$, and a second
> application of Gaussian concentration gives
> \eqref{eq:d4ball-gaussian-crossing}.

Prescribed nearest-neighbor square crossings do not glue to a crossing of a
long rectangle: a $\ast$-connected low diagonal of slope one blocks every
left-right path of the rectangle, while each of a fixed number of prescribed
squares still has both high crossings once the rectangle is long enough.  The
corrected argument obtains a crossing probability bounded below at a fixed
level from the RSW theorem the paper already uses in Section 4.3, and turns it
into the polynomial tail by Gaussian concentration of the crossing value.

## 6. Section 5.4, proof of `thm:d4-ball-green-crossing`, Step 5, lines 3828-3871

arXiv:

> Replace the variables $\zeta(y)$ in $\Psi$ one at a time by the Gaussians
> $\xi(y)$. The first two Taylor terms cancel at each replacement, and
> \eqref{eq:d4ball-phi-third} gives

followed by the display bounding $|\E\Phi(H)-\E\Phi(\mathcal H)|$.

Corrected: the replacement is made through an interpolation.  For
$t\in[0,1]$ the field $x^t$ has independent coordinates, $x^t_y=\xi(y)$ with
probability $t$ and $x^t_y=\zeta(y)$ otherwise, and the derivative of
$\E\Psi(x^t)$ in $t$ is a sum over $y$ of single-coordinate replacements taken
under one common law.  The third derivatives are bounded by nonnegative
functions $J_{z_1z_2z_3}$ with total mass $C\eta^{-3}(\log r)^3$ at every field
and with $J_{z_1z_2z_3}(F_1)\leq e^{\lambda\|F_1-F\|_\infty}J_{z_1z_2z_3}(F)$,
$\lambda=C\beta\log r$, which the proof of `lem:d4-soft-bottleneck` gives
because the soft maximum weights change by at most $e^{2\beta\delta}$ under
perturbations of size $\delta$.  The exponential moment bound controls
$\E|x|^3e^{\lambda\|h\|_\infty|x|}$ and gives a constant $M$ with
$\P(|x^t_y|\leq M)\geq1/2$; on that event the third-derivative envelope at the
field with coordinate $y$ set to zero is at most $C$ times its conditional
expectation at the field itself.  The display then starts with
$|\E\Phi(H)-\E\Phi(\mathcal H)|\leq C\sup_{t}\E\sum_yJ_y(F[x^t])$ and continues
as before, and "the second inequality is H\"older's inequality" becomes "the
third inequality".  The error term $C\eta^{-3}(\log r)^3\lfloor r^\alpha\rfloor^{-2}$
and the level shift in \eqref{eq:d4ball-lindeberg} are unchanged.

In an ordered one-at-a-time replacement the third derivatives for different
coordinates are evaluated at different hybrid fields, so the pointwise bound
\eqref{eq:d4ball-phi-third}, which sums the derivatives at one field, does not
bound the sum of the Taylor remainders.  The interpolation puts every
coordinate's remainder under one law, where that bound applies.

## 7. Section 6.3, proof of `thm:dgt4-many-limits`, Step 3, line 6352

arXiv:

> Lemmas~\ref{lem:dgt4-path-survival} and
> \ref{lem:dgt4-linearization-from-survival} give

Corrected:

> Lemmas~\ref{lem:dgt4-path-survival} and
> \ref{lem:dgt4-linearization-from-survival} apply along $R=R_{k_\ell}$: their
> proofs use the hypotheses only at the scales at which the conclusions are
> asserted, so hypotheses along a sequence $R_k\to\infty$ give the conclusions
> along $R_k$. They give

The two lemmas are stated as $R\to\infty$ through all large real $R$, while the
scenery constructed in Step 1 satisfies their hypotheses at a fixed $\kappa$
only along the extracted subsequence $R_{k_\ell}$.  Their proofs never use that
$R$ ranges over all reals, so they give the conclusions along that
subsequence, which is what Step 3 needs.

## 8. Section 5.4, proof of `lem:d4-soft-bottleneck`, line 3539

Added at the end of the proof:

> The same construction also gives, for each ordered triple
> $z_1,z_2,z_3\in Q$, a nonnegative $J_{z_1z_2z_3}\geq
> |\partial_{z_1}\partial_{z_2}\partial_{z_3}L_{Q,\beta}|$ with
> $\sum_{z_1,z_2,z_3\in Q}J_{z_1z_2z_3}(F)\leq C\beta^2(\log N)^2$ that is
> multiplicatively stable: composing the $O(\log N)$ layers, each of which
> changes every softmax weight by at most the factor $e^{2\beta\delta}$ under
> a perturbation of $F$ of size $\delta$, gives
> $J_{z_1z_2z_3}(F_1)\leq e^{C\beta(\log N)\|F_1-F\|_\infty}J_{z_1z_2z_3}(F)$
> for every $F,F_1$.

Item 6 above already attributes exactly this multiplicative stability to "the
proof of `lem:d4-soft-bottleneck`," but the lemma's proof never stated it.
The sentence above supplies it, matching
`Sandpile/Support/PositiveJet.lean`, where the same recursive construction's
derivative envelopes are `ExpStable`: a nonnegative function whose value at
one field is at most $e^{K\delta}$ times its value at a field $\delta$ away
in sup norm, because every softmax weight obeys this bound
(`LatticeProb.softWeight_stability`) and sums and products of `ExpStable`
functions are again `ExpStable` with constants added (`ExpStable.sum`,
`.mul`). The lemma's statement, and its frozen Lean formalization
`Sandpile.Frozen.d4_soft_bottleneck`, are unchanged; the addition is to the
proof only. The Step 5 sentence at line 3840 now cites this addition instead
of asserting the stability without a citation.

## 9. Section 3.2, proof of `lem:brownian-ball-localization`, line 1660

arXiv states the lemma after the sentence "The same argument extends to the
Brownian motion analogue of the odometer" and gives no proof.  Added after the
lemma:

> Fix $u\in K$ and a stopping time $\tau\leq T$, and write
> $\sigma=\tau_{u,A}$. The payoffs of $\tau$ and of $\tau\wedge\sigma$ agree
> off the event $\{\sigma<\tau\}$. On this event, the strong Markov property
> of Brownian motion at $\sigma$ bounds the conditional reward after $\sigma$
> by $\mathcal U_Z(T-\sigma,B_\sigma)$, the value of the restarted motion for
> the remaining horizon, and $|B_\sigma-u|=A$. Almost surely $Z$ grows at most
> polynomially on $[0,T]\times\R^d$, and the running maximum of Brownian
> motion on $[0,T]$ has moments of all orders, so every reward in this
> argument is integrable.
>
> The value increases with the horizon: $\mathcal U_Z(s,z)\leq\mathcal
> U_Z(T,z)$ for $0\leq s\leq T$. Indeed, the increment
> $V(a,y)=Z(a+T-s,y)-Z(a,y)$ solves the heat equation, because the
> time-independent white noise cancels, so $r\mapsto V(s-r,B_r)$ is a
> martingale on $[0,s]$ and $\mathbf E_z V(s-\tau,B_\tau)=V(s,z)$ for every
> stopping time $\tau\leq s$. Hence
> $Z(T,z)-\mathbf E_z Z(T-\tau,B_\tau)=Z(s,z)-\mathbf E_z Z(s-\tau,B_\tau)$,
> so every payoff available at horizon $s$ in
> \eqref{eq:continuum-membrane-stopping-value} is available at horizon $T$.
>
> Taking the supremum over $\tau$ gives
> $\mathcal U_Z(T,u)-\mathcal U_{Z,A}(T,u)\leq\P(\tau_{u,A}<T)\sup_z
> \mathcal U_Z(T,z)$, the supremum over the points $z$ within distance $A$ of
> $K$. The Gaussian tail $\P(\tau_{u,A}<T)\leq Ce^{-cA^2/T}$ of the exit time
> completes the proof.

The lattice argument of `lem:localization-killing` does not transfer verbatim.
After the exit the restarted motion has only the remaining horizon $T-\sigma$,
and the lattice proof bounds its reward by the value at the full horizon, which
there is immediate because a stopping time bounded by $T-\sigma$ is bounded by
$T$.  For the Brownian value $\mathcal U_Z(T,x)=Z(T,x)+\sup_\tau\mathbf
E_x[-Z(T-\tau,B_\tau)]$ the horizon also enters the field, so monotonicity in the
horizon is a property of $Z$ and needs the argument of the second paragraph;
for a general continuous field it is false.  The proof also makes explicit the
integrability that the strong Markov step needs.  The lemma's statement is
unchanged.  In the formalization the strong Markov step is the cited input
`Sandpile.External.BrownianExitStep`, stated with an integrable envelope and
with the value at the remaining horizon (see `ledger/decisions.md`, D-001), and
the monotonicity in the horizon is the repository node
`Sandpile.Frozen.brownian_value_mono_horizon`.
