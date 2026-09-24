/-
External input: the finite-time variance scale, the membrane correlation bound,
and the dimension-four window and tail bounds collected in
`ssec:green-estimates` of `sandpile.tex`.  The paper does not prove them; it
records at `sandpile.tex:1117-1122` that

  "The random-walk estimates in this subsection are standard consequences of
   the local central limit theorem, its gradient form, and the Green-function
   asymptotic; see \citet[Propositions~2.4.1, 2.4.4, and~2.4.6, and
   Theorem~4.3.1]{LawlerLimic}, together with Hoeffding's inequality for the
   off-diagonal Gaussian factor."

The four displays transcribed here are, in the paper's own words.  First
`eq:Qt-table` (`sandpile.tex:1179-1195`):

  "The field $V_t$ from \eqref{eq:membrane-recursion} satisfies
   \[ \Var(V_t(0)) = \Var(\zeta(0))\sum_{y\in\Z^d}g_t(0,y)^2\, . \]
   For $t\geq2$,
   \[ \Var(V_t(0))\asymp
      \begin{cases} t^{3/2}, & d=1\, ,\\ t, & d=2\, ,\\ t^{1/2}, & d=3\, ,\\
      \log t, & d=4\, ,\\ 1, & d\geq5\, .\end{cases} \]"

Then `eq:corr-bound` (`sandpile.tex:1197-1217`):

  "For $1\leq m\leq n$,
   \[ \frac{\Cov(V_m(0),V_n(0))}{\Var(\zeta(0))}
      = \sum_{x\in\Z^d}g_m(0,x)g_n(0,x)
      = \sum_{a<m}\sum_{b<n}p_{a+b}(0,0)\, . \]
   Together with \eqref{eq:Qt-table}, we use the following correlation bound:
   \[ \frac{\Cov(V_m(0),V_n(0))}{\sqrt{\Var(V_m(0))\Var(V_n(0))}}
      \leq \begin{cases}
        C(\tfrac mn)^{1/4},& d=1\, ,\\
        C(1{+}\log\tfrac nm)\sqrt{\tfrac mn}\, , & d=2\, ,\\
        C(\tfrac mn)^{1/4},& d=3\, ,\\
        C\sqrt{(1+\log m)/(1+\log n)},& d=4\, .\end{cases} \]"

Then `eq:d4-window-l2`, `eq:d4-window-linfty` and `eq:d4-full-window-bounds`
(`sandpile.tex:1220-1240`):

  "For all integers $m$ and $n$ with $1\leq m<n$ and all $x\in\Z^4$,
   \[ \sum_{z\in\Z^4}\left(\sum_{k=m}^{n-1}p_k(x,z)\right)^2
      \leq C\left(1+\log\frac{n+2}{m+2}\right)\, ,\qquad
      \sup_{z\in\Z^4}\sum_{k=m}^{n-1}p_k(x,z)\leq\frac{C}{m}\, . \]
   For every integer $n\geq2$ and every $x\in\Z^4$,
   \[ \sum_{z\in\Z^4}\left(\sum_{k=0}^{n-1}p_k(x,z)\right)^2
      \leq C\log(n+2)\, ,\qquad
      \sup_{z\in\Z^4}\sum_{k=0}^{n-1}p_k(x,z)\leq C\, . \]"

These results are assumed here, not proved.

Modelling.  `p_k` is `Sandpile.heatKernel d k` and `g_t` is
`Sandpile.greenTime d t`; the full window `\sum_{k=0}^{n-1}p_k(x,z)` is
therefore `Sandpile.greenTime 4 n x z` by definition, and the partial window
`\sum_{k=m}^{n-1}p_k(x,z)` is `windowKernel m n x z`, a finite sum over
`Finset.Ico m n`.

The two displays about the membrane field are transcribed in their
scenery-free form.  The paper's `\Var(V_t(0))` and `\Cov(V_m(0),V_n(0))` are
converted by the paper's own identities
`\Var(V_t(0)) = \Var(\zeta(0))\sum_y g_t(0,y)^2` and
`\Cov(V_m(0),V_n(0)) = \Var(\zeta(0))\sum_x g_m(0,x)g_n(0,x)`, stated at
`sandpile.tex:1179-1184` and `sandpile.tex:1197-1204`.  Those two identities are
the paper's own lines and are NOT part of what is assumed here: what is frozen
below is the two-sided bound on `\sum_y g_t(0,y)^2` and the upper bound on
`\sum_x g_m(0,x)g_n(0,x)`, from which the paper's `V` forms follow by dividing
by the positive constant `\Var(\zeta(0))`, which cancels from the normalized
quotient of `eq:corr-bound` and rescales both sides of `eq:Qt-table`.

`f \asymp g` is two constants and a threshold: `eq:Qt-table` is written as
`c\,\rho_d(t) \leq \sum_y g_t(0,y)^2 \leq C\,\rho_d(t)` for `t \geq 2`, with
`\rho_d(t)` the `d`-dependent rate `varianceRate` defined above the frozen
block.  The rate is an `if` chain on `d` rather than five separate implications,
so that the two constants are quantified once; its final branch is the paper's
`d\geq5` case, and it is reached only for `d \geq 5` because the statement binds
`1 \leq d`.  The rate of `eq:corr-bound` is likewise the `if` chain
`corrRate`; its final branch is the paper's common `d\in\{1,3\}` case and is
reached only for those two dimensions because the statement binds `1 \leq d` and
`d \leq 4`, which is the range of the paper's four cases.

Each display group carries its own constants, existentially quantified after
the dimension and before the times, since the paper's convention
(`sandpile.tex:781-782`) is that `c` and `C` may change from line to line and
that `C = C(d)` records dependence on `d` alone.  The two window displays and
the two full-window displays share a single `C`, as the paper writes them; a
shared constant is equivalent to one per display, since each is a bound of the
form `\cdot \leq C f` with `f \geq 0` and one may take the largest `C`.

Junk values.  `eq:corr-bound` is a normalized quotient in the paper.  Under
`1 \leq m` and `1 \leq d` both of `\sum_y g_m(0,y)^2` and `\sum_y g_n(0,y)^2`
are positive, so the quotient is well defined; nonetheless the bound is
transcribed in the cross-multiplied form
`\sum_x g_m(0,x)g_n(0,x) \leq C\,\rho\,\sqrt{\sum_x g_m(0,x)^2}\,
\sqrt{\sum_x g_n(0,x)^2}`, in which no division occurs at all, so no value of
`x/0 = 0` can arise and the statement is the paper's for every admissible pair.
Every sum over sites here is a `tsum`, and none of them can reach the junk value
of a divergent family: `g_t(x,\cdot)` is supported in the box of radius `t`
about `x` by `Sandpile.greenTime_support`, and each `p_k(x,\cdot)` is supported
in the box of radius `k` by `Sandpile.heatKernel_eq_zero_of_lt`, so
`windowKernel m n x \cdot` is supported in the box of radius `n`; every summand
is finitely supported and therefore summable, and no `Summable` conjunct is
needed.  Both suprema over `z` are written as universally quantified bounds
subject to no constraint on `z`, never as an `sSup`, so no empty or unbounded
supremum can arise; the two readings are the same statement.  The thresholds
`2 \leq t`, `1 \leq m` and `2 \leq n` are the paper's, and they keep `\log t`
and `\log(n+2)` positive, `C/m` away from a zero denominator, and the real
powers `t^{3/2}`, `t^{1/2}` and `(m/n)^{1/4}` away from a zero base; the
arguments `(n+2)/(m+2)`, `n/m` and `(1+\log m)/(1+\log n)` of the remaining
logarithms and quotients have denominators at least one.
-/
import Sandpile.Support.Kernel

namespace Sandpile.External.Variance

/-- The `d`-dependent rate on the right of `eq:Qt-table`
(`sandpile.tex:1186-1195`): `t^{3/2}` in dimension one, `t` in dimension two,
`t^{1/2}` in dimension three, `\log t` in dimension four, and `1` in dimensions
five and above.  The final branch is the paper's `d\geq5` case; the frozen
statement binds `1 \leq d`, so the branch is reached only there. -/
noncomputable def varianceRate (d : ℕ) (t : ℕ) : ℝ :=
  if d = 1 then (t : ℝ) ^ ((3 : ℝ) / 2)
  else if d = 2 then (t : ℝ)
  else if d = 3 then (t : ℝ) ^ ((1 : ℝ) / 2)
  else if d = 4 then Real.log (t : ℝ)
  else 1

/-- The `d`-dependent rate on the right of `eq:corr-bound`
(`sandpile.tex:1206-1217`), with the constant `C` stripped off:
`(1+\log(n/m))\sqrt{m/n}` in dimension two, `\sqrt{(1+\log m)/(1+\log n)}` in
dimension four, and `(m/n)^{1/4}` in dimensions one and three, which the paper
gives the same case.  The final branch is that common case; the frozen
statement binds `1 \leq d` and `d \leq 4`, so it is reached only for
`d\in\{1,3\}`. -/
noncomputable def corrRate (d : ℕ) (m n : ℕ) : ℝ :=
  if d = 2 then (1 + Real.log ((n : ℝ) / (m : ℝ))) * Real.sqrt ((m : ℝ) / (n : ℝ))
  else if d = 4 then Real.sqrt ((1 + Real.log (m : ℝ)) / (1 + Real.log (n : ℝ)))
  else ((m : ℝ) / (n : ℝ)) ^ ((1 : ℝ) / 4)

/-- The time window `\sum_{k=m}^{n-1}p_k(x,z)` of `eq:d4-window-l2` and
`eq:d4-window-linfty` (`sandpile.tex:1222-1232`), a finite sum over the steps
`k` with `m \leq k < n`. -/
noncomputable def windowKernel (m n : ℕ) (x z : Sandpile.Site 4) : ℝ :=
  ∑ k ∈ Finset.Ico m n, Sandpile.heatKernel 4 k x z

end Sandpile.External.Variance

-- FROZEN-STATEMENT-BEGIN
/-- The finite-time variance scale `eq:Qt-table`, the membrane correlation bound
`eq:corr-bound`, and the dimension-four window and tail bounds
`eq:d4-window-l2`, `eq:d4-window-linfty` and `eq:d4-full-window-bounds` of
`ssec:green-estimates`, all in their scenery-free Green-kernel form.  Assumed,
not proved. -/
def Sandpile.External.VarianceScale : Prop :=
  (∀ d : ℕ, 1 ≤ d →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ t : ℕ, 2 ≤ t →
          c * Sandpile.External.Variance.varianceRate d t ≤
              ∑' y : Sandpile.Site d, Sandpile.greenTime d t 0 y ^ 2 ∧
            (∑' y : Sandpile.Site d, Sandpile.greenTime d t 0 y ^ 2) ≤
              C * Sandpile.External.Variance.varianceRate d t) ∧
  (∀ d : ℕ, 1 ≤ d → d ≤ 4 →
      ∃ C : ℝ, 0 < C ∧
        ∀ m n : ℕ, 1 ≤ m → m ≤ n →
          (∑' x : Sandpile.Site d,
              Sandpile.greenTime d m 0 x * Sandpile.greenTime d n 0 x) ≤
            C * Sandpile.External.Variance.corrRate d m n *
              Real.sqrt (∑' x : Sandpile.Site d, Sandpile.greenTime d m 0 x ^ 2) *
              Real.sqrt (∑' x : Sandpile.Site d, Sandpile.greenTime d n 0 x ^ 2)) ∧
  (∃ C : ℝ, 0 < C ∧
      (∀ m n : ℕ, 1 ≤ m → m < n → ∀ x : Sandpile.Site 4,
          (∑' z : Sandpile.Site 4,
              Sandpile.External.Variance.windowKernel m n x z ^ 2) ≤
            C * (1 + Real.log (((n : ℝ) + 2) / ((m : ℝ) + 2))) ∧
          ∀ z : Sandpile.Site 4,
            Sandpile.External.Variance.windowKernel m n x z ≤ C / (m : ℝ)) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ x : Sandpile.Site 4,
          (∑' z : Sandpile.Site 4, Sandpile.greenTime 4 n x z ^ 2) ≤
            C * Real.log ((n : ℝ) + 2) ∧
          ∀ z : Sandpile.Site 4, Sandpile.greenTime 4 n x z ≤ C))
-- FROZEN-STATEMENT-END
