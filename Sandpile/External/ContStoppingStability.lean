/-
External input: the stability of optimal-stopping values under uniform
convergence of bounded rewards, together with the invariance principle for the
stopped walk, in the form cited at `sandpile.tex:1900-1907`.  The paper proves
Theorem 1.3(i)(b) and, at the heart of that proof, writes:

  "Fix a continuous cutoff $\chi_A:\R^d\to[0,1]$ equal to one for $|y|\leq A$
   and zero for $|y|\geq2A$.  For fixed $A$, as $R\to\infty$ the
   optimal-stopping value for the first of the two bounded rewards
     $(s,y)\mapsto-\chi_A(y)Z_R^{\rm lin}((t_R/R^2-s)_+,y)$   and
     $(s,y)\mapsto-\chi_A(y)Z(T-s,y)$
   converges to the value for the second, uniformly for
   $(T,x)\in[T_-,T_+]\times K$.  This is the standard stability of
   optimal-stopping values under uniform convergence of bounded rewards and the
   invariance principle for the stopped walk
   \citep[Theorem~3 and Corollary~4]{CoquetToldo}."

The paper announces the same input in the introduction, at
`sandpile.tex:649`: "Below, when proving convergence of the discrete stopping
values to the Brownian value in dimensions one, two, and three, we use the
stability results of \citet*[Theorem~3 and Corollary~4]{CoquetToldo}."

The cited source is Coquet and Toldo, *Convergence of values in optimal
stopping and convergence of optimal stopping times*, Electronic Journal of
Probability 12 (2007), 207-228, Theorem 3 and Corollary 4.  Theorem 3 there
states that if a sequence of processes converges in law for the Skorokhod
topology and the associated reward families are uniformly integrable, then the
values of the finite-horizon optimal-stopping problems converge; Corollary 4
specializes it to rewards of the form `G(t, Z_t)` with `G` bounded continuous
and `Z^n \Rightarrow Z`, which is the shape the paper uses: the processes are
the rescaled simple random walks, whose invariance principle supplies the
convergence in law, and the rewards are the two displayed bounded functions of
time and position.

This result is assumed here, not proved.

Modelling.  The conclusion is the paper's, stated with the supremum over
`(T,x)\in[T_-,T_+]\times K` written in `\varepsilon`-`R_0` form, exactly as
`Sandpile.External.LocalCLT` writes the local central limit theorem: for every
accuracy there is a threshold beyond which every admissible pair obeys the
bound.  Writing the supremum itself would introduce the junk value
`sSup \emptyset = 0` and the junk value of an unbounded supremum.

The reward at scale `R` is `G' R`, a function of a time in `[0,T_+]` and a
point of `\R^d`; the limit reward is `G`.  Boundedness of both families is the
source's hypothesis and is stated as a single bound valid for every scale, and
the convergence is uniform on `[0,T_+]\times\R^d`, which is what the paper's
`\chi_A`-truncated fields provide.  Continuity of the limit reward is the
source's hypothesis in Corollary 4 and is what the paper's own sentence calls
"the uniform continuity of the limiting reward".

The discrete value is `Sandpile.stoppingSup ⌊R^2T⌋ ⌊Rx⌋ F`, the supremum of
`E_{⌊Rx⌋}F(τ, X)` over walk stopping times `τ ≤ ⌊R^2T⌋`, at the reward
`F(k, X) = G'_R((⌊R^2T⌋-k)/R^2, X_k/R)`; the rescaled site `X_k/R` is
`Sandpile.External.Lclt.scaledSite R (X k)`, the same rescaling the local
central limit theorem uses.  The Brownian value is
`Sandpile.Continuum.brownianDiscount (B x) P_B h T` at `h = -G`, since that
definition is `\sup_{\tau\leq T}\mathbf E_x[-h(T-\tau,B_\tau)]` and the paper's
value is `\sup_{\tau\leq T}\mathbf E_x[G(T-\tau,B_\tau)]`.

Mathlib 4.32 constructs no Brownian motion, so the Brownian side is quantified
over a space carrying the family `B` indexed by the starting point, with `B y`
started at `y`, exactly as in every other statement of the repository.  That
space is quantified over every universe, which is what the source asserts: Coquet
and Toldo prove the theorem on an arbitrary probability space, with no
restriction of size, and a statement of the paper whose own realization space is
bound at `Type u` can then invoke it there.

How the paper's two rewards instantiate it.  The paper's rewards are written
with the ELAPSED time as their argument and subtract it from the horizon inside;
`G` and `G'` here take the REMAINING time instead, so the paper's
`(s,y) \mapsto -\chi_A(y)Z_R^{\rm lin}((t_R/R^2-s)_+,y)` is `G' R s y =
-\chi_A(y)Z_R^{\rm lin}(s,y)` and its limit is `G s y = -\chi_A(y)Z(s,y)`.  With
those, the discrete value below is
`\sup_{\tau\leq t_R}\mathbf E_{x_R}[-\chi_A(X_\tau/R)Z_R^{\rm lin}((t_R-\tau)/R^2,X_\tau/R)]`,
which is the paper's, and the Brownian value is
`\sup_{\tau\leq T}\mathbf E_x[-\chi_A(B_\tau)Z(T-\tau,B_\tau)]`, which is also the
paper's; the two are the two sides of the paper's sentence.  The rewards are
negated because `brownianDiscount` is defined with the gain `-h`, and the same
negation appears on both sides, so no sign is lost.  Because the remaining time
is the argument, neither reward depends on the horizon, which is why `G` and
`G'` may be bound before `T`.

Why the uniform convergence is over all of `\R^d`.  The paper's field converges
only locally uniformly, but the rewards carry the cutoff `\chi_A`, which vanishes
outside the ball of radius `2A`; the difference of the two rewards is therefore
supported in a fixed compact set, on which locally uniform convergence is
uniform.  So the hypothesis is exactly what `prop:dlt4-heat-potential-invariance`
supplies for the truncated fields, not a strengthening of it.

Quantifier order.  The dimension comes first, then the Brownian realization,
then the horizons `T_-` and `T_+`, written `T₀` and `T₁`, and the compact set `K`, which the paper
fixes before the limit, then the two reward families, then the accuracy
`\varepsilon`, and last the threshold `R_0`.  The threshold therefore depends on
everything the paper allows it to depend on and on nothing else.
-/
import Sandpile.Continuum.Stopping
import Sandpile.External.LocalCLT
import Sandpile.Walk

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

-- FROZEN-STATEMENT-BEGIN
/-- Stability of optimal-stopping values under uniform convergence of bounded
rewards, together with the invariance principle for the stopped walk
(`sandpile.tex:1900-1907`, `sandpile.tex:649`; Coquet-Toldo, Theorem 3 and
Corollary 4).  Assumed, not proved. -/
def Sandpile.External.ContinuumStoppingStability : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∀ (ΩB : Type u) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
      (∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB) →
    ∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ ≤ T₁ →
    ∀ K : Set (Sandpile.Continuum.Space d), IsCompact K →
    ∀ G : ℝ → Sandpile.Continuum.Space d → ℝ,
      Continuous (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) →
    ∀ G' : ℝ → ℝ → Sandpile.Continuum.Space d → ℝ,
    ∀ M : ℝ,
      (∀ (s : ℝ) (y : Sandpile.Continuum.Space d), |G s y| ≤ M) →
      (∀ (R s : ℝ) (y : Sandpile.Continuum.Space d), |G' R s y| ≤ M) →
      (∀ ε : ℝ, 0 < ε → ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ R : ℝ, R₁ ≤ R →
        ∀ s ∈ Set.Icc (0 : ℝ) T₁, ∀ y : Sandpile.Continuum.Space d,
          |G' R s y - G s y| ≤ ε) →
    ∀ ε : ℝ, 0 < ε →
      ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
        ∀ T ∈ Set.Icc T₀ T₁, ∀ x ∈ K,
          |Sandpile.stoppingSup ⌊R ^ 2 * T⌋₊ (fun i => ⌊R * x i⌋)
                (fun (k : ℕ) (X : ℕ → Sandpile.Site d) =>
                  G' R (((⌊R ^ 2 * T⌋₊ : ℕ) - (k : ℝ)) / R ^ 2)
                    (Sandpile.External.Lclt.scaledSite R (X k))) -
              Sandpile.Continuum.brownianDiscount (B x) PB (fun s y => -G s y) T| ≤ ε
-- FROZEN-STATEMENT-END
