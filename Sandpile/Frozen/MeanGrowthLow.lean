/-
Theorem 1.3(i)(a) of sandpile.tex, frozen.  `sandpile.tex:213-215`
(label `thm:main-explosion`, part (i)(a)):

  "Let $\sigma=1+2d\zeta$, where $(\zeta(x))$ are i.i.d. with $\E\zeta(0)=0$ and
   $0<\Var(\zeta(0))<\infty$ [and an exponential moment].
   (i)(a) [$d\leq3$] The rescaled mean converges:
   $\lim_{t\to\infty}t^{-(4-d)/4}\E u_t(0)$ exists and lies in $(0,\infty)$."

The limit is bound after the law, so it does not depend on `t`.

The paper proves part (i)(a) from `cor:dlt4-mean-asymptotic` (`sandpile.tex:299`:
"Part (i)(a) is Corollary~\ref{cor:dlt4-mean-asymptotic}"), whose own proof runs
through `thm:main-explosion`(i)(b) and `prop:continuum-value-selfsimilar`.  Three
results cited from outside the paper enter that chain: the stability of
optimal-stopping values under uniform convergence of bounded rewards
(`sandpile.tex:1118`), the scaling of the variance of the membrane field, and the
finite-horizon optimal-stopping theorem for Brownian motion (`sandpile.tex:1099`,
Peskir and Shiryaev, Theorem 2.2).  The first and third are carried here as
explicit hypotheses rather than as axioms.  The variance scaling is proved
unconditionally in this repository, `Sandpile.External.varianceScale`
(`Sandpile/External/VarianceScaleProved.lean`), so it is no longer carried as an
explicit hypothesis.  The polynomial growth on every strip of a continuous
version of the Gaussian heat potential (`sandpile.tex:1019-1021`, Adler and
Taylor, Theorem 2.1.1) is likewise no longer an input: it is
`Sandpile.Support.continuousVersionGrowth`, proved in the repository from the
Kolmogorov moment machinery of `MeanA*` and a quantitative box tail, by
Borel-Cantelli over the unit boxes of the integer lattice.

The statement names no probability space: the proof builds its own, through
`Sandpile.Continuum.exists_isWhiteNoise` and
`Sandpile.Continuum.exists_isBrownian_cont`.  The optimal-stopping input is therefore
carried in the form it has for every space, which is the form the cited theorem
has: its conclusion is guarded by the hypothesis that the space carries a family
of Brownian motions, so on a space that carries none it says nothing.  For the
same reason the stability input is taken at the universe of those constructed
spaces, `Type 0`, and not at an unrelated one.
-/
import Sandpile.Law
import Sandpile.Support.MeanAExplosionA
import Sandpile.External.ContStoppingStability
import Sandpile.External.VarianceScaleProved
import Sandpile.External.ContinuumOptimalStopping

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.mean_growth_le_three
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{0})
    (hOS : ∀ (ΩB : Type) [MeasurableSpace ΩB], Sandpile.External.ContinuumOptimalStopping ΩB)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-((4 - (d : ℝ)) / 4)) *
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 L)
-- FROZEN-STATEMENT-END
:= Sandpile.Support.mean_growth_le_three_wired hLocalCLT hStab Sandpile.External.varianceScale hOS
    d hd hd3 ν hprob hmean hvar hvar' θ₀ hθ₀ hexp
