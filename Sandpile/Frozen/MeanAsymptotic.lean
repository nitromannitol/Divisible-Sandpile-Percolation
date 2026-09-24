/-
Corollary of Section 4 of sandpile.tex, frozen.  `sandpile.tex:2041-2059`
(label `cor:dlt4-mean-asymptotic`):

  "For every $T>0$ and $x\in\R^d$,
   \[
     \E\mathcal U_R(T,x)
     \longrightarrow
     \E\mathcal U(T,x)=T^{(4-d)/4}\E\mathcal U(1,0)
     \qquad\text{and}\qquad
     \Var\mathcal U_R(T,x)
     \longrightarrow
     T^{(4-d)/2}\Var\mathcal U(1,0)\, ,
   \]
   and $\Var\mathcal U(1,0)>0$.  Consequently, as $t\to\infty$,
   \[
     \E u_t(0)\sim \E\mathcal U(1,0)t^{(4-d)/4}\, ,
     \qquad
     \Var(u_t(0))\sim \Var\bigl(\mathcal U(1,0)\bigr) t^{(4-d)/2}\, ."

The two objects come from the running text of `ssec:scaling-dlt4`.
`sandpile.tex:1817-1821`: "For $T>0,\ x\in\R^d$, define the rescaled odometer by
$\mathcal U_R(T,x)\coloneqq R^{-(2-d/2)} u_{\lfloor R^2T\rfloor}(\lfloor Rx\rfloor)$,
with the floor taken coordinatewise."  `sandpile.tex:1824-1825`: "In this
subsection, write $\mathcal U$ for the value $\mathcal U_Z$ from
\eqref{eq:continuum-membrane-stopping-value}."  They are `Sandpile.Continuum.rescaledOdometer` and
`Sandpile.Continuum.continuumValue`.

The standing hypotheses are those of `sandpile.tex:1810-1814`: `d ≤ 3`,
`E ζ(0) = 0`, `0 < Var(ζ(0)) < ∞`, and `E e^{θ₀|ζ(0)|} < ∞` for some `θ₀ > 0`.

Modelling choices.

The scenery is carried by its one-site law `ν` and the mass field by
`centeredMassLaw d ν`, the law of `σ = 1 + 2dζ`, so that `u_t` is
`Sandpile.odometer σ t` and `E u_t(0)` is `Sandpile.meanOdometer`, exactly as in
the frozen Theorem 1.3.  The variance of the scenery, which is the `Var(ζ(0))`
appearing in `Z`, is `variance id ν`.

The Gaussian heat potential is read through the continuous version fixed at
`sandpile.tex:1019-1021` and `sandpile.tex:2104`: the field `Z` is a
modification of `eq:dlt4-linear-gaussian-potential`, almost surely continuous on
each strip `[0,T] × ℝ^d` and of polynomial growth there, and the value
`𝒰 = 𝒰_Z` is built from it.  Continuity and growth are what make the supremum
over the Brownian stopping rules a supremum over a bounded set of reals, so that
`𝒰(T,x)` is the value of `eq:continuum-membrane-stopping-value` and not the
junk value of an unbounded supremum.  These are the binders
`prop:continuum-value-selfsimilar` carries, in the same form and the same
position.

Mathlib 4.32 constructs neither white noise nor a Brownian motion, so the
statement is quantified over a space `ΩW` carrying white noise and a space `ΩB`
carrying Brownian motion; the field is frozen at a point of `ΩW` while the
Brownian expectation integrates over `ΩB`, which is the paper's convention that
`B` is independent of `𝒲` and that the white noise is held fixed inside the
stopping value.  `brownianValue` carries its starting point only through the
Brownian motion, so a value at every starting point needs a family `B` indexed
by the starting point, with `B y` started at `y`.  The motion carries the two
binders of `lem:brownian-ball-localization`, continuity of EVERY path and strong
measurability of the value at each time, without which the supremum defining the
continuum value is the junk value of an unbounded supremum, and `ΩB` names its
universe because the cited stability input is a hypothesis about a realization
space and is taken at the universe where the motion lives.

`R → ∞` is `atTop` on `ℝ`, matching the index set `R ≥ 1` of the family.
`f ∼ g` is `Tendsto (fun t => f t / g t) atTop (𝓝 1)`.

Junk values: an integral of a non-integrable function and the variance of a
function not in `L²` are both zero in Mathlib, which would make the limit
statements empty.  The corollary presupposes that all four quantities are
finite, so square-integrability of the rescaled odometers, of the odometer
itself, and of the limiting value is asserted as part of the conclusion.  Real
powers `t^{(4-d)/4}` are `Real.rpow` of a nonnegative base.
-/
import Sandpile.Continuum.Stopping
import Sandpile.Law
import Sandpile.Support.MeanACorollary

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u


-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dlt4_mean_asymptotic
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
    (hVarScale : Sandpile.External.VarianceScale)
    (d : ℕ) (hd0 : 0 < d) (hd : d ≤ 3)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ)
    (hZmod : ∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
      Z t x =ᵐ[PW] fun ω =>
        Sandpile.Continuum.gaussianPotential d (variance id ν) W t x ω)
    (hZcont : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
        (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d))))
    (hZgrow : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
      ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)),
        |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k)
    {ΩB : Type u} [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
    (hOS : Sandpile.External.ContinuumOptimalStopping ΩB)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (hB : ∀ y : Sandpile.Continuum.Space d, Sandpile.Continuum.IsBrownian d y (B y) PB)
    (hBc : ∀ (y : Sandpile.Continuum.Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (T : ℝ) (hT : 0 < T) (x : Sandpile.Continuum.Space d) :
    (∀ R : ℝ, 1 ≤ R →
        MemLp (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ) 2
          (Sandpile.centeredMassLaw d ν)) ∧
      (∀ t : ℕ, MemLp (fun σ => Sandpile.odometer σ t 0) 2 (Sandpile.centeredMassLaw d ν)) ∧
      MemLp (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω) 2 PW ∧
      MemLp (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω) 2 PW ∧
      Tendsto (fun R : ℝ => ∫ σ, Sandpile.Continuum.rescaledOdometer d R T x σ
          ∂(Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ∂PW)) ∧
      (∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ∂PW =
        T ^ ((4 - (d : ℝ)) / 4) * ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB 1 0 ω ∂PW) ∧
      Tendsto (fun R : ℝ => variance
          (fun σ => Sandpile.Continuum.rescaledOdometer d R T x σ)
          (Sandpile.centeredMassLaw d ν)) atTop
        (𝓝 (T ^ ((4 - (d : ℝ)) / 2) * variance
          (fun ω => Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω) PW)) ∧
      0 < variance (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω) PW ∧
      Tendsto (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t /
          ((∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ∂PW) * (t : ℝ) ^ ((4 - (d : ℝ)) / 4)))
        atTop (𝓝 1) ∧
      Tendsto (fun t : ℕ =>
          variance (fun σ => Sandpile.odometer σ t 0) (Sandpile.centeredMassLaw d ν) /
          (variance (fun ω => Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω) PW * (t : ℝ) ^ ((4 - (d : ℝ)) / 2)))
        atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= Sandpile.Support.dlt4_mean_asymptotic_wired hLocalCLT hStab hVarScale d hd0 hd ν hmean hvar hvar'
    θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB hOS B hB hBc hBm T hT x
