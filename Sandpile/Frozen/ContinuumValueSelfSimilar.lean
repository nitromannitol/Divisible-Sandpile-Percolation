/-
Proposition of Section 4 of sandpile.tex, frozen.  `sandpile.tex:1989-2008`
(label `prop:continuum-value-selfsimilar`):

  "For every $T>0$ and every $x\in\R^d$,
   \[
     \mathcal U(T,x)\stackrel d= T^{(4-d)/4}\mathcal U(1,0)\, .
   \]
   There is $\theta>0$ such that
   \[
     \sup_{R\geq1}\E e^{\theta\mathcal U_R(1,0)}<\infty\, ,
     \qquad
     \E e^{\theta\mathcal U(1,0)}<\infty \, .
   \]
   In particular, for every $p>0$,
   \[
     \E\mathcal U(T,x)^p
     =
     T^{p(4-d)/4}\E\mathcal U(1,0)^p\, ,
     \qquad
     0<\E\mathcal U(1,0)^p<\infty \, ."

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

"Equal in distribution" is equality of the pushforward measures, `Measure.map`.
That map takes the junk value zero for a non-measurable function, which would
make the identity vacuous, so the identity is asserted for a MEASURABLE version
of the value.

The first clause carries the value as a measurable functional `U` of the
white-noise sample, equal almost everywhere to `continuumValue`, and states the
scaling identity for `U`.  The earlier form asserted the identity for
`continuumValue` itself, with almost-everywhere measurability of the two sides
adjoined.  That form cannot be proved and does not say what the paper says.
`continuumValue` is an `sSup` over the Brownian stopping times of `B x`, a
different family for each starting point `x`, and the paper's proof
(`sandpile.tex:1988-1992`) rescales time by `T`, which turns the stopping times
bounded by `T` of the motion started at `x` into the stopping times bounded by
one of the rescaled motion `s ↦ T^{-1/2}(B_x(Ts)-x)`.  That rescaled motion is a
Brownian motion started at the origin, but it is NOT the member `B 0` of the
given family, and nothing in the earlier statement related the two sides'
stopping families.  What makes the descent from the equality in law of the
fields to the equality in law of the values legitimate is that the stopping
value is a measurable functional of the field alone, which is what
`prop:brownian-os` supplies on one probability space: its right-continuous
value process is measurable and the optimal time is the first entry into the
contact set the field determines.  The clause is therefore stated on the one
space the theorem fixes, for that functional.  A measurable version is also
strictly more than the earlier almost-everywhere measurability, so nothing the
paper asserts has been weakened.

Mathlib 4.32 constructs neither white noise nor a Brownian motion, so the
statement is quantified over a space `ΩW` carrying white noise and a space `ΩB`
carrying Brownian motion, the field being frozen at a point of `ΩW` while the
Brownian expectation integrates over `ΩB`; this is the paper's convention that
`B` is independent of `𝒲`.  `brownianValue` carries its starting point only
through the Brownian motion, so a value at every starting point needs a family
`B` indexed by the starting point.

`T` and `x` are quantified inside each of the two clauses that mention them,
and NOT as parameters of the theorem, because the middle clause is the paper's
"There is $\theta>0$ such that", which stands outside both: `θ` is a constant of
the scenery law alone.  Binding `T` and `x` first would let the witness `θ`
depend on them.  "$\sup_{R\geq1}\E e^{\theta\mathcal U_R(1,0)}<\infty$" is
a single real bound valid for every `R ≥ 1`, together with the integrability
which makes each expectation a real number rather than the junk value zero;
"$\E e^{\theta\mathcal U(1,0)}<\infty$" is integrability alone.

`\mathcal U^p` for real `p` is `Real.rpow`.  Both values are nonnegative, as the
paper records at `sandpile.tex:1976-1980` and `sandpile.tex:2007`, so the
negative-base junk branch of `rpow` is never reached; integrability of the
`p`-th power is asserted so that `0 < \E\mathcal U(1,0)^p<\infty` is the paper's
two-sided statement and not a statement about a junk zero.

The proof uses the parabolic scaling limit of Theorem 1.3(i)(b), carrying its
cited stopping-stability input at the Brownian realization space's universe.
The motion has continuous paths at every sample and strongly measurable
evaluations; `Sandpile.Continuum.exists_isBrownian_cont` supplies such a motion.

The scenery is carried by its one-site law `ν` and the mass field by
`centeredMassLaw d ν`, so `u_t` is `Sandpile.odometer σ t` and `Var(ζ(0))`,
which is the variance appearing in `Z`, is `variance id ν`.
-/
import Sandpile.Continuum.Stopping
import Sandpile.Law
import Sandpile.Support.MeanAValue
import Sandpile.External.VarianceScale
import Sandpile.External.ContinuumOptimalStopping
import Sandpile.Frozen.BrownianScalingLimit
import Sandpile.Support.ContSelfSimilarFromScaling

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

universe u

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.continuum_value_self_similar
    (hStab : Sandpile.External.ContinuumStoppingStability.{u})
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
    (hBm : ∀ (y : Sandpile.Continuum.Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) :
    (∃ U : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ,
      (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        Measurable (U T x) ∧
        U T x =ᵐ[PW] fun ω =>
          Sandpile.Continuum.continuumValue d Z B PB T x ω) ∧
      ∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d,
        PW.map (U T x) = PW.map (fun ω => T ^ ((4 - (d : ℝ)) / 4) * U 1 0 ω)) ∧
    (∃ θ : ℝ, 0 < θ ∧
      (∃ M : ℝ, ∀ R : ℝ, 1 ≤ R →
        Integrable (fun σ => Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ))
          (Sandpile.centeredMassLaw d ν) ∧
        ∫ σ, Real.exp (θ *
          Sandpile.Continuum.rescaledOdometer d R 1 0 σ)
          ∂(Sandpile.centeredMassLaw d ν) ≤ M) ∧
      Integrable (fun ω => Real.exp (θ *
        Sandpile.Continuum.continuumValue d Z B PB 1 0 ω)) PW) ∧
    (∀ T : ℝ, 0 < T → ∀ x : Sandpile.Continuum.Space d, ∀ p : ℝ, 0 < p →
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB T x ω ^ p) PW ∧
      Integrable (fun ω => Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p) PW ∧
      ∫ ω, Sandpile.Continuum.continuumValue d
          Z B PB T x ω ^ p ∂PW =
        T ^ (p * (4 - (d : ℝ)) / 4) *
          ∫ ω, Sandpile.Continuum.continuumValue d
            Z B PB 1 0 ω ^ p ∂PW ∧
      0 < ∫ ω, Sandpile.Continuum.continuumValue d
        Z B PB 1 0 ω ^ p ∂PW)
-- FROZEN-STATEMENT-END
:= by
  have _ := hOS
  exact Sandpile.Support.continuum_value_self_similar_of_parabolic_limit
    d hd0 hd ν hvar hvar' θ₀ hθ₀ hexp PW W hW Z hZmod hZcont PB B
    (fun T hT => Sandpile.Frozen.brownian_scaling_limit hStab d hd0 hd ν hmean
      hvar hvar' θ₀ hθ₀ hexp ΩW PW W hW Z hZmod hZcont hZgrow ΩB PB B hB hBc hBm T hT)
