/-
Theorem of sandpile.tex, frozen.  `sandpile.tex:4687-4710`
(label `thm:dgt4-diffusive-membrane`):

  "Let $d\geq5$.  Suppose that $(\zeta(x))_{x\in\Z^d}$ are i.i.d.\ and
   atomless, with mean zero and finite positive variance.  Assume either that
   (a) the $\zeta(x)$ are Gaussian; or (b) the $\zeta(x)$ are bounded above and,
   for some $\alpha>2$,
     $\P(\zeta(0)<-\lambda r)/\P(\zeta(0)<-r)\longrightarrow\lambda^{-\alpha}$
     $(r\to\infty)$,
   for every $\lambda>0$.  Then, for every $T>0$ and every $s>(d-4)/2$, as
   $R\to\infty$,
     $R^{(d-4)/2}\bigl(u_{\lfloor R^2T\rfloor}-\E u_{\lfloor R^2T\rfloor}(0)\bigr)^{(R)}
      \Longrightarrow\mathcal H_{\kappa,T}$ in $H^{-s}_{\rm loc}(\R^d)$,
   where $\kappa=1$ in case (a) and $\kappa=1-1/\alpha$ in case (b).  Moreover,
   as $n\to\infty$, $\P(u_n(0)=0)\sim\frac{G(0,0)\kappa}{n}$."

Modelling decisions.

The two cases are mutually exclusive, so this is ONE theorem with a disjunctive
hypothesis `hcase` in which each disjunct also pins `κ`: the paper's "where
`κ = 1` in case (a) and `κ = 1 - 1/α` in case (b)" is exactly the statement that
`κ` is determined by the case, and `α` is bound inside the second disjunct
because it is named only there.

The scenery is the mass field written in the paper's normalization: the
integration variable is `σ` with law `Sandpile.centeredMassLaw d ν`, so that
`ζ = (σ - 1)/(2d)` has one-site law `ν` and `u_n` is `Sandpile.odometer σ n`.
This is the convention of the other frozen files, and `centeredMassLaw` carries
the `IsProbabilityMeasure` instance that `TendstoInNegSobolev` needs.

`⌊R^2T⌋` is `Nat.floor`; the convergence is along `R → ∞`, and the tightness
clause inside `TendstoInNegSobolev` only ever uses `1 ≤ R`, so the value of
`Nat.floor` at negative arguments is never seen.

`ℋ_{κ,T}` enters only through its covariance, since it is a centred Gaussian
random distribution: `Sandpile.Continuum.weightedMembraneCov d (Var ζ(0)) κ T`.
The statement is therefore not quantified over a space carrying white noise; the
white noise is already integrated out of the covariance.  Convergence in
`H^{-s}_{loc}(ℝ^d)` is `Sandpile.Continuum.TendstoInNegSobolev`.

Cited inputs (standing convention R1).  The proof at `sandpile.tex:4639-4691` runs
through `prop:dgt4-linearization` and `prop:weighted-membrane-limit`, and the
latter's own proof cites the local central limit theorem `eq:lclt-parity`, the
Gaussian upper bound `eq:rw-gaussian-upper`, the Green estimates
`eq:dgt4-intersection-first-moment`, and, for tightness through
`lem:sobolev-tightness`, the Besov tightness criterion.  The four
hypotheses `hHeatKernel`, `hGreenHigh`, `hLocalCLT` and `hBesov` were added at
version 2 for that reason.  The theorem's second conjunct is
`prop:dgt4-contact-asymptotics`, whose case (a) cites Gaussian concentration for a
Lipschitz functional at `sandpile.tex:5267-5271`; `hGaussConc` was added at
version 4 for that.  `hBesov` is bound after `d` because the Prop is
parametrized by the scenery space `Sandpile.Site d → ℝ`.

"Atomless" is `∀ z, ν {z} = 0` rather than a `NoAtoms` instance, and "Gaussian"
is `ν = gaussianReal 0 v` for some `v : ℝ≥0`; the mean is already fixed to zero
by `hmean`.  "Bounded above" is `ν (Set.Ioi M) = 0` for some `M`.  In the
regular-variation hypothesis the ratio is a quotient of reals; if
`P(ζ(0) < -r)` vanished for all large `r` the quotient would take the junk value
`0`, which is never the required positive limit `λ^{-α}`, so no law satisfies
the hypothesis vacuously.

`f ∼ g` is `Tendsto (f / g) atTop (𝓝 1)`, and `P(u_n(0) = 0)` is the `toReal` of
the measure of that event.  `G(0,0)` is `Sandpile.green d 0 0`, which is the
genuine Green function because `5 ≤ d`.
-/
import Sandpile.Law
import Sandpile.Walk
import Sandpile.Continuum.Membrane
import Sandpile.External.HeatKernelBounds
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.NormalComparison
import Sandpile.External.LocalCLT
import Sandpile.External.LocalCLTProved
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.GaussianLipschitzConcentration
import Sandpile.Support.ManyLMembrane

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_diffusive_membrane
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    (κ : ℝ)
    (hcase :
      ((∃ v : ℝ≥0, ν = gaussianReal 0 v) ∧ κ = 1) ∨
      (∃ α : ℝ, 2 < α ∧ (∃ M : ℝ, ν (Set.Ioi M) = 0) ∧
        (∀ lam : ℝ, 0 < lam →
          Tendsto (fun r : ℝ => (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
            atTop (𝓝 (lam ^ (-α)))) ∧
        κ = 1 - 1 / α)) :
    (∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
        Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
          (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
            R ^ (((d : ℝ) - 4) / 2) *
              Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer σ ⌊R ^ 2 * T⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊R ^ 2 * T⌋₊) φ)
          (Sandpile.Continuum.weightedMembraneCov d (variance (id : ℝ → ℝ) ν) κ T)) ∧
      Tendsto (fun n : ℕ =>
          ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal /
            (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= by
  have hHeatKernel : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  exact Sandpile.Support.dgt4_diffusive_membrane_of_inputs hHeatKernel hGreenHigh hGaussConc
    hNormal Sandpile.External.localCLT d hd hBesov ν hatom hmean hvar hvar' κ hcase
