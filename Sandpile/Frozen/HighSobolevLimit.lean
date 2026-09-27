/-
Theorem 1.3(iii)(c) of sandpile.tex, frozen.  `sandpile.tex:274-285`
(label `thm:main-explosion`, part (iii)(c)):

  "For Gaussian scenery, for every $T>0$ and every $s>(d-4)/2$,
   $R^{(d-4)/2}\left(u_{\lfloor TR^2\rfloor}-\E u_{\lfloor TR^2\rfloor}(0)\right)^{(R)}
   \Longrightarrow\mathcal H_{1,T}$ in $H^{-s}_{\rm loc}(\R^d)$.
   If instead the scenery is atomless and bounded above, and there exists
   $\alpha>2$ such that for every $\lambda>0$, as $s\to\infty$ we have
   $\P(\zeta(0)<-\lambda s)/\P(\zeta(0)<-s)\longrightarrow\lambda^{-\alpha}$,
   then the limit is $\mathcal H_{1-1/\alpha,T}$."

Modelling choices.  The preamble of Theorem 1.3 assumes the extra exponential
moment only in parts (i), (ii), and (iii)(a)-(b), so this statement carries only
mean zero and finite positive variance.  Convergence in `H^{-s}_{\rm loc}(\R^d)`
is `TendstoInNegSobolev`, whose two clauses are convergence in distribution of
every pairing and tightness of the norms; the limit field `\mathcal H_{\kappa,T}`
is centred Gaussian and so is recorded by its covariance
`weightedMembraneCov d (\Var\zeta(0)) \kappa T`, with `\kappa=1` in the Gaussian
case and `\kappa=1-1/\alpha` in the heavy-tail case.  The rescaled field is
`R^{(d-4)/2}` times the pairing `latticePairing R` of `u_t-\E u_t(0)` against a
test function, which is the paper's `(\cdot)^{(R)}`.  "Gaussian scenery" is
`ν = gaussianReal 0 v`; the centring and the variance are then the preamble's.
"Atomless" is `ν\{z\}=0` for every `z`, "bounded above" is `ν(M,\infty)=0` for
some `M`, and the regular-variation hypothesis is a limit of a ratio of two tail
probabilities: if the denominator vanished for large `r`, the ratio would take
the junk value zero and the hypothesis would be false, not vacuous.

Cited inputs (standing convention R1).  At `sandpile.tex:307-308` the proof of
`thm:main-explosion` reads "part (iii)(c) is
Theorem~\ref{thm:dgt4-diffusive-membrane}", so this statement carries the cited
inputs of that theorem: the heat-kernel bounds, the Green estimates in `d ≥ 5`,
Gaussian concentration for a Lipschitz functional, the normal comparison, the
intersection second moment, the local central limit theorem, and the Besov
tightness criterion.  The heat-kernel bounds and the `d ≥ 5` Green estimates are
each proved unconditionally in this repository
(`Sandpile.External.heatKernelBounds`, `Sandpile.External.greenBoundsHigh`), so
neither is carried here as an explicit hypothesis; the rest, added at version 3,
remain hypotheses that this statement did not carry before.
-/
import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.LocalCLT
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.External.GreenBoundsHighProved
import Sandpile.Support.ExplHighSobolev

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.high_sobolev_limit
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
    (hLocalCLT : Sandpile.External.LocalCLT)
    (d : ℕ) (hd : 5 ≤ d)
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site d → ℝ))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤) :
    (∀ v : ℝ≥0, ν = gaussianReal 0 v →
        ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
          Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
            (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
              R ^ (((d : ℝ) - 4) / 2) *
                Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
            (Sandpile.Continuum.weightedMembraneCov d (variance id ν) 1 T)) ∧
      ((∀ z : ℝ, ν {z} = 0) → (∃ b : ℝ, ν (Set.Ioi b) = 0) →
        ∀ α : ℝ, 2 < α →
          (∀ lam : ℝ, 0 < lam →
              Tendsto (fun r : ℝ =>
                  (ν (Set.Iio (-(lam * r)))).toReal / (ν (Set.Iio (-r))).toReal)
                atTop (𝓝 (lam ^ (-α)))) →
          ∀ T : ℝ, 0 < T → ∀ s : ℝ, ((d : ℝ) - 4) / 2 < s →
            Sandpile.Continuum.TendstoInNegSobolev d s (Sandpile.centeredMassLaw d ν)
              (fun (R : ℝ) (σ : Sandpile.Site d → ℝ) (φ : Sandpile.Continuum.Space d → ℝ) =>
                R ^ (((d : ℝ) - 4) / 2) *
                  Sandpile.Continuum.latticePairing R
                    (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
                      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) ⌊T * R ^ 2⌋₊) φ)
              (Sandpile.Continuum.weightedMembraneCov d (variance id ν) (1 - 1 / α) T))
-- FROZEN-STATEMENT-END
:=
  Sandpile.Support.high_sobolev_limit_of_membrane hd ν hmean hvar hvar'
    (fun κ hatom hcase =>
      (Sandpile.Frozen.dgt4_diffusive_membrane
        hGaussConc hNormal
        hLocalCLT d hd hBesov ν hatom hmean hvar hvar' κ hcase).1)
