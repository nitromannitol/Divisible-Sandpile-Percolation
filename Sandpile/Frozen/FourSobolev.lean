/-
Theorem 1.3(ii)(c) of sandpile.tex, frozen.  `sandpile.tex:254-258`
(label `thm:main-explosion`, part (ii)(c)):

  "For every $T>0$ and $s>0$, the fields
   $\bigl(u_{\lfloor TR^2\rfloor}-\E u_{\lfloor TR^2\rfloor}(0)\bigr)^{(R)}$ for
   $R\geq1$ are tight in $H^{-s}_{\rm loc}(\R^4)$.  Moreover, for every
   $\alpha>2$, the fields $\bigl(u_{t_R}-\E u_{t_R}(0)\bigr)^{(R)}$ at the
   superdiffusive times $t_R\coloneqq\lfloor R^\alpha\rfloor$ converge, modulo
   additive constants, to the four-dimensional membrane model $\mathcal G_4$ in
   $H^{-s}_{\rm loc}(\R^4)$."

Modelling choices.  A lattice field enters as the functional
`latticePairing R f`, which is the paper's `f^{(R)}(\varphi)`, and
`\E u_t(0)` is `meanOdometer`.  The first conjunct is `TightInNegSobolev` at the
diffusive times `\lfloor TR^2\rfloor`.  In the second conjunct "modulo additive
constants" is meaningless for a bare distribution, so the paper's own device is
used: `prop:d4-superdiffusive-limit` fixes a bounded domain `D` and a density
`\omega\in C_c^\infty(D)` with `\omega\geq0` and `\int_D\omega=1`, and states
the convergence for the `\omega`-representatives
`[(u_{t_R}-\E u_{t_R}(0))^{(R)}]^\omega\Rightarrow\mathcal G_4^\omega` in
`H^{-s}(D)`.  That is transcribed by applying `omegaRep D w` to the pairing
functional and writing out, for this fixed `D`, the two clauses of
`TendstoInNegSobolev`: convergence in distribution of every pairing against a
test function supported in `D` to the centred Gaussian of the matching variance,
and tightness of the `H^{-s}(D)` norms.  The limiting variance is the covariance
of `\mathcal G_4^\omega`, namely `membraneCov4` evaluated at the subtracted test
function, which is `omegaRep D w` applied in each of the two slots.
`\Var(\zeta(0))` is `variance id ν`.  `IsDomain` records only that `D` is open,
bounded, and nonempty, so the statement quantifies over more domains than the
paper's smooth ones.  The exponential moment is carried, since the preamble of
Theorem 1.3 assumes it in part (ii).

Cited inputs (standing convention R1).  The two propositions the proof combines
carry the heat-kernel bounds, the Besov tightness criterion and the variance
scaling of the four-dimensional field, so this statement carried them too at
earlier versions; the heat-kernel bounds and the variance scaling are each
proved unconditionally in this repository (`Sandpile.External.heatKernelBounds`,
`Sandpile.External.varianceScale`), so neither is carried here as an explicit
hypothesis.  `hMembrane`, the scaling limit of the four-dimensional discrete
membrane field cited in Step 1 of `prop:d4-superdiffusive-limit`, remains one.
-/
import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.External.ContinuumBesovTightness
import Sandpile.External.HeatKernelBoundsProved
import Sandpile.External.MembraneScalingFour
import Sandpile.External.VarianceScaleProved
import Sandpile.Support.ExplFourSobolev

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.four_sobolev
    (hBesov : Sandpile.External.ContinuumBesovTightness (Sandpile.Site 4 → ℝ))
    (hMembrane : Sandpile.External.MembraneScalingLimitFour)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s) :
    Sandpile.Continuum.TightInNegSobolev 4 s (Sandpile.centeredMassLaw 4 ν)
        (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
          Sandpile.Continuum.latticePairing R
            (fun x => Sandpile.odometer σ ⌊T * R ^ 2⌋₊ x -
              Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊T * R ^ 2⌋₊)) ∧
      ∀ D : Set (Sandpile.Continuum.Space 4), Sandpile.Continuum.IsDomain D →
        ∀ w : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsAveragingDensity D w →
          ∀ α : ℝ, 2 < α →
            (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
                TendstoInDistribution
                  (fun (R : ℝ) (σ : Sandpile.Site 4 → ℝ) =>
                    Sandpile.Continuum.omegaRep D w
                      (Sandpile.Continuum.latticePairing R
                        (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                          Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
                  atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
                  (gaussianReal 0 (Real.toNNReal
                    (Sandpile.Continuum.omegaRep D w
                      (fun φ' => Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.membraneCov4 (variance id ν) φ') φ) φ)))) ∧
              ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
                Sandpile.centeredMassLaw 4 ν
                    {σ | M < Sandpile.Continuum.negSobolevNorm 4 s D
                      (Sandpile.Continuum.omegaRep D w
                        (Sandpile.Continuum.latticePairing R
                          (fun x => Sandpile.odometer σ ⌊R ^ α⌋₊ x -
                            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
                  ENNReal.ofReal ε
-- FROZEN-STATEMENT-END
:=
  -- The assembly of the two propositions the paper's proof names
  -- (`sandpile.tex:302-304`).  The first conjunct, the tightness at the diffusive times
  -- `⌊TR²⌋`, is `prop:d4-diffusive-tightness`; the second is `prop:d4-superdiffusive-limit`
  -- at every domain, every averaging density and every exponent `α > 2`.
  Sandpile.Support.four_sobolev_of_superdiffusive Sandpile.External.heatKernelBounds hBesov ν
    inferInstance hmean hvar hvar' T hT s hs
    (fun D hD w hw α hα =>
      Sandpile.Frozen.d4_superdiffusive_limit
        hMembrane D hD w hw α hα ν
        inferInstance
        hmean hvar hvar' θ₀ hθ₀ hexp s hs)
