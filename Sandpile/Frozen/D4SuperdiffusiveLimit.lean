/-
Proposition of Section 5 of sandpile.tex, frozen.  `sandpile.tex:3356-3364`
(label `prop:d4-superdiffusive-limit`):

  "[Superdiffusive membrane limit in dimension four]  Fix a bounded smooth
   domain $D\subset\R^4$, a density $\omega\in C_c^\infty(D)$ satisfying
   $\omega\geq0$ and $\int_D\omega(x)dx=1$, and $\alpha>2$.  Then, for every
   $s>0$, as $R\to\infty$,
   \[
     \left[\bigl(u_{\lfloor R^\alpha\rfloor}-\E u_{\lfloor R^\alpha\rfloor}(0)
     \bigr)^{(R)}\right]^\omega\Longrightarrow\mathcal G_4^\omega
     \qquad\text{in }H^{-s}(D)\, .
   \]
   Here $\mathcal G_4$ is the four-dimensional continuum membrane model of
   Subsection~\ref{ssec:continuum-membrane-fields} and the superscript $\omega$
   is defined in \eqref{eq:d4-omega-representative}."

Modelling.  The scenery `ζ` is carried by its one-site law `ν` and the field by
`centeredMassLaw 4 ν`, the law of `σ = 1 + 8ζ`, so `u_t` is
`Sandpile.odometer σ t` and `E u_t(0)` is `Sandpile.meanOdometer`.  The
standing hypotheses of `sec:dim4-regime` are in force: mean-zero i.i.d.\
scenery with `0 < Var(ζ(0)) < ∞` and an exponential moment.  The domain is
`IsDomain D` and the density is `IsAveragingDensity D ω`, which is exactly the
paper's three conditions on `ω`.  The time is `⌊R^α⌋` as a natural number.

Both sides carry the `ω`-representative of `eq:d4-omega-representative`:
the left side is `omegaRep D ω` applied to the pairing functional, and the
limit is the centred Gaussian random distribution with covariance
`omegaMembraneCov4 D ω Var(ζ(0))`, that is `Cov(𝒢_4(φ̃), 𝒢_4(ψ̃))` with
`φ̃ = φ - ω∫_D φ`.  This is `𝒢_4^ω`.  Because the limit is a covariance, no
white noise and no auxiliary probability space are needed here.

Cited input (standing convention R1).  Step 1 of the paper's proof cites the
convergence of the discrete membrane field to the continuum membrane field, so
the statement carries `Sandpile.External.MembraneScalingLimitFour`, which is
that convergence stated for the four-dimensional potential kernel; the paper's
own new point, that the time truncation washes out at superdiffusive times, is
not assumed but proved here.

The convergence is in `H^{-s}(D)` for the fixed domain `D` of the statement,
not in `H^{-s}_{\rm loc}(\R^4)`, so `Sandpile.Continuum.TendstoInNegSobolev` is
not used: its two clauses quantify over test functions on all of `ℝ^4` and over
all bounded domains.  Instead the two clauses are written out inline for the
single domain `D`: every pairing with a test function supported in `D`
converges in distribution to the centred Gaussian with the matching variance,
and the `H^{-s}(D)` norms are tight.  This is neither a weakening nor a
strengthening of that definition, but its specialization to one domain, which
is what the paper states.
-/
import Sandpile.Law
import Sandpile.Continuum.Membrane
import Sandpile.External.HeatKernelBounds
import Sandpile.External.MembraneScalingFour
import Sandpile.External.VarianceScale
import Sandpile.Support.D4STightness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_superdiffusive_limit
    (hMembrane : Sandpile.External.MembraneScalingLimitFour)
    (D : Set (Sandpile.Continuum.Space 4)) (hD : Sandpile.Continuum.IsDomain D)
    (w : Sandpile.Continuum.Space 4 → ℝ)
    (hw : Sandpile.Continuum.IsAveragingDensity D w)
    (α : ℝ) (hα : 2 < α)
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (s : ℝ) (hs : 0 < s) :
    (∀ φ : Sandpile.Continuum.Space 4 → ℝ, Sandpile.Continuum.IsTestFn D φ →
        TendstoInDistribution
          (fun (R : ℝ) (ω : Sandpile.Site 4 → ℝ) =>
            Sandpile.Continuum.omegaRep D w
              (Sandpile.Continuum.latticePairing R
                (fun x => Sandpile.odometer ω ⌊R ^ α⌋₊ x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)) φ)
          atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw 4 ν)
          (gaussianReal 0 (Real.toNNReal
            (Sandpile.omegaMembraneCov4 D w (variance id ν) φ φ)))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
        Sandpile.centeredMassLaw 4 ν
            {ω | M < Sandpile.Continuum.negSobolevNorm 4 s D
              (Sandpile.Continuum.omegaRep D w
                (Sandpile.Continuum.latticePairing R
                  (fun x => Sandpile.odometer ω ⌊R ^ α⌋₊ x -
                    Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) ⌊R ^ α⌋₊)))} ≤
          ENNReal.ofReal ε)
-- FROZEN-STATEMENT-END
:= by
  have hHeatKernel : Sandpile.External.HeatKernelBounds := Sandpile.External.heatKernelBounds
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  haveI := hprob
  -- the moment hypotheses the two clauses consume, from the finite variance
  have hsqm : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hsq2 : Integrable (fun z : ℝ => z ^ 2) ν := by simpa using hsqm.integrable_sq
  have hint : Integrable (id : ℝ → ℝ) ν := hsqm.integrable (by norm_num)
  have hpos : Integrable (fun z : ℝ => max z 0) ν := by
    refine hint.abs.mono' (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    rcases le_or_gt 0 z with hz | hz
    · rw [max_eq_left hz]
      simp
    · rw [max_eq_right (le_of_lt hz), abs_zero]
      simp
  refine ⟨fun φ hφ => ?_, fun ε hε => ?_⟩
  · exact Sandpile.d4_superdiffusive_first_clause hHeatKernel hVarScale hMembrane ν hprob
      hmean hvar hvar' θ₀ hθ₀ hexp hint hpos hD hw hα hs hφ
  · exact Sandpile.Support.d4_superdiffusive_tightness hHeatKernel hVarScale hMembrane ν hprob
      hmean hvar hvar' θ₀ hθ₀ hexp hint hpos hsq2 hD hw hα hs hε
