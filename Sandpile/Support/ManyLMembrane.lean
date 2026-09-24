/-
The assembly of `thm:dgt4-diffusive-membrane` (`sandpile.tex:4616-4639`).

The paper's proof (`sandpile.tex:4639-4691`) is two displays: the contact
asymptotics `P(u_n(0)=0) ~ G(0,0)κ/n` of `prop:dgt4-contact-asymptotics`, and
the linearization `prop:dgt4-linearization` together with
`prop:weighted-membrane-limit` at the weight `q(r) = (1-r/T)^κ`.  The first is
the theorem's second conjunct; the second is the convergence in
`H^{-s}_loc(ℝ^d)`.

`Sandpile.Support.dgt4_diffusive_membrane_of` (`Support/ContDGT4Membrane.lean`)
already proves the convergence from the linearization, the weighted membrane
limit and the odometer tightness.  The theorem below is the whole node: it
discharges the linearization and the contact asymptotics from the two frozen
dgt4 inputs of the same name, so the node follows by this one application the
moment those two land.
-/
import Sandpile.Support.ContDGT4Membrane
import Sandpile.Frozen.DGT4Linearization
import Sandpile.External.NormalComparison
import Sandpile.External.IntersectionSecondMoment
import Sandpile.Frozen.DGT4ContactAsymptotics

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- **`thm:dgt4-diffusive-membrane` from the two frozen dgt4 inputs.**  The
linearization `prop:dgt4-linearization` supplies the hypothesis of
`dgt4_diffusive_membrane_of`, which carries the weighted membrane limit and the
tightness; the contact asymptotics `prop:dgt4-contact-asymptotics` is the
theorem's second conjunct verbatim.  The only work is that the linearization is
stated for the paper's case dichotomy, which pins `κ > 0`, while the assembly
needs `0 ≤ κ`. -/
theorem dgt4_diffusive_membrane_of_inputs
    (hHeatKernel : Sandpile.External.HeatKernelBounds)
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (hNormal : Sandpile.External.NormalComparison)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (hLocalCLT : Sandpile.External.LocalCLT)
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
            (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1) := by
  have hκ : 0 ≤ κ := by
    rcases hcase with ⟨-, hκ1⟩ | ⟨α, hα, ⟨M, hM⟩, hlam, hκ2⟩
    · rw [hκ1]; norm_num
    · rw [hκ2]
      have h1 : 1 / α < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
  refine ⟨fun T hT s hs => ?_, ?_⟩
  · exact dgt4_diffusive_membrane_of hHeatKernel hGreenHigh hLocalCLT hBesov hd ν hmean hvar
      hvar' κ hκ T hT
      (fun φ hφ => Sandpile.Frozen.dgt4_linearization hGreenHigh hGaussConc hNormal hInter d hd hBesov ν hatom hmean hvar
        hvar' κ hcase
        T hT φ hφ) s hs
  · exact Sandpile.Frozen.dgt4_contact_asymptotics hGreenHigh hGaussConc d hd ν hatom hmean hvar hvar'
      κ hcase

end Sandpile.Support
