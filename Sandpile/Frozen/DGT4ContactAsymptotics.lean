import Sandpile.Law
import Sandpile.Walk
import Sandpile.External.GreenBoundsHigh
import Sandpile.External.GaussianLipschitzConcentration
import Sandpile.Support.Dgt4AFinal

/-!
# Contact-probability asymptotics above dimension four

This file proves the frozen statement of `prop:dgt4-contact-asymptotics` (`sandpile.tex:4894-4896`):
for `d ≥ 5` and scenery `ζ` i.i.d., atomless, centered, of finite positive variance, and either
Gaussian (`κ = 1`) or bounded above with a regularly varying lower tail of index `-α`, `α > 2`
(`κ = 1 - 1/α`), the probability that the odometer at the origin vanishes at time `n` is
asymptotic to `G(0,0) κ / n`. The scenery is carried in the mass normalization, so `u_n(0)` is
`Sandpile.odometer σ n 0` for `σ` of law `Sandpile.centeredMassLaw d ν`. The proof of the two cases
cites Borell's and Tsirelson-Ibragimov-Sudakov's Gaussian concentration inequality for the
Lipschitz functional `Θ_n` of `sandpile.tex:5267-5271` as the explicit hypothesis `hGaussConc`,
and draws throughout on the `d ≥ 5` Green estimates.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_contact_asymptotics
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
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
    Tendsto (fun n : ℕ =>
        ((Sandpile.centeredMassLaw d ν) {σ | Sandpile.odometer σ n 0 = 0}).toReal /
          (Sandpile.green d 0 0 * κ / n)) atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= by
  have hGreenHigh : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  exact Sandpile.dgt4_contact_asymptotics_of_hcase hGreenHigh hGaussConc d hd ν hatom hmean hvar
    hvar' κ hcase
