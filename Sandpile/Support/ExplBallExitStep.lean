/-
The strong Markov step of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the strong Markov property at the exit time of the ball and the polynomial
growth of the field.

The strong Markov property at the exit time is the External
`Sandpile.External.BrownianExitStep`; the polynomial growth of the field supplies
the integrability of the two stopped rewards through the envelope of the motion.
Together they give `BallStepResidual`, the one estimate the reduction of the lemma
leaves open.
-/
import Sandpile.Support.ExplBallConditional
import Sandpile.Support.ExplBallFarUniform
import Sandpile.Support.ExplBrownianEnvelope
import Sandpile.External.BrownianExitStep

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- The strong Markov step residual of `lem:brownian-ball-localization` from the strong Markov
property at the exit time of the ball and the polynomial growth of the field. -/
theorem ballStepResidual_of_exitStep (d : ℕ)
    (hExit : Sandpile.External.BrownianExitStep) (hgrowth : BallGrowthResidual d) :
    BallStepResidual d := by
  refine ballStepResidual_of_growth_and_conditional d hgrowth ?_
  intro ΩW mΩW PW hPW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB mΩB PB hPB B hBrown hcont hmeas
  filter_upwards [hc T hT] with ω hcω
  intro u hu τ hτ hbound
  exact hExit d ΩB PB B hBrown hcont hmeas T hT (fun t z => Z t z ω) hcω A hA K hK u hu τ hτ hbound

end Sandpile.Continuum
