import Sandpile.Support.Dgt4MeanDiv
import Sandpile.Support.Dgt4ABandTau
import Sandpile.Support.Dgt4ABandParameters

/-!
# Divergence of the Frozen Mean Level

The frozen mean level diverges, and the hitting index of the band exists.

`b_n = E u_n(0) / G(0,0)` is the frozen mean level. The crude lower bound on the
mean odometer makes it diverge, so for every band scale the level eventually
reaches the middle of the band, and the hitting index `τ_k` is well defined.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- **The frozen mean level diverges.**  `E u_n(0)` grows without bound, and
`G(0,0)` is a positive constant, so the level `b_n = E u_n(0)/G(0,0)` diverges. -/
theorem tendsto_bandLevel_atTop (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) :
    Tendsto (fun n : ℕ => meanOdometer (centeredMassLaw d ν) n / green d 0 0)
      atTop atTop := by
  have hG : 0 < green d 0 0 := zero_lt_one.trans_le (one_le_green (by omega))
  exact (tendsto_meanOdometer_atTop hd ν hint hmean hnondeg).atTop_div_const hG

/-- **The hitting index exists.**  The level reaches the middle of the `k`-th
band, which is what `bandProfile_hitting_le` needs to define `τ_k`. -/
theorem bandHitting_exists_sandpile (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) (k : ℕ) :
    ∃ n : ℕ, P.level k - (1 - P.l1) * P.level k / 2
      ≤ meanOdometer (centeredMassLaw d ν) n / green d 0 0 :=
  bandHitting_exists _ _ (tendsto_bandLevel_atTop hd ν hint hmean hnondeg)

end Sandpile.Support
