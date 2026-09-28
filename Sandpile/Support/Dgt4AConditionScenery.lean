import Sandpile.Support.Dgt4ACondition
import Sandpile.Support.LinGaussBridge
import Sandpile.Support.SceneryBridge

/-!
# The conditioning carried to the scenery and to the mass configuration

The conditioning of `Support/Dgt4ACondition.lean` carried to the scenery and to the mass
configuration, which is where Steps 2 to 4 of case (a) read it.

`map_scenery_centeredMassLaw` and `iidLaw_gaussianReal_eq_map` write the law of the scenery as
the image of the standard Gaussian product under the scaling `\omega\mapsto\sqrt v\omega`, so
the splitting `\omega=\xi(\omega)e+\rho(\omega)` of `Support/Dgt4ACondition.lean` becomes the
splitting of the scenery

  `\zeta(z)=\sqrt v\,(r(z)+s\,e(z))`,   `s` standard Gaussian, `r` the residual field,

with `s` and `r` independent. Since `V_\infty(0)=\sqrt v\|G(0,\cdot)\|\,\xi`, fixing `s` fixes
`-V_\infty(0)`, and the three theorems below, `measure_iidLaw_gauss_shift`,
`integral_iidLaw_gauss_shift`, and `measure_centeredMassLaw_gauss_shift`, are the paper's
conditioning on `-V_\infty(0)` at `sandpile.tex:5105-5109` for probabilities, for means, and
for the events of the mass configuration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **The conditioning on the scenery, for probabilities.** -/
theorem measure_iidLaw_gauss_shift (hd : 5 ≤ d) (v : ℝ≥0) {A : Set (Site d → ℝ)}
    (hA : MeasurableSet A) :
    LatticeProb.iidLaw d (gaussianReal 0 v) A
      = ∫⁻ s, ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
          {r | (fun z => Real.sqrt (v : ℝ) * (r z + s * (greenUnit d hd : Site d → ℝ) z)) ∈ A}
        ∂(gaussianReal 0 1) := by
  have hS : Measurable (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z) := by
    fun_prop
  rw [iidLaw_gaussianReal_eq_map d v, Measure.map_apply hS hA,
    measure_gaussLaw_shift hd (hS hA)]
  rfl

/-- **The conditioning on the scenery, for means.**  The inner integral is the paper's
conditional expectation given `-V_\infty(0)`. -/
theorem integral_iidLaw_gauss_shift (hd : 5 ≤ d) (v : ℝ≥0) (F : (Site d → ℝ) → ℝ)
    (hF : Integrable F (LatticeProb.iidLaw d (gaussianReal 0 v))) :
    (∫ ζ, F ζ ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = ∫ s, (∫ r, F (fun z => Real.sqrt (v : ℝ) * (r z + s * (greenUnit d hd : Site d → ℝ) z))
          ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) ∂(gaussianReal 0 1) := by
  have hS : Measurable (fun (ω : Site d → ℝ) (z : Site d) => Real.sqrt (v : ℝ) * ω z) := by
    fun_prop
  rw [iidLaw_gaussianReal_eq_map d v] at hF ⊢
  rw [integral_map hS.aemeasurable hF.1]
  exact integral_gaussLaw_shift hd _ ((integrable_map_measure hF.1 hS.aemeasurable).mp hF)

/-- **The conditioning on the mass configuration.**  Every event of
`ThresholdRelativeError` is an event of the scenery, so this is the form Steps 2 to 4
use. -/
theorem measure_centeredMassLaw_gauss_shift (hd : 5 ≤ d) (v : ℝ≥0) {A : Set (Site d → ℝ)}
    (hA : MeasurableSet A) :
    (centeredMassLaw d (gaussianReal 0 v)) (Sandpile.scenery d ⁻¹' A)
      = ∫⁻ s, ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
          {r | (fun z => Real.sqrt (v : ℝ) * (r z + s * (greenUnit d hd : Site d → ℝ) z)) ∈ A}
        ∂(gaussianReal 0 1) := by
  rw [← Measure.map_apply (measurable_scenery d) hA,
    map_scenery_centeredMassLaw d (gaussianReal 0 v) (by omega),
    measure_iidLaw_gauss_shift hd v hA]

end Sandpile
