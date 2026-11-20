import Sandpile.Support.D4MembraneAssembly
import Sandpile.Support.D4MembraneRieszCovariance
import Sandpile.External.PairedLocalCLTFourProved

/-!
# Four-dimensional membrane scaling

The scalar convergence and the uniform negative Sobolev norm bound hold for
the whole-space membrane representative under the stated coefficient defect
condition.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.External

/-- The four-dimensional membrane scaling input holds. -/
theorem membraneScalingLimitFour_holds : MembraneScalingLimitFour := by
  apply Sandpile.Support.membraneScalingLimitFour_of_local_covariance
  intro ν hprob _ hvariance D w hw T χ hχ β hβ _
  let : IsProbabilityMeasure ν := hprob
  have hsq : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvariance
  obtain ⟨K, hK, hcov⟩ :=
    Sandpile.Support.exists_membrane_omegaEmbed_riesz_covariance_bound
      pairedLocalCLTFour ν hsq D w hw χ hχ β hβ
  exact ⟨K, hK, fun R hR => hcov (T R) R hR⟩

end Sandpile.External
