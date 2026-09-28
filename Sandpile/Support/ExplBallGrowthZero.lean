import Sandpile.Support.ExplBallFinal

/-!
# The growth residual in dimension zero

`Sandpile.Continuum.ballGrowthResidual_zero` establishes `BallGrowthResidual 0`: in dimension
zero `Space 0` is a single point, so a continuous field on a compact time strip is automatically
bounded above by its supremum there, and the samplewise polynomial growth bound the residual asks
for holds with exponent `p = 0` and constant that supremum norm.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- In dimension zero the space is a single point, so the continuous field on a strip is
bounded by its supremum there and the growth residual holds with exponent zero. -/
theorem ballGrowthResidual_zero : BallGrowthResidual 0 := by
  intro ΩW _ PW _ W hW ν2 hν2 Z hmod hc T hT
  filter_upwards [hc T hT] with ω hcω
  have hcont : ContinuousOn (fun p : ℝ × Space 0 => ‖Z p.1 p.2 ω‖)
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space 0))) := hcω.norm
  have hK : IsCompact (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space 0))) :=
    isCompact_Icc.prod isCompact_univ
  have hbdd : BddAbove ((fun p : ℝ × Space 0 => ‖Z p.1 p.2 ω‖) ''
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space 0)))) :=
    (hK.image_of_continuousOn hcont).bddAbove
  refine ⟨sSup ((fun p : ℝ × Space 0 => ‖Z p.1 p.2 ω‖) ''
      (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space 0)))), ?_, 0, ?_⟩
  · have hmem : ‖Z 0 (0 : Space 0) ω‖ ∈
        (fun p : ℝ × Space 0 => ‖Z p.1 p.2 ω‖) ''
          (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space 0))) :=
      ⟨(0, (0 : Space 0)), by simp [hT.le]⟩
    exact le_trans (norm_nonneg _) (le_csSup hbdd hmem)
  · intro v hv y
    have hmem : ‖Z (v:ℝ) y ω‖ ∈
        (fun p : ℝ × Space 0 => ‖Z p.1 p.2 ω‖) ''
          (Set.Icc (0:ℝ) T ×ˢ (Set.univ : Set (Space 0))) :=
      ⟨((v:ℝ), y), by simp [v.coe_nonneg, hv]⟩
    have := le_csSup hbdd hmem
    simpa using this

end Sandpile.Continuum
