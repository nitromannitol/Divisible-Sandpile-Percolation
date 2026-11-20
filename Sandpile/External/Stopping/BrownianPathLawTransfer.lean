import Sandpile.External.Stopping.CenteredWalkCoupling

/-!
# Brownian coordinates under a change of path realization

A measurable path observable with Brownian law remains Brownian when the
underlying path is replaced by another random element with the same law.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Sandpile.External.Stopping

/-- A continuous real-valued path observable has Brownian law under any
realization of the same underlying path law. -/
theorem isBrownianReal_of_same_path_law
    {S Ω Ω' : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {F : Ω → S} {Y : Ω' → S}
    (hFm : Measurable F) (hYm : Measurable Y) (hmap : Q.map Y = P.map F)
    (φ : S → ℝ≥0 → ℝ) (hφm : ∀ t, Measurable (fun s => φ s t))
    (hφc : ∀ s, Continuous (φ s))
    (hB : IsBrownianReal (fun t ω => φ (F ω) t) P) :
    IsBrownianReal (fun t ω => φ (Y ω) t) Q where
  toIsPreBrownianReal := by
    refine ⟨fun I => ?_⟩
    let g : S → (I → ℝ) := fun s i => φ s i
    have hgm : Measurable g := measurable_pi_iff.2 fun i => hφm i
    have hF : HasLaw F (P.map F) P := hasLaw_map hFm.aemeasurable
    have hY : HasLaw Y (P.map F) Q := ⟨hYm.aemeasurable, hmap⟩
    have hsource : HasLaw (fun ω => g (F ω)) (ProbabilityTheory.BrownianReal.projectiveFamily I) P := hB.hasLaw I
    change HasLaw (fun ω => g (Y ω)) (ProbabilityTheory.BrownianReal.projectiveFamily I) Q
    exact HasLaw.comp_of_hasLaw_comp (f := g) hgm.aemeasurable hF hY hsource
  cont := Filter.Eventually.of_forall fun ω => hφc (Y ω)

end Sandpile.External.Stopping
