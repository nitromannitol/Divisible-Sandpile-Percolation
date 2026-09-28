import Sandpile.Support.OriginProfile

/-!
# Divergence of the mean odometer

Two facts about the scenery law and the mean odometer that both proofs of
`prop:dgt4-contact-asymptotics` open with. Case (a) uses `E u_n(0) → ∞` through
`eq:dgt4-gaussian-height-order` (`sandpile.tex:5033`), and case (b) states it outright: "By Part
(i) of Corollary~\ref{cor:dgt4-mean-lower}, `E u_n(0) → ∞`" (`sandpile.tex:5309`). The corollary
is sealed, and its nondegeneracy hypothesis is supplied by the atomlessness of the scenery law.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- An atomless probability measure is not a Dirac mass, which is the
nondegeneracy hypothesis of `cor:dgt4-mean-lower`. -/
theorem ne_dirac_of_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) : ∀ z : ℝ, ν ≠ Measure.dirac z := by
  intro z hz
  have h1 : ν {z} = 0 := hatom z
  rw [hz, Measure.dirac_apply' z (measurableSet_singleton z)] at h1
  simp at h1

/-- Part (i) of `cor:dgt4-mean-lower`: the mean odometer at the origin diverges. -/
theorem tendsto_meanOdometer_atTop {d : ℕ} (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z) :
    Tendsto (fun n : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n)
      atTop atTop := by
  obtain ⟨c, hc, t₀, hl⟩ :=
    (Sandpile.Frozen.dgt4_mean_lower d hd).1 ν inferInstance hint hmean hnondeg
  exact tendsto_atTop_of_log_lower hc (by positivity : (0 : ℝ) < 2 / d) hl

end Sandpile
