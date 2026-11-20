import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Independence.Basic

/-!
# Independence under weak convergence

A weak limit of joint probability laws with independent coordinates retains
independence. This is used for future increments in the filtration-convergence
argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace

namespace Sandpile.External.Stopping

/-- Independence of two coordinates is preserved by weak convergence of
their joint laws. -/
theorem indepFun_fst_snd_of_weak_limit
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [PseudoMetrizableSpace E] [PseudoMetrizableSpace F]
    (μ : ℕ → ProbabilityMeasure (E × F)) (ν : ProbabilityMeasure (E × F))
    (hlim : Tendsto μ atTop (𝓝 ν))
    (hindep : ∀ n, IndepFun (Prod.fst : E × F → E) Prod.snd (μ n : Measure (E × F))) :
    IndepFun (Prod.fst : E × F → E) Prod.snd (ν : Measure (E × F)) := by
  have hfst := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hlim
    (f := (Prod.fst : E × F → E)) continuous_fst
  have hsnd := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hlim
    (f := (Prod.snd : E × F → F)) continuous_snd
  have hprod := (ProbabilityMeasure.continuous_prod.tendsto
    (ν.map Prod.fst, ν.map Prod.snd)).comp (hfst.prodMk_nhds hsnd)
  have hseq : (fun n => ((μ n).map Prod.fst).prod ((μ n).map Prod.snd)) = μ := by
    funext n
    apply Subtype.ext
    change ((μ n : Measure (E × F)).map Prod.fst).prod
      ((μ n : Measure (E × F)).map Prod.snd) = (μ n : Measure (E × F))
    have h := (indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable).1 (hindep n)
    simpa only [Prod.mk.eta, Measure.map_id'] using h.symm
  change Tendsto (fun n => ((μ n).map Prod.fst).prod ((μ n).map Prod.snd)) atTop
    (𝓝 ((ν.map Prod.fst).prod (ν.map Prod.snd))) at hprod
  rw [hseq] at hprod
  have heq : ν = (ν.map Prod.fst).prod (ν.map Prod.snd) :=
    tendsto_nhds_unique hlim hprod
  apply (indepFun_iff_map_prod_eq_prod_map_map
    measurable_fst.aemeasurable measurable_snd.aemeasurable).2
  have hm : (ν : Measure (E × F)) =
      ((ν : Measure (E × F)).map Prod.fst).prod ((ν : Measure (E × F)).map Prod.snd) :=
    congrArg (fun p : ProbabilityMeasure (E × F) => (p : Measure (E × F))) heq
  simpa only [Prod.mk.eta, Measure.map_id'] using hm

end Sandpile.External.Stopping
