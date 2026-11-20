import Sandpile.External.Stopping.IndependentWeakLimits

/-!
# Independent observations under weak convergence

Continuous observations of weakly convergent probability laws retain
independence in the limit. This is the continuous mapping step in the
filtration-convergence argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace

namespace Sandpile.External.Stopping

/-- Independence of continuous observations passes to a weak limit. -/
theorem indepFun_of_weak_limit_of_continuous
    {S E F : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace E] [TopologicalSpace F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [PseudoMetrizableSpace E] [PseudoMetrizableSpace F]
    (μ : ℕ → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (hlim : Tendsto μ atTop (𝓝 ν)) (f : S → E) (g : S → F)
    (hf : Continuous f) (hg : Continuous g)
    (hindep : ∀ n, IndepFun f g (μ n : Measure S)) :
    IndepFun f g (ν : Measure S) := by
  let h : S → E × F := fun x => (f x, g x)
  have hh : Continuous h := hf.prodMk hg
  let η : ℕ → ProbabilityMeasure (E × F) := fun n => (μ n).map h
  let κ : ProbabilityMeasure (E × F) := ν.map h
  have hconv : Tendsto η atTop (𝓝 κ) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hlim hh
  have hind (n : ℕ) : IndepFun (Prod.fst : E × F → E) Prod.snd (η n : Measure (E × F)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable).2
    have hi := (indepFun_iff_map_prod_eq_prod_map_map hf.measurable.aemeasurable
      hg.measurable.aemeasurable).1 (hindep n)
    change ((μ n : Measure S).map h).map (fun p => (p.1, p.2)) =
      (((μ n : Measure S).map h).map Prod.fst).prod
        (((μ n : Measure S).map h).map Prod.snd)
    rw [Measure.map_map (measurable_fst.prodMk measurable_snd) hh.measurable,
      Measure.map_map measurable_fst hh.measurable, Measure.map_map measurable_snd hh.measurable]
    exact hi
  have hk := indepFun_fst_snd_of_weak_limit η κ hconv hind
  have hk' := (indepFun_iff_map_prod_eq_prod_map_map
    measurable_fst.aemeasurable measurable_snd.aemeasurable).1 hk
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.measurable.aemeasurable
    hg.measurable.aemeasurable).2
  change ((ν : Measure S).map h).map (fun p => (p.1, p.2)) =
    (((ν : Measure S).map h).map Prod.fst).prod
      (((ν : Measure S).map h).map Prod.snd) at hk'
  rw [Measure.map_map (measurable_fst.prodMk measurable_snd) hh.measurable,
    Measure.map_map measurable_fst hh.measurable, Measure.map_map measurable_snd hh.measurable] at hk'
  exact hk'

end Sandpile.External.Stopping
