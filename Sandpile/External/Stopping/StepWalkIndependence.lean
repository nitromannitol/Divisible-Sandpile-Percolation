import Sandpile.External.Stopping.StepWalkDriverIndependence

/-!
# Independent increments under the site-walk law

The floor-time walk has independent increments under its own path law. This
transfers the disjoint-block proof from the i.i.d. driver to the measurable
image law of the walk.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Independence of a finite family descends through a measurable map. -/
theorem iIndepFun_map_of_comp {ι Ω Ξ E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (g : Ω → Ξ) (hg : Measurable g)
    (f : ι → Ξ → E) (hf : ∀ i, Measurable (f i))
    (hind : iIndepFun (fun i => f i ∘ g) μ) : iIndepFun f (μ.map g) := by
  let : IsProbabilityMeasure (μ.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have hsource := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hf i).comp hg).aemeasurable)).1 hind
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hf i).aemeasurable)).2
  calc
    (μ.map g).map (fun ω i => f i ω) =
        μ.map ((fun ω i => f i ω) ∘ g) :=
      Measure.map_map (measurable_pi_iff.2 hf) hg
    _ = Measure.pi (fun i => μ.map (f i ∘ g)) := hsource
    _ = Measure.pi (fun i => (μ.map g).map (f i)) := by
      congr 1
      funext i
      exact (Measure.map_map (hf i) hg).symm

/-- At a fixed time the step walk is measurable in the lattice path. -/
theorem measurable_stepWalk {d : ℕ} (R : ℝ) (t : ℝ≥0) :
    Measurable (stepWalk (d := d) R t) :=
  (measurable_of_countable (Lclt.scaledSite (d := d) R)).comp (measurable_pi_apply _)

/-- The step walk has independent increments under the site-walk law. -/
theorem hasIndepIncrements_stepWalk {d : ℕ} [NeZero d] (R : ℝ) (q : Site d) :
    HasIndepIncrements (stepWalk R) (walkLaw d q) := by
  intro n t ht
  change iIndepFun (fun (i : Fin n) X => stepWalk R (t i.succ) X - stepWalk R (t i.castSucc) X)
    ((LatticeProb.incPathLaw d).map (LatticeProb.sitePath q))
  apply iIndepFun_map_of_comp (LatticeProb.incPathLaw d) (LatticeProb.sitePath q)
    (LatticeProb.measurable_sitePath q)
  · intro i
    exact (measurable_stepWalk R (t i.succ)).sub (measurable_stepWalk R (t i.castSucc))
  · exact hasIndepIncrements_stepWalk_driver R q n t ht

/-- The diffusively time-scaled step walk has independent increments. -/
theorem hasIndepIncrements_diffusiveStepWalk {d : ℕ} [NeZero d] (R : ℝ) (q : Site d) :
    HasIndepIncrements (diffusiveStepWalk R) (walkLaw d q) := by
  intro n t ht
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hm : Monotone (fun i => c * t i) := fun i j hij =>
    mul_le_mul_of_nonneg_left (ht hij) (zero_le : 0 ≤ c)
  exact hasIndepIncrements_stepWalk R q n (fun i => c * t i) hm

end Sandpile.External.Stopping
