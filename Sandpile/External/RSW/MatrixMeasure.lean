import Sandpile.External.RSW.ScaleComposition

/-!
# Symmetry of finite product laws

A finite matrix of independent identically distributed entries has the same law after
transposition.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile.External.RSW

/-- Transposing a finite matrix preserves the independent identical product law. -/
theorem measurePreserving_matrix_transpose {ι : Type*} [Fintype ι]
    (ν : Measure Bool) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun ω : ι → ι → Bool => fun i j => ω j i)
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => ν)
      (Measure.pi fun _ : ι => Measure.pi fun _ : ι => ν) := by
  classical
  let T : (ι → ι → Bool) → (ι → ι → Bool) := fun ω i j => ω j i
  have hm : Measurable T := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply i).comp (measurable_pi_apply j)
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.map_apply hm (measurableSet_singleton ω)]
  have he : T ⁻¹' {ω} = {T ω} := by
    ext η
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      funext i j
      have hh := congrFun (congrFun h j) i
      exact hh
    · intro h
      subst η
      funext i j
      rfl
  rw [he]
  simp only [Measure.pi_singleton]
  exact Finset.prod_comm

end Sandpile.External.RSW
