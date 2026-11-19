import LatticeProb.Prob.Blocks
import LatticeProb.Walk.Infinite

/-!
# Independence of disjoint increment blocks

Disjoint coordinate blocks of an independent increment sequence are mutually
independent. Any measurable functions of those blocks are independent as well.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.External.Stopping

/-- Restrictions of an i.i.d. field to pairwise disjoint sets are independent. -/
theorem iIndepFun_restrict_infinitePi {ι V α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (A : ι → Set V)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun (i : ι) (ω : V → α) => (A i).domRestrict ω)
      (Measure.infinitePi fun _ : V => ν) := by
  have hread : (Measure.infinitePi fun _ : V => ν).map
      (fun ω (p : (i : ι) × ↥(A i)) => ω (LatticeProb.blockIndex A p)) =
      Measure.infinitePi fun _ : (i : ι) × ↥(A i) => ν :=
    LatticeProb.infinitePi_map_comp' ν (LatticeProb.blockIndex A)
      (LatticeProb.blockIndex_injective A hdisj)
  have hblocks : (Measure.infinitePi fun _ : V => ν).map
      (fun ω i => (A i).domRestrict ω) =
      Measure.infinitePi fun i : ι => Measure.infinitePi fun _ : ↥(A i) => ν := by
    have hcomp : (fun (ω : V → α) (i : ι) => (A i).domRestrict ω) =
        ⇑(MeasurableEquiv.piCurry fun (_ : ι) (_ : ↥(A _)) => α) ∘
          (fun ω p => ω (LatticeProb.blockIndex A p)) := rfl
    rw [hcomp, ← Measure.map_map (MeasurableEquiv.piCurry _).measurable
      (Measurable.of_eval fun p => measurable_pi_apply (LatticeProb.blockIndex A p)),
      hread]
    exact Measure.infinitePi_map_piCurry (fun (i : ι) (_ : ↥(A i)) => (ν : Measure α))
  have hm : AEMeasurable (fun (ω : V → α) (i : ι) => (A i).domRestrict ω)
      (Measure.infinitePi fun _ : V => ν) := by
    refine (Measurable.of_eval fun i => ?_).aemeasurable
    exact Measurable.of_eval fun j => measurable_pi_apply (j : V)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀ hm, hblocks]
  congr 1
  funext i
  exact (Measure.infinitePi_map_restrict' (μ := fun _ : V => ν) (I := A i)).symm

/-- Measurable functions of disjoint coordinate blocks are independent. -/
theorem iIndepFun_of_disjoint_blocks {ι V α : Type*} [MeasurableSpace α]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (ν : Measure α) [IsProbabilityMeasure ν] (A : ι → Set V)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (f : (i : ι) → (A i → α) → β i) (hf : ∀ i, Measurable (f i)) :
    iIndepFun (fun i (ω : V → α) => f i ((A i).domRestrict ω))
      (Measure.infinitePi fun _ : V => ν) :=
  (iIndepFun_restrict_infinitePi ν A hdisj).comp f hf

end Sandpile.External.Stopping
