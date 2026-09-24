/-
Finite-coordinate measurability and independence of low-field events
that read disjoint blocks of scenery.
-/
import Sandpile.Support.FiniteKernelTail
import LatticeProb.Prob.Blocks

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace Sandpile

lemma measurable_finiteKernelField_restrict {d : ℕ} (h : Site d → ℝ) (z : Site d)
    (A : Finset (Site d)) (hA : ∀ y ∉ A, h (y - z) = 0) :
    Measurable[MeasurableSpace.comap (Set.restrict (A : Set (Site d))) inferInstance]
      (fun ζ : Site d → ℝ => finiteKernelField h ζ z) := by
  have he (ζ : Site d → ℝ) : finiteKernelField h ζ z = ∑ y ∈ A, h (y - z) * ζ y := by
    rw [finiteKernelField_eq_tsum_translated]
    exact tsum_eq_sum (fun y hy => by rw [hA y hy, zero_mul])
  apply measurable_restrict_of_congr (A : Set (Site d))
  · simp only [he]
    exact Finset.measurable_sum _ (fun y _ => measurable_const.mul (measurable_pi_apply y))
  · intro ζ ξ hζξ
    rw [he, he]
    exact Finset.sum_congr rfl (fun y hy => by rw [hζξ y hy])

def kernelLowEvent {d : ℕ} (h : Site d → ℝ) (S : Finset (Site d)) (level : ℝ) : Set (Site d → ℝ) :=
  {ζ | ∃ z ∈ S, finiteKernelField h ζ z ≤ level}

lemma measurableSet_kernelLowEvent_restrict {d : ℕ} (h : Site d → ℝ)
    (S A : Finset (Site d)) (hA : ∀ z ∈ S, ∀ y ∉ A, h (y - z) = 0) (level : ℝ) :
    MeasurableSet[MeasurableSpace.comap (Set.restrict (A : Set (Site d))) inferInstance]
      (kernelLowEvent h S level) := by
  have he : kernelLowEvent h S level = ⋃ z ∈ S, {ζ | finiteKernelField h ζ z ≤ level} := by
    ext ζ
    simp only [kernelLowEvent, mem_setOf_eq, mem_iUnion, exists_prop]
  rw [he]
  exact MeasurableSet.biUnion S.countable_toSet (fun z hz =>
    measurableSet_le (measurable_finiteKernelField_restrict h z A (hA z hz)) measurable_const)

lemma kernelLowEvent_inter_eq_prod {d : ℕ} {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Site d → ℝ) (S A : ι → Finset (Site d))
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => (A i : Set (Site d)))))
    (hA : ∀ i z, z ∈ S i → ∀ y ∉ A i, h (y - z) = 0) (level : ℝ) (s : Finset ι) :
    (LatticeProb.iidLaw d μ) {ζ | ∀ i ∈ s, ζ ∈ kernelLowEvent h (S i) level} =
      ∏ i ∈ s, (LatticeProb.iidLaw d μ) (kernelLowEvent h (S i) level) := by
  have hi := LatticeProb.iIndep_comap_of_pairwise_disjoint μ
    (fun i => (A i : Set (Site d))) hdisj
  have he : {ζ | ∀ i ∈ s, ζ ∈ kernelLowEvent h (S i) level} = ⋂ i ∈ s, kernelLowEvent h (S i) level := by
    ext ζ
    simp only [mem_setOf_eq, mem_iInter]
  rw [he]
  exact hi.meas_biInter (fun i _ => measurableSet_kernelLowEvent_restrict h (S i) (A i) (hA i) level)

lemma kernelLowEvent_inter_le_pow {d : ℕ} {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Site d → ℝ) (S A : ι → Finset (Site d))
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => (A i : Set (Site d)))))
    (hA : ∀ i z, z ∈ S i → ∀ y ∉ A i, h (y - z) = 0) (level : ℝ) (s : Finset ι)
    {p : ℝ≥0∞} (hp : ∀ i ∈ s, (LatticeProb.iidLaw d μ) (kernelLowEvent h (S i) level) ≤ p) :
    (LatticeProb.iidLaw d μ) {ζ | ∀ i ∈ s, ζ ∈ kernelLowEvent h (S i) level} ≤ p ^ s.card := by
  rw [kernelLowEvent_inter_eq_prod μ h S A hdisj hA level s]
  calc
    _ ≤ ∏ _i ∈ s, p := Finset.prod_le_prod (fun _ _ => bot_le) hp
    _ = _ := Finset.prod_const p

end Sandpile
