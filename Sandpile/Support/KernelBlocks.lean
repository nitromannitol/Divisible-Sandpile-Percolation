import Sandpile.Support.FiniteKernelTail
import LatticeProb.Prob.Blocks

/-!
# Independence of low-field events reading disjoint blocks of scenery

Shows that the event `finiteKernelField h ζ z ≤ level`, and hence the event `kernelLowEvent h S
level` that some site of a finite set `S` sees a low field, is measurable with respect to the
scenery values on a finite block `A` when `h (y - z) = 0` for every `y` outside `A`. When the
blocks attached to a pairwise disjoint family of index sets are themselves pairwise disjoint,
the corresponding low-field events are independent under `LatticeProb.iidLaw`, which turns a
uniform bound `p` on each individual probability into the power bound `p ^ s.card` on their
simultaneous occurrence over any finite index set `s`.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace Sandpile

/-- The field `finiteKernelField h ζ z`, as a function of the scenery `ζ`, is measurable with
respect to the coordinates in a finite set `A`, provided `h (y - z) = 0` for every `y ∉ A`; it
then equals the finite sum `∑ y ∈ A, h (y - z) * ζ y`, which depends only on `ζ`'s restriction
to `A`. -/
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

/-- The event that some site of `S` sees a field, under `finiteKernelField h`, at most
`level`. -/
def kernelLowEvent {d : ℕ} (h : Site d → ℝ) (S : Finset (Site d)) (level : ℝ) : Set (Site d → ℝ) :=
  {ζ | ∃ z ∈ S, finiteKernelField h ζ z ≤ level}

/-- `kernelLowEvent h S level` is measurable with respect to the coordinates in a finite set
`A`, provided every site `z ∈ S` has `h (y - z) = 0` for all `y ∉ A`, since it is a finite union
over `S` of the measurable sets `measurable_finiteKernelField_restrict` produces. -/
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

/-- If the finite blocks `A i` attached to a pairwise disjoint family of index sets `i` are
themselves pairwise disjoint, the low-field events `kernelLowEvent h (S i) level` are
independent under the i.i.d. law `LatticeProb.iidLaw d μ`: the probability that all of them
occur, over any finite index set `s`, is the product of their individual probabilities. -/
lemma kernelLowEvent_inter_eq_prod {d : ℕ} {ι : Type*} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : Site d → ℝ) (S A : ι → Finset (Site d))
    (hdisj : Pairwise (Function.onFun Disjoint (fun i => (A i : Set (Site d)))))
    (hA : ∀ i z, z ∈ S i → ∀ y ∉ A i, h (y - z) = 0) (level : ℝ) (s : Finset ι) :
    (LatticeProb.iidLaw d μ) {ζ | ∀ i ∈ s, ζ ∈ kernelLowEvent h (S i) level} =
      ∏ i ∈ s, (LatticeProb.iidLaw d μ) (kernelLowEvent h (S i) level) := by
  have hi := LatticeProb.iIndep_comap_of_pairwise_disjoint μ
    (fun i => (A i : Set (Site d))) hdisj
  have he : {ζ | ∀ i ∈ s, ζ ∈ kernelLowEvent h (S i) level}
    = ⋂ i ∈ s, kernelLowEvent h (S i) level := by
    ext ζ
    simp only [mem_setOf_eq, mem_iInter]
  rw [he]
  exact hi.meas_biInter
    (fun i _ => measurableSet_kernelLowEvent_restrict h (S i) (A i) (hA i) level)

/-- Under the same block-disjointness hypothesis as `kernelLowEvent_inter_eq_prod`, if each
individual low-field probability is at most `p`, the probability that the event occurs at every
index in a finite set `s` is at most `p ^ s.card`. -/
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
