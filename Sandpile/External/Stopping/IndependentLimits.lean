import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Independence.InfinitePi

/-!
# Joint limits of independent random variables

For a finite family of independent random variables, marginal convergence in
law implies joint convergence when the limiting variables are independent.
The proof uses continuity of finite products of probability measures.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace

namespace Sandpile.External.Stopping

/-- Marginal convergence and independence imply joint convergence for a finite family. -/
theorem tendstoInDistribution_pi_of_independent {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] [∀ i, PseudoMetrizableSpace (E i)]
    [∀ i, OpensMeasurableSpace (E i)]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ω' : Type*} [MeasurableSpace Ω']
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : (n : ℕ) → (i : ι) → Ω n → E i) (Y : (i : ι) → Ω' → E i)
    (hX : ∀ n, iIndepFun (X n) (P n)) (hY : iIndepFun Y Q)
    (h : ∀ i, TendstoInDistribution (fun n => X n i) atTop (Y i) P Q) :
    TendstoInDistribution (fun n ω i => X n i ω) atTop (fun ω i => Y i ω) P Q := by
  have hm (n : ℕ) : AEMeasurable (fun ω i => X n i ω) (P n) :=
    AEMeasurable.of_eval fun i => (h i).forall_aemeasurable n
  have hm' : AEMeasurable (fun ω i => Y i ω) Q :=
    AEMeasurable.of_eval fun i => (h i).aemeasurable_limit
  let μ : (n : ℕ) → (i : ι) → ProbabilityMeasure (E i) := fun n i =>
    ⟨(P n).map (X n i), (Measure.isProbabilityMeasure_map_iff
      ((h i).forall_aemeasurable n)).2 inferInstance⟩
  let ν : (i : ι) → ProbabilityMeasure (E i) := fun i =>
    ⟨Q.map (Y i), (Measure.isProbabilityMeasure_map_iff
      ((h i).aemeasurable_limit)).2 inferInstance⟩
  have ht : Tendsto μ atTop (𝓝 ν) := tendsto_pi_nhds.mpr fun i => (h i).tendsto
  have hp := (ProbabilityMeasure.continuous_pi.tendsto ν).comp ht
  refine ⟨hm, hm', ?_⟩
  have hmap (n : ℕ) : (P n).map (fun ω i => X n i ω) =
      Measure.pi (fun i => (P n).map (X n i)) :=
    ((iIndepFun_iff_map_fun_eq_pi_map fun i => (h i).forall_aemeasurable n).mp (hX n))
  have hmap' : Q.map (fun ω i => Y i ω) = Measure.pi (fun i => Q.map (Y i)) :=
    ((iIndepFun_iff_map_fun_eq_pi_map fun i => (h i).aemeasurable_limit).mp hY)
  have hlimit : (⟨Q.map (fun ω i => Y i ω), inferInstance⟩ :
      ProbabilityMeasure ((i : ι) → E i)) = ProbabilityMeasure.pi ν :=
    Subtype.ext hmap'
  rw [hlimit]
  apply Filter.Tendsto.congr (fun n => ?_) hp
  exact Subtype.ext (hmap n).symm

end Sandpile.External.Stopping
