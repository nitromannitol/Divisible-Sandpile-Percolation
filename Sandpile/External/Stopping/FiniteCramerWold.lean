import LatticeProb.Prob.CramerWold

/-!
# Cramér–Wold on finite product spaces

Finite-dimensional convergence in a real product space follows from the
convergence of all scalar linear combinations of its coordinates.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace Sandpile.External.Stopping

/-- Cramér–Wold for a real product indexed by any finite type. -/
theorem tendstoInDistribution_fintype_of_forall_dot {ι : Type*} [Fintype ι]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (X : ℕ → Ω → (ι → ℝ)) (Z : Ω' → (ι → ℝ)) (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z Q)
    (h : ∀ t : ι → ℝ, TendstoInDistribution
      (fun n ω => ∑ i, X n ω i * t i) atTop
      (fun ω => ∑ i, Z ω i * t i) (fun _ => P) Q) :
    TendstoInDistribution X atTop Z (fun _ => P) Q := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) := EuclideanSpace.equiv ι ℝ
  have key : TendstoInDistribution (fun n ω => e.symm (X n ω)) atTop
      (fun ω => e.symm (Z ω)) (fun _ => P) Q := by
    refine LatticeProb.CramerWold.tendstoInDistribution_of_forall_inner _ _ P Q
      (fun n => e.symm.continuous.measurable.comp_aemeasurable (hX n))
      (e.symm.continuous.measurable.comp_aemeasurable hZ) ?_
    intro t
    have ht := h (e t)
    have h1 : (fun n ω => (inner ℝ (e.symm (X n ω)) t : ℝ)) =
        fun n ω => ∑ i, X n ω i * (e t) i := by
      funext n ω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : (fun ω => (inner ℝ (e.symm (Z ω)) t : ℝ)) =
        fun ω => ∑ i, Z ω i * (e t) i := by
      funext ω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [h1, h2]
    exact ht
  have hfin := key.continuous_comp (g := fun x : EuclideanSpace ℝ ι => e x) e.continuous
  simpa [Function.comp_def] using hfin

end Sandpile.External.Stopping
