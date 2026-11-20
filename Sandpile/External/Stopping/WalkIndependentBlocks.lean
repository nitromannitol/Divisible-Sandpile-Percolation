import Sandpile.External.Stopping.IndependentBlocks
import Sandpile.External.LocalCLT
import LatticeProb.Walk.Markov

/-!
# Independent sums of lattice walk increments

Scaled sums of disjoint finite sets of independent walk increments are
independent. This applies to the disjoint time intervals of a step walk.
-/

open MeasureTheory ProbabilityTheory Set

namespace Sandpile.External.Stopping

/-- Scaled sums over disjoint finite blocks of walk increments are independent. -/
theorem iIndepFun_scaled_site_block_sums {d : ℕ} [NeZero d] {ι : Type*}
    (R : ℝ) (A : ι → Finset ℕ)
    (hdisj : Pairwise (fun i j => Disjoint ((A i : Finset ℕ) : Set ℕ) (A j : Set ℕ))) :
    iIndepFun (fun i (ξ : ℕ → Site d) => Lclt.scaledSite R (∑ k ∈ A i, ξ k))
      (LatticeProb.incPathLaw d) := by
  let S : ι → Set ℕ := fun i => (A i : Set ℕ)
  let f : (i : ι) → (S i → Site d) → Continuum.Space d := fun i z =>
    Lclt.scaledSite R (∑ k : S i, z k)
  have hf (i : ι) : Measurable (f i) := by
    apply (measurable_of_countable (Lclt.scaledSite (d := d) R)).comp
    apply Finset.measurable_sum
    intro k _
    exact measurable_pi_apply k
  have hi := iIndepFun_of_disjoint_blocks (LatticeProb.incLaw d) S hdisj f hf
  change iIndepFun _ (LatticeProb.incPathLaw d) at hi
  convert hi using 1
  funext i ξ
  change Lclt.scaledSite R (∑ k ∈ A i, ξ k) = Lclt.scaledSite R (∑ k : S i, ξ k)
  congr 1
  exact (Finset.sum_attach (A i) ξ).symm

end Sandpile.External.Stopping
