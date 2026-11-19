import Sandpile.External.Stopping.WalkScalarCLT
import LatticeProb.Prob.Blocks

/-!
# Central limit theorem for walk increment blocks

The central limit theorem for a projected walk increment remains valid when
its summands are read from arbitrary injectively indexed blocks. The block
and its starting point may vary with the scale.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- Projected sums over injectively indexed blocks obey the scalar central limit theorem. -/
theorem tendstoInDistribution_projected_increment_blocks (d : ℕ) [NeZero d]
    (a : Fin d → ℝ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (v : ℕ → ℕ → ℕ) (hv : ∀ n, Function.Injective (v n)) :
    TendstoInDistribution
      (fun (n : ℕ) (ξ : ℕ → LatticeProb.Site d) =>
        (Real.sqrt (m n))⁻¹ * ∑ k ∈ Finset.range (m n), LatticeProb.dotSite a (ξ (v n k)))
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.incPathLaw d)
      (gaussianReal 0 (Real.toNNReal ((∑ i, (a i) ^ 2) / d))) := by
  let F : ℕ → (ℕ → LatticeProb.Site d) → ℝ := fun n ξ =>
    (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, LatticeProb.dotSite a (ξ k)
  have h := tendstoInDistribution_projected_increments d a
  have hmeas (n : ℕ) : Measurable (F n) := by
    dsimp [F]
    fun_prop (disch := exact measurable_of_countable _)
  have hmap (n : ℕ) :
      (LatticeProb.incPathLaw d).map (fun ξ => F (m n) (fun k => ξ (v n k))) =
        (LatticeProb.incPathLaw d).map (F (m n)) := by
    have hread : Measurable (fun (ξ : ℕ → LatticeProb.Site d) k => ξ (v n k)) :=
      Measurable.of_eval fun k => measurable_pi_apply (v n k)
    change (LatticeProb.incPathLaw d).map
      (F (m n) ∘ (fun (ξ : ℕ → LatticeProb.Site d) k => ξ (v n k))) = _
    rw [← Measure.map_map (hmeas _) hread]
    rw [LatticeProb.incPathLaw, LatticeProb.infinitePi_map_comp' _ _ (hv n)]
  refine ⟨?_, h.aemeasurable_limit, ?_⟩
  · intro n
    exact (hmeas _).aemeasurable.comp_measurable
      (Measurable.of_eval fun k => measurable_pi_apply (v n k))
  · have ht := h.tendsto.comp hm
    apply Filter.Tendsto.congr (fun n => ?_) ht
    apply Subtype.ext
    exact (hmap n).symm

end Sandpile.External.Stopping
