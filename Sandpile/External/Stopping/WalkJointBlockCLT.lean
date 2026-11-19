import Sandpile.External.Stopping.WalkBlockCLT
import Sandpile.External.Stopping.IndependentBlocks
import Sandpile.External.Stopping.IndependentLimits

/-!
# Joint central limit theorem for walk increment blocks

Projected sums over disjoint, growing blocks converge jointly to independent
centered Gaussian variables. Both block lengths and positions may vary.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.External.Stopping

/-- Disjoint projected increment blocks converge jointly to independent Gaussians. -/
theorem tendstoInDistribution_projected_disjoint_blocks
    {ι : Type*} [Fintype ι] (d : ℕ) [NeZero d] (a : ι → Fin d → ℝ)
    (m : ℕ → ι → ℕ) (hm : ∀ i, Tendsto (fun n => m n i) atTop atTop)
    (v : ℕ → ι → ℕ → ℕ) (hv : ∀ n i, Function.Injective (v n i))
    (hdisj : ∀ n, Pairwise (fun i j => Disjoint
      (Set.range fun k : Fin (m n i) => v n i k)
      (Set.range fun k : Fin (m n j) => v n j k))) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) i =>
        (Real.sqrt (m n i))⁻¹ * ∑ k ∈ Finset.range (m n i),
          LatticeProb.dotSite (a i) (ξ (v n i k)))
      atTop (id : (ι → ℝ) → (ι → ℝ)) (fun _ => LatticeProb.incPathLaw d)
      (Measure.pi fun i => gaussianReal 0 (Real.toNNReal ((∑ j, (a i j) ^ 2) / d))) := by
  let ν : ι → Measure ℝ := fun i =>
    gaussianReal 0 (Real.toNNReal ((∑ j, (a i j) ^ 2) / d))
  let A : ℕ → ι → Set ℕ := fun n i => Set.range fun k : Fin (m n i) => v n i k
  let X : (n : ℕ) → ι → (ℕ → LatticeProb.Site d) → ℝ := fun n i ξ =>
    (Real.sqrt (m n i))⁻¹ * ∑ k ∈ Finset.range (m n i),
      LatticeProb.dotSite (a i) (ξ (v n i k))
  have hX (n : ℕ) : iIndepFun (X n) (LatticeProb.incPathLaw d) := by
    let f : (i : ι) → (A n i → LatticeProb.Site d) → ℝ := fun i z =>
      (Real.sqrt (m n i))⁻¹ * ∑ k : Fin (m n i),
        LatticeProb.dotSite (a i) (z ⟨v n i k, ⟨k, rfl⟩⟩)
    have hf (i : ι) : Measurable (f i) := by
      dsimp [f]
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro k _
      exact (measurable_of_countable (LatticeProb.dotSite (a i))).comp
        (measurable_pi_apply _)
    have hind := iIndepFun_of_disjoint_blocks (LatticeProb.incLaw d) (A n)
      (hdisj n) f hf
    change iIndepFun _ (LatticeProb.incPathLaw d) at hind
    convert hind using 1
    funext i ξ
    dsimp [X, f]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun k =>
      LatticeProb.dotSite (a i) (ξ (v n i k))) (m n i)).symm
  have hY : iIndepFun (fun i (z : ι → ℝ) => z i) (Measure.pi ν) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hlim (i : ι) : TendstoInDistribution (fun n => X n i) atTop
      (fun z : ι → ℝ => z i) (fun _ => LatticeProb.incPathLaw d) (Measure.pi ν) := by
    have h := tendstoInDistribution_projected_increment_blocks d (a i)
      (fun n => m n i) (hm i) (fun n => v n i) (fun n => hv n i)
    refine ⟨h.forall_aemeasurable, (measurable_pi_apply i).aemeasurable, ?_⟩
    have heval : (Measure.pi ν).map (fun z : ι → ℝ => z i) = ν i :=
      (measurePreserving_eval ν i).map_eq
    simpa only [heval, Measure.map_id] using h.tendsto
  have h := tendstoInDistribution_pi_of_independent (fun _ => LatticeProb.incPathLaw d)
      (Measure.pi ν) X (fun i z => z i) hX hY hlim
  refine h.congr (fun _ => Filter.Eventually.of_forall fun ξ => ?_)
    (Filter.Eventually.of_forall fun z => ?_)
  · funext i
    rfl
  · funext i
    rfl

end Sandpile.External.Stopping
