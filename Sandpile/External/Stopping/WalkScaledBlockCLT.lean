import Sandpile.External.Stopping.WalkJointBlockCLT

/-!
# Joint limits of diffusively scaled increment blocks

A common spatial scale replaces the square-root block normalization when the
ratio of the two scales converges. This follows from Slutsky's theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.External.Stopping

/-- Disjoint projected blocks converge jointly under a common spatial scaling. -/
theorem tendstoInDistribution_scaled_disjoint_blocks
    {ι : Type*} [Fintype ι] (d : ℕ) [NeZero d] (a : ι → Fin d → ℝ)
    (m : ℕ → ι → ℕ) (hm : ∀ i, Tendsto (fun n => m n i) atTop atTop)
    (v : ℕ → ι → ℕ → ℕ) (hv : ∀ n i, Function.Injective (v n i))
    (hdisj : ∀ n, Pairwise (fun i j => Disjoint
      (Set.range fun k : Fin (m n i) => v n i k)
      (Set.range fun k : Fin (m n j) => v n j k)))
    (R : ℕ → ℝ) (L : ι → ℝ)
    (hscale : ∀ i, Tendsto (fun n => Real.sqrt (m n i) / R n) atTop (𝓝 (L i))) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) i =>
        (R n)⁻¹ * ∑ k ∈ Finset.range (m n i),
          LatticeProb.dotSite (a i) (ξ (v n i k)))
      atTop (fun (z : ι → ℝ) i => z i * L i) (fun _ => LatticeProb.incPathLaw d)
      (Measure.pi fun i => gaussianReal 0 (Real.toNNReal ((∑ j, (a i j) ^ 2) / d))) := by
  let c : ℕ → ι → ℝ := fun n i => Real.sqrt (m n i) / R n
  have hc : Tendsto c atTop (𝓝 L) := tendsto_pi_nhds.mpr hscale
  have hcmeasure : TendstoInMeasure (LatticeProb.incPathLaw d)
      (fun n (_ : ℕ → LatticeProb.Site d) => c n) atTop (fun _ => L) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact stronglyMeasurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ => hc
  have h := tendstoInDistribution_projected_disjoint_blocks d a m hm v hv hdisj
  have h' := h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : (ι → ℝ) × (ι → ℝ) => fun i => p.1 i * p.2 i)
    (by fun_prop) hcmeasure (fun _ => measurable_const.aemeasurable)
  refine h'.congr (fun n => Filter.Eventually.of_forall fun ξ => ?_)
    (Filter.Eventually.of_forall fun _ => rfl)
  funext i
  dsimp [c]
  by_cases hzero : m n i = 0
  · simp [hzero]
  · have hs : Real.sqrt (m n i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hzero)))
    field_simp

end Sandpile.External.Stopping
