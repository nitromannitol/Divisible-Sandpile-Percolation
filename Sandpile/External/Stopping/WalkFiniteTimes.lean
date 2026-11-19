import Sandpile.External.Stopping.WalkFiniteOrderedTimes

/-!
# Walk convergence at finitely many times

Sorting the distinct observation times and repeating coordinates gives the
finite-dimensional convergence without an ordering or distinctness assumption.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Joint convergence at arbitrary finite times, including repeated times and
zero, for the walk and Brownian motion relative to their initial positions. -/
theorem tendstoInDistribution_walk_brownian_finite_times
    {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (u : ι → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) (p : ι × Fin d) =>
        (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊),
          ((ξ k p.2 : ℤ) : ℝ))
      atTop (fun ω (p : ι × Fin d) => B (u p.1) ω p.2 - B 0 ω p.2)
      (fun _ => LatticeProb.incPathLaw d) P := by
  classical
  let S : Finset ℝ≥0 := insert 0 (Finset.univ.image u)
  have hzero : (0 : ℝ≥0) ∈ S := Finset.mem_insert_self _ _
  have hmem (i : ι) : u i ∈ S := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0, hzero⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  let e : Fin (m + 1) ≃o S := S.orderIsoOfFin hm
  let v : Fin (m + 1) → ℝ≥0 := fun i => (e i : ℝ≥0)
  have hv : StrictMono v := fun i j hij => e.strictMono hij
  let idx : ι → Fin (m + 1) := fun i => e.symm ⟨u i, hmem i⟩
  have hidx (i : ι) : v (idx i) = u i := congrArg Subtype.val (e.apply_symm_apply ⟨u i, hmem i⟩)
  have hvzero : v 0 = 0 := by
    let j : Fin (m + 1) := e.symm ⟨0, hzero⟩
    have hj : v j = 0 := congrArg Subtype.val (e.apply_symm_apply ⟨0, hzero⟩)
    exact le_antisymm (hj ▸ hv.monotone (Fin.zero_le j)) (zero_le : 0 ≤ v 0)
  let F : (Fin (m + 1) × Fin d → ℝ) → (ι × Fin d → ℝ) := fun z p => z (idx p.1, p.2)
  have hF : Continuous F := continuous_pi fun p => continuous_apply _
  have h := (tendstoInDistribution_walk_brownian_finite_ordered_times R hR v hv P B hB).continuous_comp hF
  refine h.congr (fun n => Filter.Eventually.of_forall fun ξ => ?_)
    (Filter.Eventually.of_forall fun ω => ?_)
  · funext p
    simp only [Function.comp_def, F, hidx, hvzero, NNReal.coe_zero, zero_mul,
      Nat.floor_zero, Finset.range_zero, Finset.sum_empty, sub_zero]
  · funext p
    simp only [Function.comp_def, F, hidx, hvzero]

end Sandpile.External.Stopping
