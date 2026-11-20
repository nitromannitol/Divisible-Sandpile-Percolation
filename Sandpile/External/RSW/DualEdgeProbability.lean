import Sandpile.External.RSW.EdgePathProbability
import Sandpile.External.RSW.DualSwap

/-!
# The dual one-edge probability

For a symmetric bond law, a horizontal dual bond is open with probability one minus the
probability that a horizontal primal bond is open.
-/

open LatticeProb MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A measure-preserving reindexing preserves one-bond open probabilities. -/
theorem measureReal_bondOpenEvent_reindex (μ : Measure (Sym2 (Site 2) → Bool))
    (g : Site 2 → Site 2) (hμ : MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) μ μ) (e : Sym2 (Site 2)) :
    μ.real (bondOpenEvent (Sym2.map g e)) = μ.real (bondOpenEvent e) := by
  have he : (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map g) ⁻¹' bondOpenEvent e =
      bondOpenEvent (Sym2.map g e) := rfl
  rw [← he]
  exact hμ.measureReal_preimage (measurableSet_bondOpenEvent e).nullMeasurableSet

/-- The primal bond crossing the first horizontal dual bond is vertical. -/
theorem dualEdgeEquiv_symm_horizontalBond_zero :
    dualEdgeEquiv.symm (horizontalBond 0) = s(pt 1 0, pt 1 1) := by
  apply dualEdgeEquiv.injective
  rw [dualEdgeEquiv.apply_symm_apply, dualEdgeEquiv_apply]
  have hu : pt 1 0 + Pi.single (1 : Fin 2) 1 = pt 1 1 := by
    ext i
    fin_cases i <;> simp [pt]
  have hd : pt 1 0 - Pi.single (0 : Fin 2) 1 = pt 0 0 := by
    ext i
    fin_cases i <;> simp [pt]
  rw [← hu, dualEdge_vertical, hd]
  rfl

/-- The primal edge crossing the first dual horizontal edge is a shifted coordinate
interchange of the first horizontal edge. -/
theorem dual_primal_bond_eq_reindex :
    s(pt 1 0, pt 1 1) = Sym2.map (fun z => z + pt 1 0)
      (Sym2.map swapPlaneSite (horizontalBond 0)) := by
  have h₀ : swapPlaneSite (pt 0 0) + pt 1 0 = pt 1 0 := by
    ext i
    fin_cases i <;> simp [pt, swapPlaneSite]
  have h₁ : swapPlaneSite (pt 1 0) + pt 1 0 = pt 1 1 := by
    ext i
    fin_cases i <;> simp [pt, swapPlaneSite]
  simp only [horizontalBond, Nat.cast_zero, zero_add, Sym2.map_mk, h₀, h₁]

/-- The horizontal dual-bond probability is the complement of the horizontal primal-bond
probability. -/
theorem dualBondConfig_horizontalBond_probability
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) :
    (μ.map dualBondConfig).real (bondOpenEvent (horizontalBond 0)) =
      1 - μ.real (bondOpenEvent (horizontalBond 0)) := by
  have he : dualBondConfig ⁻¹' bondOpenEvent (horizontalBond 0) =
      (bondOpenEvent s(pt 1 0, pt 1 1))ᶜ := by
    ext ω
    simp only [mem_preimage, bondOpenEvent, mem_ofPred_eq, mem_compl_iff,
      dualBondConfig, dualEdgeEquiv_symm_horizontalBond_zero]
    cases ω s(pt 1 0, pt 1 1) <;> decide
  have hp : μ.real (bondOpenEvent s(pt 1 0, pt 1 1)) =
      μ.real (bondOpenEvent (horizontalBond 0)) := by
    rw [dual_primal_bond_eq_reindex]
    exact (measureReal_bondOpenEvent_reindex μ (fun z => z + pt 1 0) (ht (pt 1 0)) _).trans
      (measureReal_bondOpenEvent_reindex μ swapPlaneSite hs _)
  calc
    (μ.map dualBondConfig).real (bondOpenEvent (horizontalBond 0)) =
        μ.real (dualBondConfig ⁻¹' bondOpenEvent (horizontalBond 0)) := by
          simp only [Measure.real, Measure.map_apply measurable_dualBondConfig
            (measurableSet_bondOpenEvent _)]
    _ = 1 - μ.real (bondOpenEvent s(pt 1 0, pt 1 1)) := by
      rw [he, probReal_compl_eq_one_sub (measurableSet_bondOpenEvent _)]
    _ = 1 - μ.real (bondOpenEvent (horizontalBond 0)) := by rw [hp]

end Sandpile.External.RSW
