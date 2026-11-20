import Sandpile.External.RSW.DualProbability
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWProofs

/-!
# Shifted and rotated dual crossings

Discrete planar duality identifies a horizontal crossing with the complement of a vertical
crossing of the dual rectangle, whose side lengths differ by one from the primal lengths.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Relabeling an open edge set along a lattice automorphism undoes the corresponding
reindexing of its Boolean configuration. -/
theorem relabel_openPlaneBonds (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2)
    (ω : Sym2 (Site 2) → Bool) :
    BondConfig.relabel (sym2Equiv φ.toEquiv)
      (openPlaneBonds (ω ∘ Sym2.map φ)) = openPlaneBonds ω := by
  ext e
  rw [BondConfig.mem_relabel_iff, sym2Equiv_symm, sym2Equiv_apply]
  simp only [openPlaneBonds, mem_ofPred_eq, Function.comp_apply, lattice_eq_zdGraph]
  have he : Sym2.map φ.toEquiv.symm e ∈ (LatticeModels.zdGraph 2).edgeSet ↔
      e ∈ (LatticeModels.zdGraph 2).edgeSet := by
    change sym2Equiv φ.symm.toEquiv e ∈ _ ↔ _
    rw [sym2Equiv_mem_edgeSet_iff]
  rw [he]
  have hm : Sym2.map φ (Sym2.map φ.toEquiv.symm e) = e := by
    induction e using Sym2.ind with
    | _ x y =>
      change s(φ.toEquiv (φ.toEquiv.symm x), φ.toEquiv (φ.toEquiv.symm y)) = s(x, y)
      simp only [Equiv.apply_symm_apply]
  rw [hm]

/-- Interchange the axes and shift down to locate the dual rectangle. -/
def dualCrossingIso : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2 :=
  transposeIso.trans (zdShiftIso dualShift)

/-- The image of the ordinary rectangle under the dual crossing isomorphism. -/
theorem dualCrossingIso_image_rectangle (m n : ℕ) :
    dualCrossingIso '' (↑(rectangle (n + 1) m) : Set (Site 2)) =
      ↑(dualRectangle (m + 1) n) := by
  rw [← image_dualShift_rectangle]
  change ((fun z : Site 2 => z + dualShift) ∘ (transposeIso : Site 2 → Site 2)) '' _ = _
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (Set.image (fun z : Site 2 => z + dualShift))
      ((image_transposeIso _).trans (preimage_transpose_rectangle (n + 1) m))

/-- The left side of the ordinary rectangle maps to the bottom dual side. -/
theorem dualCrossingIso_image_leftSide (m n : ℕ) :
    dualCrossingIso '' (↑(leftSide (n + 1) m) : Set (Site 2)) =
      ↑(dualBottomSide (m + 1) n) := by
  rw [← image_dualShift_bottomSide]
  change ((fun z : Site 2 => z + dualShift) ∘ (transposeIso : Site 2 → Site 2)) '' _ = _
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (Set.image (fun z : Site 2 => z + dualShift))
      ((image_transposeIso _).trans (preimage_transpose_leftSide (n + 1) m))

/-- The right side of the ordinary rectangle maps to the top dual side. -/
theorem dualCrossingIso_image_rightSide (m n : ℕ) :
    dualCrossingIso '' (↑(rightSide (n + 1) m) : Set (Site 2)) =
      ↑(dualTopSide (m + 1) n) := by
  rw [← image_dualShift_topSide]
  change ((fun z : Site 2 => z + dualShift) ∘ (transposeIso : Site 2 → Site 2)) '' _ = _
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (Set.image (fun z : Site 2 => z + dualShift))
      ((image_transposeIso _).trans (preimage_transpose_rightSide (n + 1) m))

/-- A shifted dual crossing is the ordinary horizontal crossing of the rotated dual box,
with the dual bonds reindexed by the rotation and translation. -/
theorem mem_shiftedDualCrossingEvent_iff_rotated (m n : ℕ)
    (ω : Sym2 (Site 2) → Bool) :
    ω ∈ shiftedDualCrossingEvent (m + 1) n ↔
      (dualBondConfig ω ∘ Sym2.map dualCrossingIso) ∈ bondCrossingEvent (n + 1) m := by
  rw [mem_shiftedDualCrossingEvent_iff, mem_bondCrossingEvent_iff_lrCrossing]
  have he := Set.ext_iff.mp
    (preimage_relabel_openCrossing dualCrossingIso.toEquiv
      (↑(rectangle (n + 1) m)) (↑(leftSide (n + 1) m)) (↑(rightSide (n + 1) m)))
    (openPlaneBonds (dualBondConfig ω ∘ Sym2.map dualCrossingIso))
  change BondConfig.relabel (sym2Equiv dualCrossingIso.toEquiv)
      (openPlaneBonds (dualBondConfig ω ∘ Sym2.map dualCrossingIso)) ∈
    openCrossing (dualCrossingIso '' (↑(rectangle (n + 1) m) : Set (Site 2)))
      (dualCrossingIso '' (↑(leftSide (n + 1) m) : Set (Site 2)))
      (dualCrossingIso '' (↑(rightSide (n + 1) m) : Set (Site 2))) ↔ _ at he
  rw [dualCrossingIso_image_rectangle, dualCrossingIso_image_leftSide,
    dualCrossingIso_image_rightSide, relabel_openPlaneBonds] at he
  change openPlaneBonds (dualBondConfig ω) ∈
      openCrossing (↑(dualRectangle (m + 1) n)) (↑(dualBottomSide (m + 1) n))
        (↑(dualTopSide (m + 1) n)) ↔ _ at he
  rw [openCrossing_comm] at he
  exact he

end Sandpile.External.RSW
