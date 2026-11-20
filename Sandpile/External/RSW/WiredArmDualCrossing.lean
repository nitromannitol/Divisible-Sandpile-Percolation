import Sandpile.External.RSW.WiredArmDual
import Sandpile.External.RSW.ArmCrossing
import Sandpile.External.RSW.DualRotatedCrossing

/-!
# Dual crossing of the wired arm rectangle

If the arm is absent, planar duality produces a crossing of the shifted dual
rectangle associated with the wired arm configuration.
-/

open Set

namespace Sandpile.External.RSW

/-- A centered horizontal crossing after interchanging coordinates gives a vertical
crossing of the original rectangle. -/
theorem vertical_crossing_of_swap_centeredBondCrossingEvent (M N : ℕ)
    (ω : Sym2 (Site 2) → Bool)
    (h : (ω ∘ Sym2.map swapPlaneSite) ∈ centeredBondCrossingEvent N M) :
    ∃ (a b : centeredPlaneRectangle M N)
      (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b),
      (a : Site 2) 1 = (N : ℤ) ∧ (b : Site 2) 1 = -(N : ℤ) ∧ IsBondOpenWalk ω p := by
  let Q := centeredPlaneRectangle N M
  let R := centeredPlaneRectangle M N
  have hQR (z : Q) : swapPlaneSite z ∈ R := by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simpa only [swapPlaneSite, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using ⟨hz.2.2.1, hz.2.2.2, hz.1, hz.2.1⟩
  let f : rectangleGraph Q →g rectangleGraph R :=
    ⟨fun z => ⟨swapPlaneSite z, hQR z⟩, fun h => lattice_adj_swap_plane h⟩
  obtain ⟨a, b, p, ha, hb, hp⟩ := (mem_centeredBondCrossingEvent_iff N M _).mp h
  refine ⟨f b, f a, (p.map f).reverse, ?_, ?_, ?_⟩
  · change (b : Site 2) 0 = N
    exact hb
  · change (a : Site 2) 0 = -(N : ℤ)
    exact ha
  · apply IsBondOpenWalk.reverse
    exact (isBondOpenWalk_map swapPlaneSite f (fun _ => rfl) ω p).mpr hp

/-- Absence of an arm gives a dual crossing of the translated and transposed wired box. -/
theorem dual_crossing_of_not_kstArmEvent (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    (dualBondConfig ((wiredArmConfig m ω ∘ Sym2.map swapPlaneSite) ∘
      Sym2.map (fun z => z + (- ![((m + 1 : ℕ) : ℤ), ((m + m / 64 : ℕ) : ℤ)]))) ∘
      Sym2.map dualCrossingIso) ∈
        bondCrossingEvent (2 * (m + m / 64) + 1) (2 * m + 1) := by
  have hn : (wiredArmConfig m ω ∘ Sym2.map swapPlaneSite) ∉
      centeredBondCrossingEvent (m + 1) (m + m / 64) := by
    intro hc
    apply h
    exact kstArmEvent_of_canonical_wired_crossing m hm ω
      (vertical_crossing_of_swap_centeredBondCrossingEvent (m + m / 64) (m + 1) _ hc)
  change ((wiredArmConfig m ω ∘ Sym2.map swapPlaneSite) ∘
    Sym2.map (fun z => z + (- ![((m + 1 : ℕ) : ℤ), ((m + m / 64 : ℕ) : ℤ)]))) ∉
      bondCrossingEvent (2 * (m + 1)) (2 * (m + m / 64)) at hn
  have hd : ((wiredArmConfig m ω ∘ Sym2.map swapPlaneSite) ∘
    Sym2.map (fun z => z + (- ![((m + 1 : ℕ) : ℤ), ((m + m / 64 : ℕ) : ℤ)]))) ∈
      shiftedDualCrossingEvent ((2 * m + 1) + 1) (2 * (m + m / 64)) := by
    rw [shiftedDualCrossingEvent_eq_compl]
    change _ ∉ bondCrossingEvent _ _
    convert hn using 1
  exact (mem_shiftedDualCrossingEvent_iff_rotated (2 * m + 1) (2 * (m + m / 64)) _).mp hd

end Sandpile.External.RSW
