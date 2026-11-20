import Sandpile.External.RSW.WiredKSTConfiguration
import Sandpile.External.RSW.WiredArmDualCrossing
import Sandpile.External.RSW.KSTPathBond
import Sandpile.External.RSW.KSTPathInclusion

/-!
# Dual crossings around a path

If a simple lattice path contains no KST subpath in either direction, planar
duality supplies a crossing in the dual of its wired scale rectangle.
-/

namespace Sandpile.External.RSW

/-- A path without a smaller scale subpath in either direction has a dual
crossing in the corresponding wired rectangle. -/
theorem dual_crossing_of_no_kst_subpath (k : ℕ) (hk : 0 < k)
    {Q : Finset (Site 2)} {a b : Q} (p : (rectangleGraph Q).Walk a b)
    (hp : p.IsPath) (hsub : ¬ HasKSTSubpath k p)
    (hsubrev : ¬ HasKSTSubpath k p.reverse)
    (hQR : centeredPlaneRectangle (k + k / 12) (k + 1) ⊆ Q) :
    (dualBondConfig ((wiredKSTConfig k (pathBondConfig p) ∘ Sym2.map swapPlaneSite) ∘
      Sym2.map (fun z => z + (- ![((k + 1 : ℕ) : ℤ), ((k + k / 12 : ℕ) : ℤ)]))) ∘
      Sym2.map dualCrossingIso) ∈
        bondCrossingEvent (2 * (k + k / 12) + 1) (2 * k + 1) := by
  have hn : (wiredKSTConfig k (pathBondConfig p) ∘ Sym2.map swapPlaneSite) ∉
      centeredBondCrossingEvent (k + 1) (k + k / 12) := by
    intro hc
    obtain ⟨x, y, q, hq, hqo⟩ := exists_kstPath_of_canonical_wired_crossing k hk
      (pathBondConfig p)
      (vertical_crossing_of_swap_centeredBondCrossingEvent (k + k / 12) (k + 1) _ hc)
    let q' := q.map (rectangleGraphInclusion hQR)
    have hq' : IsKSTPath k q' := hq.map_inclusion hQR
    have hqo' : IsBondOpenWalk (pathBondConfig p) q' := hqo.map_inclusion hQR
    rcases hasKSTSubpath_or_reverse_of_open_pathBondConfig k hk p q' hp hq' hqo' with h | h
    · exact hsub h
    · exact hsubrev h
  change ((wiredKSTConfig k (pathBondConfig p) ∘ Sym2.map swapPlaneSite) ∘
    Sym2.map (fun z => z + (- ![((k + 1 : ℕ) : ℤ), ((k + k / 12 : ℕ) : ℤ)]))) ∉
      bondCrossingEvent (2 * (k + 1)) (2 * (k + k / 12)) at hn
  have hd : ((wiredKSTConfig k (pathBondConfig p) ∘ Sym2.map swapPlaneSite) ∘
    Sym2.map (fun z => z + (- ![((k + 1 : ℕ) : ℤ), ((k + k / 12 : ℕ) : ℤ)]))) ∈
      shiftedDualCrossingEvent ((2 * k + 1) + 1) (2 * (k + k / 12)) := by
    rw [shiftedDualCrossingEvent_eq_compl]
    change _ ∉ bondCrossingEvent _ _
    convert hn using 1
  exact (mem_shiftedDualCrossingEvent_iff_rotated (2 * k + 1) (2 * (k + k / 12)) _).mp hd

end Sandpile.External.RSW
