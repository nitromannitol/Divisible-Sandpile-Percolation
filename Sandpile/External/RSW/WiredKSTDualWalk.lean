import Sandpile.External.RSW.WiredKSTDualEdges
import Sandpile.External.RSW.WiredDualCoordinates
import Sandpile.External.RSW.TranslatedCrossingWalk

/-!
# A dual walk around a scale path

The dual crossing of a wired scale rectangle can be expressed as an open walk
in face coordinates, with explicit bounds and endpoints.
-/

open Percolation.Literature

namespace Sandpile.External.RSW

/-- The coordinate changes in wired scale duality reduce to a translation. -/
theorem wiredKST_dual_reindex (k : ℕ) (ω : Sym2 (Site 2) → Bool) :
    (dualBondConfig ((wiredKSTConfig k ω ∘ Sym2.map swapPlaneSite) ∘
      Sym2.map (fun z => z + (- ![((k + 1 : ℕ) : ℤ), ((k + k / 12 : ℕ) : ℤ)]))) ∘
      Sym2.map dualCrossingIso) =
    (dualBondConfig (wiredKSTConfig k ω) ∘
      Sym2.map (fun z => z + ![-((k + k / 12 : ℕ) : ℤ) - 1, -((k + 1 : ℕ) : ℤ)])) := by
  rw [dualBondConfig_translate, dualBondConfig_swap]
  funext edge
  induction edge using Sym2.ind with
  | _ x y =>
    simp only [Function.comp_apply, Sym2.map_mk]
    have hf (z : Site 2) : dualCrossingIso z = swapPlaneSite z + dualShift := by
      ext i
      fin_cases i <;> simp [dualCrossingIso, swapPlaneSite]
    have hg (z : Site 2) :
        swapPlaneSite (dualCrossingIso z +
          (- ![((k + 1 : ℕ) : ℤ), ((k + k / 12 : ℕ) : ℤ)])) =
        z + ![-((k + k / 12 : ℕ) : ℤ) - 1, -((k + 1 : ℕ) : ℤ)] := by
      rw [hf]
      ext i
      fin_cases i
      · simp [swapPlaneSite, dualShift, Pi.add_apply]
        ring
      · simp [swapPlaneSite, dualShift, Pi.add_apply]
    rw [hg x, hg y]

/-- A path with no smaller scale subpath in either orientation has a dual walk
across the associated wired rectangle. -/
theorem exists_wiredKST_dual_walk_of_no_subpath (k : ℕ) (hk : 0 < k)
    {Q : Finset (Site 2)} {a b : Q} (p : (rectangleGraph Q).Walk a b)
    (hp : p.IsPath) (hsub : ¬ HasKSTSubpath k p)
    (hsubrev : ¬ HasKSTSubpath k p.reverse)
    (hQR : centeredPlaneRectangle (k + k / 12) (k + 1) ⊆ Q) :
    ∃ (x y : centeredPlaneRectangle (k + k / 12 + 1) (k + 1))
      (q : (rectangleGraph (centeredPlaneRectangle (k + k / 12 + 1) (k + 1))).Walk x y),
      q.IsPath ∧ IsBondOpenWalk (dualBondConfig (wiredKSTConfig k (pathBondConfig p))) q ∧
      (x : Site 2) 0 = -((k + k / 12 : ℕ) : ℤ) - 1 ∧
      (y : Site 2) 0 = ((k + k / 12 : ℕ) : ℤ) ∧
      ∀ z ∈ q.support,
        -((k + k / 12 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((k + k / 12 : ℕ) : ℤ) ∧
        -((k + 1 : ℕ) : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ (k : ℤ) := by
  let M := k + k / 12
  let x : ℤ := -(M : ℤ) - 1
  let y : ℤ := -((k + 1 : ℕ) : ℤ)
  have hx : x + ((2 * M + 1 : ℕ) : ℤ) = M := by
    dsimp [x]
    omega
  have hy : y + ((2 * k + 1 : ℕ) : ℤ) = k := by
    dsimp [y]
    omega
  have hc := dual_crossing_of_no_kst_subpath k hk p hp hsub hsubrev hQR
  rw [wiredKST_dual_reindex] at hc
  change (dualBondConfig (wiredKSTConfig k (pathBondConfig p)) ∘ Sym2.map (fun z => z + ![x, y])) ∈
    bondCrossingEvent (2 * M + 1) (2 * k + 1) at hc
  obtain ⟨a, b, q, hq, ha, hb, hs⟩ := translated_bondCrossingEvent_exists_walk
    (2 * M + 1) (2 * k + 1) (M + 1) (k + 1) x y
    (by dsimp [x]; omega) (by rw [hx]; push_cast; omega)
    (by dsimp [y]; omega) (by rw [hy]; push_cast; omega) hc
  refine ⟨a, b, q.bypass, q.bypass_isPath, hq.bypass, ha, ?_, ?_⟩
  · simpa only [hx, M] using hb
  · intro z hz
    simpa only [hx, hy, x, y, M] using hs z (q.support_bypass_subset_support hz)

end Sandpile.External.RSW
