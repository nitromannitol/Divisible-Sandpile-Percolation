import Sandpile.External.RSW.WiredKSTCrossingPath
import Sandpile.External.RSW.LastEntryFirstExit

/-!
# Cutting a wired dual crossing at its boundary

A simple wired dual crossing has a segment between the left and right boundary
arcs whose non-endpoint vertices are strictly inside the enlarged face rectangle.
-/

namespace Sandpile.External.RSW

/-- The left boundary arc of the wired dual face rectangle. -/
def wiredKSTDualLeftBoundary (m : ℕ) (z : Site 2) : Prop :=
  z 0 ≤ -((m / 12 : ℕ) : ℤ) - 1 ∧
    (z 0 = -((m + m / 12 : ℕ) : ℤ) - 1 ∨
      z 1 = -((m : ℤ) + 1) ∨ z 1 = m)

/-- The right boundary arc of the wired dual face rectangle. -/
def wiredKSTDualRightBoundary (m : ℕ) (z : Site 2) : Prop :=
  ((m / 12 : ℕ) : ℤ) ≤ z 0 ∧
    (z 0 = ((m + m / 12 : ℕ) : ℤ) ∨
      z 1 = -((m : ℤ) + 1) ∨ z 1 = m)

/-- Cut a dual crossing to a path between the left and right wired boundary arcs. -/
theorem exists_wiredKST_dual_boundary_cut_of_no_subpath (m : ℕ) (hm : 0 < m)
    {Q : Finset (Site 2)} {u v : Q} (r : (rectangleGraph Q).Walk u v)
    (hr : r.IsPath) (hsub : ¬ HasKSTSubpath m r)
    (hsubrev : ¬ HasKSTSubpath m r.reverse)
    (hQR : centeredPlaneRectangle (m + m / 12) (m + 1) ⊆ Q) :
    ∃ (a b : centeredPlaneRectangle (m + m / 12 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 12 + 1) (m + 1))).Walk a b),
      p.IsPath ∧ IsBondOpenWalk (dualBondConfig (wiredKSTConfig m (pathBondConfig r))) p ∧
      wiredKSTDualLeftBoundary m a ∧ wiredKSTDualRightBoundary m b ∧
      (∀ z ∈ p.support, -((m + m / 12 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
        -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m) ∧
      ∀ z ∈ p.support, z ≠ a → z ≠ b →
        -((m + m / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 < ((m + m / 12 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 < m := by
  classical
  obtain ⟨a, b, p, hp, ho, ha, hb, hs, hc⟩ :=
    exists_wiredKST_dual_crossing_path_of_no_subpath m hm r hr hsub hsubrev hQR
  let A : centeredPlaneRectangle (m + m / 12 + 1) (m + 1) → Prop :=
    fun z => wiredKSTDualLeftBoundary m z
  let B : centeredPlaneRectangle (m + m / 12 + 1) (m + 1) → Prop :=
    fun z => wiredKSTDualRightBoundary m z
  have hdis : ∀ z, A z → ¬ B z := by
    intro z hz hz'
    dsimp [A, B, wiredKSTDualLeftBoundary, wiredKSTDualRightBoundary] at hz hz'
    omega
  have ha' : A a := by
    dsimp [A, wiredKSTDualLeftBoundary]
    rw [ha]
    push_cast
    omega
  have hb' : B b := by
    dsimp [B, wiredKSTDualRightBoundary]
    rw [hb]
    push_cast
    omega
  obtain ⟨c, d, q, hsub, hca, hdb, hends⟩ :=
    exists_subwalk_between_disjoint_sets A B hdis p ha' hb'
  have hqpath := SimpleGraph.Walk.isPath_of_isSubwalk hsub hp
  have hqopen := ho.subwalk hsub
  have hqbounds : ∀ z ∈ q.support, -((m + m / 12 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
      (z : Site 2) 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
      -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m :=
    fun z hz => hs z (hsub.support_subset hz)
  refine ⟨c, d, q, hqpath, hqopen, hca, hdb, hqbounds, ?_⟩
  intro z hz hzc hzd
  have hbounds := hqbounds z hz
  have hnA : ¬ A z := fun hzA => hzc ((hends z hz).1 hzA)
  have hnB : ¬ B z := fun hzB => hzd ((hends z hz).2 hzB)
  have hcentral : -((m / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 →
      (z : Site 2) 0 < ((m / 12 : ℕ) : ℤ) →
      -((m : ℤ) + 1) < (z : Site 2) 1 ∧ (z : Site 2) 1 < m :=
    hc z (hsub.support_subset hz)
  dsimp [A, B, wiredKSTDualLeftBoundary, wiredKSTDualRightBoundary] at hnA hnB
  push_cast at *
  by_cases hl : -((m / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0
  · by_cases hr : (z : Site 2) 0 < ((m / 12 : ℕ) : ℤ)
    · have hy := hcentral hl hr
      omega
    · omega
  · omega

end Sandpile.External.RSW
