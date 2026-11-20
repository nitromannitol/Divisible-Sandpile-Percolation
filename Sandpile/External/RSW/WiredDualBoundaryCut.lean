import Sandpile.External.RSW.WiredDualCrossingPath
import Sandpile.External.RSW.LastEntryFirstExit

/-!
# Cutting a wired dual crossing at its boundary

A simple wired dual crossing has a segment between the left and right boundary
arcs whose non-endpoint vertices are strictly inside the enlarged face rectangle.
-/

namespace Sandpile.External.RSW

/-- The left boundary arc of the wired dual face rectangle. -/
def wiredDualLeftBoundary (m : ℕ) (z : Site 2) : Prop :=
  z 0 ≤ -((m / 64 : ℕ) : ℤ) - 1 ∧
    (z 0 = -((m + m / 64 : ℕ) : ℤ) - 1 ∨
      z 1 = -((m : ℤ) + 1) ∨ z 1 = m)

/-- The right boundary arc of the wired dual face rectangle. -/
def wiredDualRightBoundary (m : ℕ) (z : Site 2) : Prop :=
  ((m / 64 : ℕ) : ℤ) ≤ z 0 ∧
    (z 0 = ((m + m / 64 : ℕ) : ℤ) ∨
      z 1 = -((m : ℤ) + 1) ∨ z 1 = m)

/-- Cut a dual crossing to a path between the left and right wired boundary arcs. -/
theorem exists_wired_dual_boundary_cut_of_not_kstArmEvent (m : ℕ) (hm : 0 < m)
    (ω : Sym2 (Site 2) → Bool) (h : ω ∉ kstArmEvent m) :
    ∃ (a b : centeredPlaneRectangle (m + m / 64 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 64 + 1) (m + 1))).Walk a b),
      p.IsPath ∧ IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p ∧
      wiredDualLeftBoundary m a ∧ wiredDualRightBoundary m b ∧
      (∀ z ∈ p.support, -((m + m / 64 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ ((m + m / 64 : ℕ) : ℤ) ∧
        -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m) ∧
      ∀ z ∈ p.support, z ≠ a → z ≠ b →
        -((m + m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 < ((m + m / 64 : ℕ) : ℤ) ∧
        -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 < m := by
  classical
  obtain ⟨a, b, p, hp, ho, ha, hb, hs, hc⟩ :=
    exists_wired_dual_crossing_path_of_not_kstArmEvent m hm ω h
  let A : centeredPlaneRectangle (m + m / 64 + 1) (m + 1) → Prop :=
    fun z => wiredDualLeftBoundary m z
  let B : centeredPlaneRectangle (m + m / 64 + 1) (m + 1) → Prop :=
    fun z => wiredDualRightBoundary m z
  have hdis : ∀ z, A z → ¬ B z := by
    intro z hz hz'
    dsimp [A, B, wiredDualLeftBoundary, wiredDualRightBoundary] at hz hz'
    omega
  have ha' : A a := by
    dsimp [A, wiredDualLeftBoundary]
    rw [ha]
    push_cast
    omega
  have hb' : B b := by
    dsimp [B, wiredDualRightBoundary]
    rw [hb]
    push_cast
    omega
  obtain ⟨c, d, q, hsub, hca, hdb, hends⟩ :=
    exists_subwalk_between_disjoint_sets A B hdis p ha' hb'
  have hqpath := SimpleGraph.Walk.isPath_of_isSubwalk hsub hp
  have hqopen := ho.subwalk hsub
  have hqbounds : ∀ z ∈ q.support, -((m + m / 64 : ℕ) : ℤ) - 1 ≤ (z : Site 2) 0 ∧
      (z : Site 2) 0 ≤ ((m + m / 64 : ℕ) : ℤ) ∧
      -((m : ℤ) + 1) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ m :=
    fun z hz => hs z (hsub.support_subset hz)
  refine ⟨c, d, q, hqpath, hqopen, hca, hdb, hqbounds, ?_⟩
  intro z hz hzc hzd
  have hbounds := hqbounds z hz
  have hnA : ¬ A z := fun hzA => hzc ((hends z hz).1 hzA)
  have hnB : ¬ B z := fun hzB => hzd ((hends z hz).2 hzB)
  have hcentral : -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0 →
      (z : Site 2) 0 < ((m / 64 : ℕ) : ℤ) →
      -((m : ℤ) + 1) < (z : Site 2) 1 ∧ (z : Site 2) 1 < m :=
    hc z (hsub.support_subset hz)
  dsimp [A, B, wiredDualLeftBoundary, wiredDualRightBoundary] at hnA hnB
  push_cast at *
  by_cases hl : -((m / 64 : ℕ) : ℤ) ≤ (z : Site 2) 0
  · by_cases hr : (z : Site 2) 0 < ((m / 64 : ℕ) : ℤ)
    · have hy := hcentral hl hr
      omega
    · omega
  · omega

end Sandpile.External.RSW
