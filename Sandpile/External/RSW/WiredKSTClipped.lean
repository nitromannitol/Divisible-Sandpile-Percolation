import Sandpile.External.RSW.WiredKSTBoundaryEntrance
import Sandpile.External.RSW.TrimPathEndpoints

/-!
# Clipping a wired dual crossing

An exceptional scale path gives a wired dual path inside the bridge rectangle,
with endpoints on its left and right target arcs.
-/

namespace Sandpile.External.RSW

/-- An exceptional path gives a clipped wired dual path between the bridge targets. -/
theorem exists_wiredKST_dual_clipped_path_of_no_subpath (m : ℕ) (hm : 12 ≤ m)
    {Q : Finset (Site 2)} {u v : Q} (r : (rectangleGraph Q).Walk u v)
    (hr : r.IsPath) (hsub : ¬ HasKSTSubpath m r)
    (hsubrev : ¬ HasKSTSubpath m r.reverse)
    (hQR : centeredPlaneRectangle (m + m / 12) (m + 1) ⊆ Q) :
    ∃ (a b : centeredPlaneRectangle (m + m / 12 + 1) (m + 1))
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 12 + 1) (m + 1))).Walk a b),
      IsBondOpenWalk (dualBondConfig (wiredKSTConfig m (pathBondConfig r))) p ∧
      ((a : Site 2) 0 = -((m + m / 12 : ℕ) : ℤ) ∨
        ((a : Site 2) 0 ≤ -((m / 12 : ℕ) : ℤ) ∧
          ((a : Site 2) 1 = -(m : ℤ) ∨ (a : Site 2) 1 = m))) ∧
      ((b : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) ∨
        (((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧
          ((b : Site 2) 1 = -(m : ℤ) ∨ (b : Site 2) 1 = m))) ∧
      (∀ x ∈ p.support, ∀ y ∈ p.support, (rectangleGraph
        (centeredPlaneRectangle (m + m / 12 + 1) (m + 1))).Adj x y →
        ¬ ((x : Site 2) 1 = m ∧ (y : Site 2) 1 = m)) ∧
      ∀ z ∈ p.support, (z : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m := by
  classical
  obtain ⟨a, b, p, hp, ho, ha, hb, hs, hi⟩ :=
    exists_wiredKST_dual_boundary_cut_of_no_subpath m (by omega) r hr hsub hsubrev hQR
  have hd : 0 < m / 12 := Nat.div_pos hm (by decide)
  have hne : a ≠ b := by
    intro he
    subst b
    dsimp [wiredKSTDualLeftBoundary, wiredKSTDualRightBoundary] at ha hb
    omega
  have hsep : ¬ (rectangleGraph (centeredPlaneRectangle (m + m / 12 + 1) (m + 1))).Adj a b := by
    intro hab
    have hab' : (lattice 2).Adj (a : Site 2) (b : Site 2) := hab
    have hx := lattice_two_adj_cases hab'
    dsimp [wiredKSTDualLeftBoundary, wiredKSTDualRightBoundary] at ha hb
    rcases hx with hx | hx | hx | hx <;> omega
  let C : centeredPlaneRectangle (m + m / 12 + 1) (m + 1) → Prop :=
    fun z => (z : Site 2) ∈ centeredPlaneRectangle (m + m / 12) m
  have hc : ∀ z ∈ p.support, z ≠ a → z ≠ b → C z := by
    intro z hz hza hzb
    have hz' := hi z hz hza hzb
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    omega
  obtain ⟨c, d, q, hsub, hcend, hdend, hq⟩ :=
    exists_subwalk_trim_endpoints p hp hne hsep C hc
  have hcb := (mem_centeredPlaneRectangle _ _ _).mp (hq c q.start_mem_support)
  have hdb := (mem_centeredPlaneRectangle _ _ _).mp (hq d q.end_mem_support)
  have habounds := hs a p.start_mem_support
  have hbbounds := hs b p.end_mem_support
  have hctarget : (c : Site 2) 0 = -((m + m / 12 : ℕ) : ℤ) ∨
      ((c : Site 2) 0 ≤ -((m / 12 : ℕ) : ℤ) ∧
        ((c : Site 2) 1 = -(m : ℤ) ∨ (c : Site 2) 1 = m)) := by
    rcases hcend with ⟨_, rfl⟩ | ⟨hn, hadj⟩
    · dsimp [wiredKSTDualLeftBoundary] at ha
      omega
    · have hadj' : (lattice 2).Adj (a : Site 2) (c : Site 2) := hadj
      have hout : (a : Site 2) 0 < -((m + m / 12 : ℕ) : ℤ) ∨
          (a : Site 2) 1 < -(m : ℤ) := by
        have hn' : ¬ (-((m + m / 12 : ℕ) : ℤ) ≤ (a : Site 2) 0 ∧
            (a : Site 2) 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
            -(m : ℤ) ≤ (a : Site 2) 1 ∧ (a : Site 2) 1 ≤ m) := by
          simpa only [C, mem_centeredPlaneRectangle] using hn
        omega
      exact wiredKSTDualLeftBoundary_exterior_neighbor m hadj' ha hcb hout
  have hdtarget : (d : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) ∨
      (((m / 12 : ℕ) : ℤ) ≤ (d : Site 2) 0 ∧
        ((d : Site 2) 1 = -(m : ℤ) ∨ (d : Site 2) 1 = m)) := by
    rcases hdend with ⟨_, rfl⟩ | ⟨hn, hadj⟩
    · dsimp [wiredKSTDualRightBoundary] at hb
      omega
    · have hadj' : (lattice 2).Adj (b : Site 2) (d : Site 2) := hadj.symm
      have hout : (b : Site 2) 1 < -(m : ℤ) := by
        have hn' : ¬ (-((m + m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧
            (b : Site 2) 0 ≤ ((m + m / 12 : ℕ) : ℤ) ∧
            -(m : ℤ) ≤ (b : Site 2) 1 ∧ (b : Site 2) 1 ≤ m) := by
          simpa only [C, mem_centeredPlaneRectangle] using hn
        dsimp [wiredKSTDualRightBoundary] at hb
        push_cast at *
        omega
      exact wiredKSTDualRightBoundary_exterior_neighbor m hadj' hb hdb hout
  have htop : ∀ z ∈ p.support, (z : Site 2) 1 = m → z = a ∨ z = b := by
    intro z hz hzrow
    by_cases hza : z = a
    · exact Or.inl hza
    by_cases hzb : z = b
    · exact Or.inr hzb
    have hz' := hi z hz hza hzb
    omega
  have hno : ∀ x ∈ q.support, ∀ y ∈ q.support,
      (rectangleGraph (centeredPlaneRectangle (m + m / 12 + 1) (m + 1))).Adj x y →
      ¬ ((x : Site 2) 1 = m ∧ (y : Site 2) 1 = m) := by
    intro x hx y hy hxy hrow
    have hx' := htop x (hsub.support_subset hx) hrow.1
    have hy' := htop y (hsub.support_subset hy) hrow.2
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact hxy.ne rfl
    · exact hsep hxy
    · exact hsep hxy.symm
    · exact hxy.ne rfl
  exact ⟨c, d, q, ho.subwalk hsub, hctarget, hdtarget, hno, hq⟩

end Sandpile.External.RSW
