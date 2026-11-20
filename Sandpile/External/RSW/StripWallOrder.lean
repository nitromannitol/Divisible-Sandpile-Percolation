import Sandpile.External.RSW.VerticalOrderIntersection
import Sandpile.External.RSW.StripWallIntersection

/-!
# Endpoint order between strip walls

A strip crossing disjoint from two vertical walls stays between their endpoints
on the opposite boundary when it starts between their endpoints.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- Endpoint order is preserved by disjoint vertical walks in a lattice rectangle. -/
theorem rectangle_vertical_walks_order_of_disjoint {Q : Finset (Site 2)}
    {a b u v : Q} (p : (rectangleGraph Q).Walk a b)
    (q : (rectangleGraph Q).Walk u v) {L R B T : ℤ} (hBT : B < T)
    (hp : ∀ z ∈ p.support, L ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ R ∧
      B ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ T)
    (hq : ∀ z ∈ q.support, L ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ R ∧
      B ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ T)
    (ha : (a : Site 2) 1 = T) (hb : (b : Site 2) 1 = B)
    (hu : (u : Site 2) 1 = T) (hv : (v : Site 2) 1 = B)
    (hdis : ∀ z ∈ p.support, z ∉ q.support)
    (htop : (u : Site 2) 0 ≤ (a : Site 2) 0) :
    (v : Site 2) 0 < (b : Site 2) 0 := by
  let f : rectangleGraph Q →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hbox {s t : Q} (w : (rectangleGraph Q).Walk s t)
      (hw : ∀ z ∈ w.support, L ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ R ∧
        B ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ T) :
      ∀ z ∈ (w.map f).support, L ≤ z 0 ∧ z 0 ≤ R ∧ B ≤ z 1 ∧ z 1 ≤ T := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact hw z' hz'
  have hdis' : ∀ z ∈ (p.map f).support, z ∉ (q.map f).support := by
    intro z hzp hzq
    rw [SimpleGraph.Walk.support_map] at hzp hzq
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hzp
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hzq
    have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
    subst y
    exact hdis x hx hy
  exact vertical_walks_order_of_disjoint hBT (p.map f) (q.map f)
    (hbox p hp) (hbox q hq) ha hb hu hv hdis' htop

/-- A strip walk between two disjoint KST paths has its lower endpoint between theirs. -/
theorem strip_walk_endpoint_between_walls {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (left : (rectangleGraph Q).Walk c d) (right : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hleft : IsKSTPath k left) (hright : IsKSTPath k right)
    (hp : ∀ z ∈ p.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (ha : (a : Site 2) 1 = k) (hb : (b : Site 2) 1 = -(k : ℤ))
    (hl : ∀ z ∈ p.support, z ∉ left.support)
    (hr : ∀ z ∈ p.support, z ∉ right.support)
    (htopLeft : (c : Site 2) 0 ≤ (a : Site 2) 0)
    (htopRight : (a : Site 2) 0 ≤ (e : Site 2) 0) :
    (d : Site 2) 0 < (b : Site 2) 0 ∧ (b : Site 2) 0 < (f : Site 2) 0 := by
  have hBT : -(k : ℤ) < k := by omega
  have hbox {s t : Q} (w : (rectangleGraph Q).Walk s t)
      (hw : ∀ z ∈ w.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k) :
      ∀ z ∈ w.support, -((k + k / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧
        (z : Site 2) 0 ≤ (k + k / 12 : ℕ) ∧ -(k : ℤ) ≤ (z : Site 2) 1 ∧
        (z : Site 2) 1 ≤ k := by
    intro z hz
    exact (mem_centeredPlaneRectangle _ _ _).mp (hw z hz)
  have hrdis : ∀ z ∈ right.support, z ∉ p.support := by
    intro z hz hpz
    exact hr z hpz hz
  exact ⟨rectangle_vertical_walks_order_of_disjoint p left hBT (hbox p hp)
      (hbox left hleft.2.2.2.2.2.2.2) ha hb hleft.2.1 hleft.2.2.1 hl htopLeft,
    rectangle_vertical_walks_order_of_disjoint right p hBT
      (hbox right hright.2.2.2.2.2.2.2) (hbox p hp)
      hright.2.1 hright.2.2.1 ha hb hrdis htopRight⟩

/-- A simple strip crossing between two disjoint KST paths is itself a KST path. -/
theorem isKSTPath_of_strip_walk_between_walls {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (left : (rectangleGraph Q).Walk c d) (right : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hpath : p.IsPath)
    (hleft : IsKSTPath k left) (hright : IsKSTPath k right)
    (hp : ∀ z ∈ p.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (ha : (a : Site 2) 1 = k) (hb : (b : Site 2) 1 = -(k : ℤ))
    (hl : ∀ z ∈ p.support, z ∉ left.support)
    (hr : ∀ z ∈ p.support, z ∉ right.support)
    (htopLeft : (c : Site 2) 0 ≤ (a : Site 2) 0)
    (htopRight : (a : Site 2) 0 ≤ (e : Site 2) 0) : IsKSTPath k p := by
  have hbottom := strip_walk_endpoint_between_walls p left right hk hleft hright hp
    ha hb hl hr htopLeft htopRight
  refine ⟨hpath, ha, hb, ?_, ?_, ?_, ?_, hp⟩
  · have h := hleft.2.2.2.1
    omega
  · have h := hright.2.2.2.2.1
    omega
  · have h := hleft.2.2.2.2.2.1
    omega
  · have h := hright.2.2.2.2.2.2.1
    omega

end Sandpile.External.RSW
