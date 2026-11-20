import Sandpile.External.RSW.StripWallConfinement
import Sandpile.External.RSW.StripWallOrder
import Sandpile.External.RSW.QuasiCascadeCover

/-!
# KST strip confinement

A strip crossing starting between two KST paths and avoiding them is itself a
KST path whenever it is simple.
-/

open LatticeProb Percolation.Literature

namespace Sandpile.External.RSW

/-- A strip walk starting between KST walls and avoiding them stays in their scale box. -/
theorem kst_strip_walk_bounded_between_walls {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (left : (rectangleGraph Q).Walk c d) (right : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hleft : IsKSTPath k left) (hright : IsKSTPath k right)
    (hp : ∀ z ∈ p.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (ha : (a : Site 2) 1 = k)
    (hl : ∀ z ∈ p.support, z ∉ left.support)
    (hr : ∀ z ∈ p.support, z ∉ right.support)
    (htopLeft : (c : Site 2) 0 ≤ (a : Site 2) 0)
    (htopRight : (a : Site 2) 0 ≤ (e : Site 2) 0) :
    ∀ z ∈ p.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k := by
  let f : rectangleGraph Q →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hbox {s t : Q} (w : (rectangleGraph Q).Walk s t)
      (hw : ∀ z ∈ w.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k) :
      ∀ z ∈ (w.map f).support, -((k + k / 12 : ℕ) : ℤ) ≤ z 0 ∧
        z 0 ≤ (k + k / 12 : ℕ) ∧ -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ _).mp (hw z' hz')
  have hstrip : ∀ z ∈ (p.map f).support, -(k : ℤ) ≤ z 1 ∧ z 1 ≤ k := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact hp z' hz'
  have hdis {s t : Q} (w : (rectangleGraph Q).Walk s t)
      (hw : ∀ z ∈ p.support, z ∉ w.support) :
      ∀ z ∈ (p.map f).support, z ∉ (w.map f).support := by
    intro z hzp hzw
    rw [SimpleGraph.Walk.support_map] at hzp hzw
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hzp
    obtain ⟨y, hy, hye⟩ := List.mem_map.mp hzw
    have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
    subst y
    exact hw x hx hy
  have hBT : -(k : ℤ) < k := by omega
  have hleftSide : -((k + k / 12 : ℕ) : ℤ) < (c : Site 2) 0 := by
    have h := hleft.2.2.2.1
    push_cast
    omega
  have hrightSide : (e : Site 2) 0 < ((k + k / 12 : ℕ) : ℤ) := by
    have h := hright.2.2.2.2.1
    push_cast
    omega
  have hbound := strip_walk_bounded_between_walls hBT (left.map f) (right.map f) (p.map f)
    (hbox left hleft.2.2.2.2.2.2.2) (hbox right hright.2.2.2.2.2.2.2) hstrip
    hleft.2.1 hleft.2.2.1 hright.2.1 hright.2.2.1 ha hleftSide hrightSide
    htopLeft htopRight (hdis left hl) (hdis right hr)
  intro z hz
  apply (mem_centeredPlaneRectangle _ _ _).mpr
  have hz' : (z : Site 2) ∈ (p.map f).support := by
    rw [SimpleGraph.Walk.support_map]
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  exact ⟨(hbound _ hz').1, (hbound _ hz').2, (hp z hz).1, (hp z hz).2⟩

/-- A simple strip crossing between disjoint KST walls is a KST path. -/
theorem isKSTPath_of_avoiding_walls {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (left : (rectangleGraph Q).Walk c d) (right : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hpath : p.IsPath)
    (hleft : IsKSTPath k left) (hright : IsKSTPath k right)
    (hp : ∀ z ∈ p.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (ha : (a : Site 2) 1 = k) (hb : (b : Site 2) 1 = -(k : ℤ))
    (hl : ∀ z ∈ p.support, z ∉ left.support)
    (hr : ∀ z ∈ p.support, z ∉ right.support)
    (htopLeft : (c : Site 2) 0 ≤ (a : Site 2) 0)
    (htopRight : (a : Site 2) 0 ≤ (e : Site 2) 0) : IsKSTPath k p :=
  isKSTPath_of_strip_walk_between_walls p left right hk hpath hleft hright
    (kst_strip_walk_bounded_between_walls p left right hk hleft hright hp ha hl hr
      htopLeft htopRight) ha hb hl hr htopLeft htopRight

/-- A controlled strip subwalk between KST walls yields a KST subpath. -/
theorem hasKSTSubpath_of_strip_between_walls {Q : Finset (Site 2)}
    {a b u v c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (q : (rectangleGraph Q).Walk u v)
    (left : (rectangleGraph Q).Walk c d) (right : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hp : p.IsPath) (hq : q.IsSubwalk p)
    (hleft : IsKSTPath k left) (hright : IsKSTPath k right)
    (hstrip : ∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (hu : (u : Site 2) 1 = k) (hv : (v : Site 2) 1 = -(k : ℤ))
    (hl : ∀ z ∈ p.support, z ∉ left.support)
    (hr : ∀ z ∈ p.support, z ∉ right.support)
    (htopLeft : (c : Site 2) 0 ≤ (u : Site 2) 0)
    (htopRight : (u : Site 2) 0 ≤ (e : Site 2) 0) : HasKSTSubpath k p := by
  refine ⟨u, v, q, hq, ?_⟩
  exact isKSTPath_of_avoiding_walls q left right hk
    (SimpleGraph.Walk.isPath_of_isSubwalk hq hp) hleft hright hstrip hu hv
    (fun z hz => hl z (hq.support_subset hz))
    (fun z hz => hr z (hq.support_subset hz)) htopLeft htopRight

end Sandpile.External.RSW
