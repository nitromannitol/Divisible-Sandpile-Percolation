import Sandpile.External.RSW.KSTStripConfinement
import Sandpile.External.RSW.VerticalStripSubpath

/-!
# Strip crossings between unordered walls

A strip crossing between two KST paths is a KST path regardless of the order
in which the walls are named.
-/

namespace Sandpile.External.RSW

/-- A simple strip crossing starting between two walls is a KST path. -/
theorem isKSTPath_of_between_unordered_walls {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (first : (rectangleGraph Q).Walk c d) (second : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hpath : p.IsPath)
    (hfirst : IsKSTPath k first) (hsecond : IsKSTPath k second)
    (hp : ∀ z ∈ p.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (ha : (a : Site 2) 1 = k) (hb : (b : Site 2) 1 = -(k : ℤ))
    (hfirstDisjoint : ∀ z ∈ p.support, z ∉ first.support)
    (hsecondDisjoint : ∀ z ∈ p.support, z ∉ second.support)
    (hbetween : ((c : Site 2) 0 ≤ (a : Site 2) 0 ∧
        (a : Site 2) 0 ≤ (e : Site 2) 0) ∨
      ((e : Site 2) 0 ≤ (a : Site 2) 0 ∧ (a : Site 2) 0 ≤ (c : Site 2) 0)) :
    IsKSTPath k p := by
  rcases hbetween with h | h
  · exact isKSTPath_of_avoiding_walls p first second hk hpath hfirst hsecond hp ha hb
      hfirstDisjoint hsecondDisjoint h.1 h.2
  · exact isKSTPath_of_avoiding_walls p second first hk hpath hsecond hfirst hp ha hb
      hsecondDisjoint hfirstDisjoint h.1 h.2

/-- Every strip subpath of an exceptional path starts outside the wall endpoints. -/
theorem strip_subpath_outside_wall_endpoints {Q : Finset (Site 2)}
    {a b u v c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (q : (rectangleGraph Q).Walk u v)
    (first : (rectangleGraph Q).Walk c d) (second : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hpath : p.IsPath) (hsub : q.IsSubwalk p)
    (hfirst : IsKSTPath k first) (hsecond : IsKSTPath k second)
    (hstrip : ∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (hu : (u : Site 2) 1 = k) (hv : (v : Site 2) 1 = -(k : ℤ))
    (hfirstDisjoint : ∀ z ∈ p.support, z ∉ first.support)
    (hsecondDisjoint : ∀ z ∈ p.support, z ∉ second.support)
    (hbad : ¬ HasKSTSubpath k p) :
    ((u : Site 2) 0 < (c : Site 2) 0 ∧ (u : Site 2) 0 < (e : Site 2) 0) ∨
      ((c : Site 2) 0 < (u : Site 2) 0 ∧ (e : Site 2) 0 < (u : Site 2) 0) := by
  have hn : ¬ (((c : Site 2) 0 ≤ (u : Site 2) 0 ∧
        (u : Site 2) 0 ≤ (e : Site 2) 0) ∨
      ((e : Site 2) 0 ≤ (u : Site 2) 0 ∧ (u : Site 2) 0 ≤ (c : Site 2) 0)) := by
    intro hbetween
    apply hbad
    refine ⟨u, v, q, hsub, ?_⟩
    exact isKSTPath_of_between_unordered_walls q first second hk
      (SimpleGraph.Walk.isPath_of_isSubwalk hsub hpath) hfirst hsecond hstrip hu hv
      (fun z hz => hfirstDisjoint z (hsub.support_subset hz))
      (fun z hz => hsecondDisjoint z (hsub.support_subset hz)) hbetween
  omega

/-- A path without a KST subpath has a strip crossing starting outside both wall endpoints. -/
theorem exists_strip_subpath_outside_wall_endpoints {Q : Finset (Site 2)}
    {a b c d e f : Q} (p : (rectangleGraph Q).Walk a b)
    (first : (rectangleGraph Q).Walk c d) (second : (rectangleGraph Q).Walk e f)
    {k : ℕ} (hk : 0 < k) (hpath : p.IsPath)
    (hfirst : IsKSTPath k first) (hsecond : IsKSTPath k second)
    (ha : (k : ℤ) ≤ (a : Site 2) 1) (hb : (b : Site 2) 1 ≤ -(k : ℤ))
    (hfirstDisjoint : ∀ z ∈ p.support, z ∉ first.support)
    (hsecondDisjoint : ∀ z ∈ p.support, z ∉ second.support)
    (hbad : ¬ HasKSTSubpath k p) :
    ∃ (u v : Q) (q : (rectangleGraph Q).Walk u v),
      q.IsSubwalk p ∧ q.IsPath ∧ (u : Site 2) 1 = k ∧ (v : Site 2) 1 = -(k : ℤ) ∧
      (∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k) ∧
      (((u : Site 2) 0 < (c : Site 2) 0 ∧ (u : Site 2) 0 < (e : Site 2) 0) ∨
       ((c : Site 2) 0 < (u : Site 2) 0 ∧ (e : Site 2) 0 < (u : Site 2) 0)) := by
  obtain ⟨u, v, q, hsub, hqpath, hu, hv, hstrip⟩ :=
    exists_vertical_strip_subpath p hpath (B := -(k : ℤ)) (T := k) (by omega) ha hb
  refine ⟨u, v, q, hsub, hqpath, hu, hv, hstrip, ?_⟩
  exact strip_subpath_outside_wall_endpoints p q first second hk hpath hsub hfirst hsecond
    hstrip hu hv hfirstDisjoint hsecondDisjoint hbad

end Sandpile.External.RSW
