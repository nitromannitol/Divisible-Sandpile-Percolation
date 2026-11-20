import Sandpile.External.RSW.CorridorBoundaryContact
import Sandpile.External.RSW.UnorderedStripWalls

/-!
# Corridor contacts outside an exceptional strip crossing

An exceptional crossing avoiding two attached walls meets both endpoint segments
outside any strip subpath that meets the boundary rows only at its endpoints.
-/

namespace Sandpile.External.RSW

/-- Boundary contacts between attached walls are outside an exceptional strip subpath. -/
theorem centered_crossing_boundary_contacts_outside_strip_subpath {M N k : ℕ}
    {a b c d x left e f u right s t : centeredPlaneRectangle M N}
    (p : (rectangleGraph (centeredPlaneRectangle M N)).Walk a b)
    (r : (rectangleGraph (centeredPlaneRectangle M N)).Walk c d)
    (q : (rectangleGraph (centeredPlaneRectangle M N)).Walk x left)
    (r' : (rectangleGraph (centeredPlaneRectangle M N)).Walk e f)
    (q' : (rectangleGraph (centeredPlaneRectangle M N)).Walk u right)
    (strip : (rectangleGraph (centeredPlaneRectangle M N)).Walk s t)
    (hk : 0 < k) (hp : p.IsPath) (hsub : strip.IsSubwalk p)
    (ha : (a : Site 2) 1 = N) (hb : (b : Site 2) 1 = -(N : ℤ))
    (hr : IsKSTPath k r) (hr' : IsKSTPath k r')
    (hx : x ∈ r.support) (hu : u ∈ r'.support)
    (hleft : (left : Site 2) 0 = -(M : ℤ)) (hright : (right : Site 2) 0 = M)
    (hstrip : ∀ z ∈ strip.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k)
    (hs : (s : Site 2) 1 = k) (ht : (t : Site 2) 1 = -(k : ℤ))
    (hboundary : ∀ z ∈ strip.support, ((z : Site 2) 1 = k → z = s) ∧
      ((z : Site 2) 1 = -(k : ℤ) → z = t))
    (havoid : ∀ z ∈ p.support, z ∉ r.support ∧ z ∉ q.support ∧
      z ∉ r'.support ∧ z ∉ q'.support)
    (hbad : ¬ HasKSTSubpath k p) :
    (∃ z ∈ p.support, z ∉ strip.support ∧ (z : Site 2) 1 = k ∧
      (((c : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (e : Site 2) 0) ∨
       ((e : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (c : Site 2) 0))) ∧
    (∃ z ∈ p.support, z ∉ strip.support ∧ (z : Site 2) 1 = -(k : ℤ) ∧
      (((d : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (f : Site 2) 0) ∨
       ((f : Site 2) 0 ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (d : Site 2) 0))) := by
  have horder := strip_subpath_endpoints_outside_walls p strip r r' hk hp hsub hr hr'
    hstrip hs ht (fun z hz => (havoid z hz).1) (fun z hz => (havoid z hz).2.2.1) hbad
  obtain ⟨⟨ztop, hztop, hztopRow, hztopOrder⟩,
    ⟨zbottom, hzbottom, hzbottomRow, hzbottomOrder⟩⟩ :=
    centered_crossing_meets_kst_wall_endpoint_segments p r q r' q' ha hb hr hr'
      hx hu hleft hright havoid
  constructor
  · refine ⟨ztop, hztop, ?_, hztopRow, hztopOrder⟩
    intro hz
    have heq := (hboundary ztop hz).1 hztopRow
    have hx := congrArg (fun z : centeredPlaneRectangle M N => (z : Site 2) 0) heq
    rcases horder with h | h <;> rcases hztopOrder with h' | h' <;> omega
  · refine ⟨zbottom, hzbottom, ?_, hzbottomRow, hzbottomOrder⟩
    intro hz
    have heq := (hboundary zbottom hz).2 hzbottomRow
    have hx := congrArg (fun z : centeredPlaneRectangle M N => (z : Site 2) 0) heq
    rcases horder with h | h <;> rcases hzbottomOrder with h' | h' <;> omega

end Sandpile.External.RSW
