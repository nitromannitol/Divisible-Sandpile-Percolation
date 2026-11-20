import Sandpile.External.RSW.StripPathObstruction
import Sandpile.External.RSW.StripWallIntersection

/-!
# Strip obstructions in the presence of a wall

A strip path avoiding a KST wall cannot have endpoints on opposite target arcs.
When it has no smaller KST subpath, this narrows its possible obstructions.
-/

namespace Sandpile.External.RSW

/-- A strip path avoiding a KST wall has no pair of opposite target endpoints. -/
theorem kst_strip_endpoints_of_disjoint {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (q : (rectangleGraph Q).Walk c d)
    {k : ℕ} (hk : 0 < k) (hp : IsKSTPath k p)
    (hq : ∀ z ∈ q.support, (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (hc : (c : Site 2) 1 = k) (hd : (d : Site 2) 1 = -(k : ℤ))
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    ¬ (((c : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ) ∧
        ((k / 12 : ℕ) : ℤ) ≤ (d : Site 2) 0) ∨
      (((k / 12 : ℕ) : ℤ) ≤ (c : Site 2) 0 ∧
        (d : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ))) := by
  intro hside
  obtain ⟨z, hzp, hzq⟩ :=
    kstPath_intersects_strip_walk_of_opposite_targets p q hk hp hq hc hd hside
  exact hdis z hzp hzq

/-- A strip subpath without a smaller KST subpath either leaves the scale box or
has an endpoint outside the target without crossing the opposite target arc. -/
theorem exists_strip_wall_obstruction {Q : Finset (Site 2)} {a b c d : Q}
    (p : (rectangleGraph Q).Walk a b) (wall : (rectangleGraph Q).Walk c d)
    (hp : p.IsPath) {k : ℕ} (hk : 0 < k) (hwall : IsKSTPath k wall)
    (ha : (k : ℤ) ≤ (a : Site 2) 1) (hb : (b : Site 2) 1 ≤ -(k : ℤ))
    (hbad : ¬ HasKSTSubpath k p)
    (hdis : ∀ z ∈ wall.support, z ∉ p.support) :
    ∃ (u v : Q) (q : (rectangleGraph Q).Walk u v),
      q.IsSubwalk p ∧ q.IsPath ∧ (u : Site 2) 1 = k ∧ (v : Site 2) 1 = -(k : ℤ) ∧
      (∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k) ∧
      (∀ z ∈ q.support, ((z : Site 2) 1 = k → z = u) ∧
        ((z : Site 2) 1 = -(k : ℤ) → z = v)) ∧
      ((∃ z ∈ q.support, (z : Site 2) 0 < -((k + k / 12 : ℕ) : ℤ) ∨
          (k + k / 12 : ℕ) < (z : Site 2) 0) ∨
       (((u : Site 2) 0 < -((k / 12 : ℕ) : ℤ) ∨
          (k / 12 : ℕ) < (u : Site 2) 0 ∨
          (v : Site 2) 0 < -((k / 12 : ℕ) : ℤ) ∨
          (k / 12 : ℕ) < (v : Site 2) 0) ∧
        ¬ (((u : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ) ∧
            ((k / 12 : ℕ) : ℤ) ≤ (v : Site 2) 0) ∨
          (((k / 12 : ℕ) : ℤ) ≤ (u : Site 2) 0 ∧
            (v : Site 2) 0 ≤ -((k / 12 : ℕ) : ℤ))))) := by
  obtain ⟨u, v, q, hsub, hpath, hu, hv, hstrip, hboundary, hobstruction⟩ :=
    exists_strip_subpath_obstruction p hp hk ha hb hbad
  refine ⟨u, v, q, hsub, hpath, hu, hv, hstrip, hboundary, ?_⟩
  by_cases hbox : ∀ z ∈ q.support,
      (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k
  · right
    constructor
    · rcases hobstruction with h | h | h | h | ⟨z, hz, hzside⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · have hzbox := (mem_centeredPlaneRectangle _ _ _).mp (hbox z hz)
        omega
    · apply kst_strip_endpoints_of_disjoint wall q hk hwall hbox hu hv
      intro z hz hzq
      exact hdis z hz (hsub.support_subset hzq)
  · left
    push Not at hbox
    obtain ⟨z, hz, hzbox⟩ := hbox
    refine ⟨z, hz, ?_⟩
    have hzstrip := hstrip z hz
    have hbox' := (mem_centeredPlaneRectangle (k + k / 12) k (z : Site 2))
    by_contra hn
    apply hzbox
    apply hbox'.mpr
    omega

end Sandpile.External.RSW
