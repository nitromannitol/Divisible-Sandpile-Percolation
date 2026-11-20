import Sandpile.External.RSW.LocalKSTSubpath

/-!
# Obstructions on a strip subpath

If a simple vertical crossing has no KST subpath, a contiguous strip crossing
must have an endpoint outside its target or a vertex beyond a vertical side.
-/

namespace Sandpile.External.RSW

/-- A path without a KST subpath has a strip subpath with a boundary obstruction. -/
theorem exists_strip_subpath_obstruction {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b) (hp : p.IsPath) {k : ℕ} (hk : 0 < k)
    (ha : (k : ℤ) ≤ (a : Site 2) 1) (hb : (b : Site 2) 1 ≤ -(k : ℤ))
    (hbad : ¬ HasKSTSubpath k p) :
    ∃ (c d : Q) (q : (rectangleGraph Q).Walk c d),
      q.IsSubwalk p ∧ q.IsPath ∧ (c : Site 2) 1 = k ∧ (d : Site 2) 1 = -(k : ℤ) ∧
      (∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k) ∧
      (∀ z ∈ q.support, ((z : Site 2) 1 = k → z = c) ∧
        ((z : Site 2) 1 = -(k : ℤ) → z = d)) ∧
      ((c : Site 2) 0 < -((k / 12 : ℕ) : ℤ) ∨
        (k / 12 : ℕ) < (c : Site 2) 0 ∨
        (d : Site 2) 0 < -((k / 12 : ℕ) : ℤ) ∨
        (k / 12 : ℕ) < (d : Site 2) 0 ∨
        ∃ z ∈ q.support, (z : Site 2) 0 < -((k + k / 12 : ℕ) : ℤ) ∨
          (k + k / 12 : ℕ) < (z : Site 2) 0) := by
  obtain ⟨c, d, q, hsub, hpath, hc, hd, hstrip, hboundary⟩ :=
    exists_vertical_strip_subpath_with_boundary p hp (B := -(k : ℤ)) (T := k)
      (by omega) ha hb
  refine ⟨c, d, q, hsub, hpath, hc, hd, hstrip, hboundary, ?_⟩
  by_contra hn
  push Not at hn
  apply hbad
  refine ⟨c, d, q, hsub, ⟨hpath, hc, hd, ?_, ?_, ?_, ?_, ?_⟩⟩
  · omega
  · omega
  · omega
  · omega
  · intro z hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    have hzside := hn.2.2.2.2 z hz
    exact ⟨by omega, by omega, (hstrip z hz).1, (hstrip z hz).2⟩

end Sandpile.External.RSW
