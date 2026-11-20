import Sandpile.External.RSW.KSTStripSubpath

/-!
# Local KST subpaths

A controlled segment of a path crossing the scale strip contains a KST subpath,
even when the rest of the path leaves the scale rectangle.
-/

namespace Sandpile.External.RSW

/-- A controlled subwalk crossing the scale strip contains a KST subpath. -/
theorem hasKSTSubpath_of_controlled_subwalk {Q : Finset (Site 2)} {a b c d : Q}
    {p : (rectangleGraph Q).Walk a b} (hp : p.IsPath)
    (q : (rectangleGraph Q).Walk c d) (hq : q.IsSubwalk p) {k : ℕ} (hk : 0 < k)
    (hc : (k : ℤ) ≤ (c : Site 2) 1) (hd : (d : Site 2) 1 ≤ -(k : ℤ))
    (hbox : ∀ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 →
      (z : Site 2) 1 ≤ k → (z : Site 2) ∈ centeredPlaneRectangle (k + k / 12) k)
    (htarget : ∀ z ∈ q.support, (z : Site 2) 1 = k ∨ (z : Site 2) 1 = -(k : ℤ) →
      -((k / 12 : ℕ) : ℤ) ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ (k / 12 : ℕ)) :
    HasKSTSubpath k p := by
  have hqp : q.IsPath := SimpleGraph.Walk.isPath_of_isSubwalk hq hp
  obtain ⟨x, y, r, hrq, hrp, hx, hy, hstrip⟩ :=
    exists_vertical_strip_subpath q hqp (B := -(k : ℤ)) (T := k) (by omega) hc hd
  have hxt := htarget x (hrq.support_subset r.start_mem_support) (Or.inl hx)
  have hyt := htarget y (hrq.support_subset r.end_mem_support) (Or.inr hy)
  refine ⟨x, y, r, hrq.trans hq, ⟨hrp, hx, hy, hxt.1, hxt.2, hyt.1, hyt.2, ?_⟩⟩
  intro z hz
  exact hbox z (hrq.support_subset hz) (hstrip z hz).1 (hstrip z hz).2

/-- A strip-crossing subwalk without a KST subpath leaves the scale box or targets. -/
theorem exists_outside_kst_box_or_target_of_no_subpath
    {Q : Finset (Site 2)} {a b c d : Q}
    {p : (rectangleGraph Q).Walk a b} (hp : p.IsPath)
    (q : (rectangleGraph Q).Walk c d) (hq : q.IsSubwalk p) {k : ℕ} (hk : 0 < k)
    (hc : (k : ℤ) ≤ (c : Site 2) 1) (hd : (d : Site 2) 1 ≤ -(k : ℤ))
    (hbad : ¬ HasKSTSubpath k p) :
    (∃ z ∈ q.support, -(k : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ k ∧
      (z : Site 2) ∉ centeredPlaneRectangle (k + k / 12) k) ∨
    ∃ z ∈ q.support, ((z : Site 2) 1 = k ∨ (z : Site 2) 1 = -(k : ℤ)) ∧
      ((z : Site 2) 0 < -((k / 12 : ℕ) : ℤ) ∨ (k / 12 : ℕ) < (z : Site 2) 0) := by
  classical
  by_contra h
  push Not at h
  apply hbad
  apply hasKSTSubpath_of_controlled_subwalk hp q hq hk hc hd
  · intro z hz hlo hhi
    exact h.1 z hz hlo hhi
  · intro z hz hrow
    have ht := h.2 z hz hrow
    omega

end Sandpile.External.RSW
