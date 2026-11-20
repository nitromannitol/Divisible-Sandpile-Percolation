import Sandpile.External.RSW.HorizontalCrossingWall
import Sandpile.External.RSW.EmbeddedHorizontalPath

/-!
# Side walls from spanning open walks

A side walk spanning the inner rectangle gives a KST wall when the two
central KST paths connect to opposite horizontal sides of that rectangle.
-/

namespace Sandpile.External.RSW

/-- A spanning side walk and two vertically attached KST paths give a side wall. -/
theorem kstWallEvent_of_spanning_side_walk (n k M W : ℕ) (left : Bool)
    (hk : 12 ≤ k) (hM : k + k / 12 + 1 ≤ M) (hN : k + 1 ≤ n)
    (hwidth : M ≤ W) (hW : W = n + 3 * (n / 12))
    {ω : Sym2 (Site 2) → Bool} {a b : centeredPlaneRectangle W n}
    {c d x y e f u v : centeredPlaneRectangle M n}
    (walk : (rectangleGraph (centeredPlaneRectangle W n)).Walk a b)
    (lower : (rectangleGraph (centeredPlaneRectangle M n)).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle M n)).Walk x y)
    (upper : (rectangleGraph (centeredPlaneRectangle M n)).Walk e f)
    (upperLink : (rectangleGraph (centeredPlaneRectangle M n)).Walk u v)
    (hwalk : IsBondOpenWalk ω walk)
    (ha : (a : Site 2) 0 = (if left then -(W : ℤ) else (W : ℤ)))
    (hspan : ((a : Site 2) 0 ≤ -(M : ℤ) ∧ (M : ℤ) ≤ (b : Site 2) 0) ∨
      ((b : Site 2) 0 ≤ -(M : ℤ) ∧ (M : ℤ) ≤ (a : Site 2) 0))
    (hl : IsKSTPath k lower) (hu : IsKSTPath k upper)
    (hx : x ∈ lower.support) (hu' : u ∈ upper.support)
    (hlopen : IsBondOpenWalk ω lower) (hllopen : IsBondOpenWalk ω lowerLink)
    (huopen : IsBondOpenWalk ω upper) (hulopen : IsBondOpenWalk ω upperLink)
    (hy : (y : Site 2) 1 = -(n : ℤ)) (hv : (v : Site 2) 1 = n) :
    ω ∈ kstWallEvent n k left := by
  subst W
  have hmpos : 0 < M := by omega
  have hex : ∃ (s t : centeredPlaneRectangle M n)
      (cross : (rectangleGraph (centeredPlaneRectangle M n)).Walk s t),
      cross.IsPath ∧ IsBondOpenWalk ω cross ∧
      (s : Site 2) 0 = -(M : ℤ) ∧ (t : Site 2) 0 = M ∧
      ∀ z ∈ cross.support, ∃ w ∈ walk.support, (w : Site 2) = (z : Site 2) := by
    rcases hspan with hs | hs
    · exact exists_open_path_in_embedded_rectangle hmpos walk hwalk hs.1 hs.2
    · obtain ⟨s, t, cross, hp, ho, hs, ht, hsupport⟩ :=
        exists_open_path_in_embedded_rectangle hmpos walk.reverse hwalk.reverse hs.1 hs.2
      refine ⟨s, t, cross, hp, ho, hs, ht, ?_⟩
      intro z hz
      obtain ⟨w, hw, he⟩ := hsupport z hz
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hw
      exact ⟨w, hw, he⟩
  obtain ⟨s, t, cross, hcross, hcopen, hs, ht, hsupport⟩ := hex
  apply kstWallEvent_of_embedded_horizontal_crossing n k M left hk hM hN hwidth
    walk cross.reverse lower lowerLink upper upperLink hwalk ha hcross.reverse hcopen.reverse
    ht hs ?_ hl hu hx hu' hlopen hllopen huopen hulopen hy hv
  intro z hz
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz
  exact hsupport z hz

end Sandpile.External.RSW
