import Sandpile.External.RSW.HorizontalKSTObstruction
import Sandpile.External.RSW.WallGluing
import Sandpile.External.RSW.KSTPathInclusion

/-!
# Walls from embedded horizontal crossings

A side walk containing an inner horizontal crossing gives a quasi-crossing wall
when two KST paths are connected to opposite horizontal sides of the inner box.
-/

open Set

namespace Sandpile.External.RSW

/-- An embedded open horizontal crossing supplies the corresponding KST wall. -/
theorem kstWallEvent_of_embedded_horizontal_crossing (n k M : ℕ) (left : Bool)
    (hk : 12 ≤ k) (hM : k + k / 12 + 1 ≤ M) (hN : k + 1 ≤ n)
    (hwidth : M ≤ n + 3 * (n / 12))
    {ω : Sym2 (Site 2) → Bool}
    {a b : centeredPlaneRectangle (n + 3 * (n / 12)) n}
    {c d x y e f u v s t : centeredPlaneRectangle M n}
    (walk : (rectangleGraph (centeredPlaneRectangle (n + 3 * (n / 12)) n)).Walk a b)
    (cross : (rectangleGraph (centeredPlaneRectangle M n)).Walk s t)
    (lower : (rectangleGraph (centeredPlaneRectangle M n)).Walk c d)
    (lowerLink : (rectangleGraph (centeredPlaneRectangle M n)).Walk x y)
    (upper : (rectangleGraph (centeredPlaneRectangle M n)).Walk e f)
    (upperLink : (rectangleGraph (centeredPlaneRectangle M n)).Walk u v)
    (hwalk : IsBondOpenWalk ω walk)
    (ha : (a : Site 2) 0 = (if left then -((n + 3 * (n / 12) : ℕ) : ℤ)
      else ((n + 3 * (n / 12) : ℕ) : ℤ)))
    (hcross : cross.IsPath) (hcopen : IsBondOpenWalk ω cross)
    (hs : (s : Site 2) 0 = M) (ht : (t : Site 2) 0 = -(M : ℤ))
    (hsupport : ∀ z ∈ cross.support, ∃ w ∈ walk.support, (w : Site 2) = (z : Site 2))
    (hl : IsKSTPath k lower) (hu : IsKSTPath k upper)
    (hx : x ∈ lower.support) (hu' : u ∈ upper.support)
    (hlopen : IsBondOpenWalk ω lower) (hllopen : IsBondOpenWalk ω lowerLink)
    (huopen : IsBondOpenWalk ω upper) (hulopen : IsBondOpenWalk ω upperLink)
    (hy : (y : Site 2) 1 = -(n : ℤ)) (hv : (v : Site 2) 1 = n) :
    ω ∈ kstWallEvent n k left := by
  let Q := centeredPlaneRectangle M n
  let R := centeredPlaneRectangle (n + 3 * (n / 12)) n
  have hQR : Q ⊆ R := by
    intro z hz
    have hz' := (mem_centeredPlaneRectangle _ _ _).mp hz
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    omega
  let F := rectangleGraphInclusion hQR
  have hpathWall {s t : Q} (path : (rectangleGraph Q).Walk s t)
      (hpath : IsKSTPath k path) (hopen : IsBondOpenWalk ω path)
      (hcontact : ∃ z ∈ path.support, ∃ w ∈ walk.support, (w : Site 2) = (z : Site 2)) :
      ω ∈ kstWallEvent n k left := by
    obtain ⟨z, hz, w, hw, he⟩ := hcontact
    obtain ⟨link, hlink, _⟩ := exists_openWalk_of_mem_support walk hwalk hw walk.start_mem_support
    have he' : F z = w := Subtype.ext he.symm
    refine ⟨F s, F t, F z, a, path.map F, ?_, hpath.map_inclusion hQR, ?_, ha,
      hopen.map_inclusion hQR, ?_⟩
    · exact he' ▸ link
    · rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨z, hz, rfl⟩
    · exact he' ▸ hlink
  have hgeometry := horizontal_crossing_meets_walls_or_kst_subpath M n k hk hM hN
    cross lower lowerLink upper upperLink hcross hs ht hl hu hx hu' hy hv
  rcases hgeometry with hsub | hsubrev | ⟨z, hzc, hz⟩
  · obtain ⟨i, j, path, hsub, hpath⟩ := hsub
    apply hpathWall path hpath (hcopen.subwalk hsub)
    exact ⟨i, path.start_mem_support, hsupport i (hsub.support_subset path.start_mem_support)⟩
  · obtain ⟨i, j, path, hsub, hpath⟩ := hsubrev
    apply hpathWall path hpath (hcopen.reverse.subwalk hsub)
    have hi : i ∈ cross.support := by
      have hh := hsub.support_subset path.start_mem_support
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hh
    exact ⟨i, path.start_mem_support, hsupport i hi⟩
  · obtain ⟨w, hw, he⟩ := hsupport z hzc
    have he' : F z = w := Subtype.ext he.symm
    have hxF : F x ∈ (lower.map F).support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨x, hx, rfl⟩
    have huF : F u ∈ (upper.map F).support := by
      rw [SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨u, hu', rfl⟩
    rcases hz with hz | hz | hz | hz
    · have hzF : w ∈ (lower.map F).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨z, hz, he'⟩
      exact kstWallEvent_of_intersecting_walks n k left (lower.map F) (lowerLink.map F) walk
        (hl.map_inclusion hQR) hxF (hlopen.map_inclusion hQR) (hllopen.map_inclusion hQR)
        hwalk ha ⟨w, Or.inl hzF, hw⟩
    · have hzF : w ∈ (lowerLink.map F).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨z, hz, he'⟩
      exact kstWallEvent_of_intersecting_walks n k left (lower.map F) (lowerLink.map F) walk
        (hl.map_inclusion hQR) hxF (hlopen.map_inclusion hQR) (hllopen.map_inclusion hQR)
        hwalk ha ⟨w, Or.inr hzF, hw⟩
    · have hzF : w ∈ (upper.map F).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨z, hz, he'⟩
      exact kstWallEvent_of_intersecting_walks n k left (upper.map F) (upperLink.map F) walk
        (hu.map_inclusion hQR) huF (huopen.map_inclusion hQR) (hulopen.map_inclusion hQR)
        hwalk ha ⟨w, Or.inl hzF, hw⟩
    · have hzF : w ∈ (upperLink.map F).support := by
        rw [SimpleGraph.Walk.support_map, List.mem_map]
        exact ⟨z, hz, he'⟩
      exact kstWallEvent_of_intersecting_walks n k left (upper.map F) (upperLink.map F) walk
        (hu.map_inclusion hQR) huF (huopen.map_inclusion hQR) (hulopen.map_inclusion hQR)
        hwalk ha ⟨w, Or.inr hzF, hw⟩

end Sandpile.External.RSW
