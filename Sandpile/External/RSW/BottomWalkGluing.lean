import Sandpile.External.RSW.BottomAlternation
import Sandpile.External.RSW.BondWalk
import Sandpile.External.RSW.CenteredGeometry

/-!
# Gluing bottom-to-bottom walks

Two bottom walks whose horizontal endpoint intervals overlap can be replaced by one open
bottom walk spanning both intervals. Alternating endpoints force intersection; nested
intervals need no joining.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Rectangle walks with weakly alternating bottom endpoints meet. -/
theorem bottom_rectangle_walks_intersect {M n : ℕ}
    {a b c d : centeredPlaneRectangle M n}
    (p : (rectangleGraph (centeredPlaneRectangle M n)).Walk a b)
    (q : (rectangleGraph (centeredPlaneRectangle M n)).Walk c d)
    (ha : (a : Site 2) 1 = -(n : ℤ)) (hb : (b : Site 2) 1 = -(n : ℤ))
    (hc : (c : Site 2) 1 = -(n : ℤ)) (hd : (d : Site 2) 1 = -(n : ℤ))
    (hac : (a : Site 2) 0 ≤ (c : Site 2) 0)
    (hcb : (c : Site 2) 0 ≤ (b : Site 2) 0)
    (hbd : (b : Site 2) 0 ≤ (d : Site 2) 0) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  by_cases he : (a : Site 2) 0 = (c : Site 2) 0
  · have heq : a = c := Subtype.ext (LatticeModels.Site.eq_iff_two.mpr ⟨he, by omega⟩)
    exact ⟨a, p.start_mem_support, heq ▸ q.start_mem_support⟩
  by_cases he' : (c : Site 2) 0 = (b : Site 2) 0
  · have heq : c = b := Subtype.ext (LatticeModels.Site.eq_iff_two.mpr ⟨he', by omega⟩)
    exact ⟨b, p.end_mem_support, heq ▸ q.start_mem_support⟩
  by_cases he'' : (b : Site 2) 0 = (d : Site 2) 0
  · have heq : b = d := Subtype.ext (LatticeModels.Site.eq_iff_two.mpr ⟨he'', by omega⟩)
    exact ⟨b, p.end_mem_support, heq ▸ q.end_mem_support⟩
  let f : rectangleGraph (centeredPlaneRectangle M n) →g LatticeModels.zdGraph 2 :=
    ⟨Subtype.val, fun h => by rw [← lattice_eq_zdGraph]; exact h⟩
  have hp : ∀ z ∈ (p.map f).support,
      -(M : ℤ) ≤ z 0 ∧ z 0 ≤ M ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp z'.property
  have hq : ∀ z ∈ (q.map f).support,
      -(M : ℤ) ≤ z 0 ∧ z 0 ≤ M ∧ -(n : ℤ) ≤ z 1 ∧ z 1 ≤ n := by
    intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    exact (mem_centeredPlaneRectangle _ _ z').mp z'.property
  have hac' : (f a) 0 < (f c) 0 := by
    change (a : Site 2) 0 < (c : Site 2) 0
    omega
  have hcb' : (f c) 0 < (f b) 0 := by
    change (c : Site 2) 0 < (b : Site 2) 0
    omega
  have hbd' : (f b) 0 < (f d) 0 := by
    change (b : Site 2) 0 < (d : Site 2) 0
    omega
  obtain ⟨z, hzp, hzq⟩ := bottom_alternating_paths_intersect (p.map f) (q.map f) hp hq
    ha hc hb hd hac' hcb' hbd'
  rw [SimpleGraph.Walk.support_map] at hzp hzq
  obtain ⟨x, hxp, hx⟩ := List.mem_map.mp hzp
  obtain ⟨y, hyq, hy⟩ := List.mem_map.mp hzq
  have hxy : x = y := Subtype.ext (hx.trans hy.symm)
  exact ⟨x, hxp, hxy ▸ hyq⟩

/-- Two open bottom walks with overlapping endpoint intervals can be replaced by an
open bottom walk spanning both intervals. -/
theorem exists_open_bottom_walk_spanning {M n : ℕ} {ω : Sym2 (Site 2) → Bool}
    {a b c d : centeredPlaneRectangle M n}
    (p : (rectangleGraph (centeredPlaneRectangle M n)).Walk a b)
    (q : (rectangleGraph (centeredPlaneRectangle M n)).Walk c d)
    (hp : IsBondOpenWalk ω p) (hq : IsBondOpenWalk ω q)
    (ha : (a : Site 2) 1 = -(n : ℤ)) (hb : (b : Site 2) 1 = -(n : ℤ))
    (hc : (c : Site 2) 1 = -(n : ℤ)) (hd : (d : Site 2) 1 = -(n : ℤ))
    (hab : (a : Site 2) 0 ≤ (b : Site 2) 0)
    (hcd : (c : Site 2) 0 ≤ (d : Site 2) 0)
    (had : (a : Site 2) 0 ≤ (d : Site 2) 0)
    (hcb : (c : Site 2) 0 ≤ (b : Site 2) 0) :
    ∃ (x y : centeredPlaneRectangle M n)
      (r : (rectangleGraph (centeredPlaneRectangle M n)).Walk x y),
      IsBondOpenWalk ω r ∧ (x : Site 2) 1 = -(n : ℤ) ∧ (y : Site 2) 1 = -(n : ℤ) ∧
      (x : Site 2) 0 ≤ (a : Site 2) 0 ∧ (x : Site 2) 0 ≤ (c : Site 2) 0 ∧
      (b : Site 2) 0 ≤ (y : Site 2) 0 ∧ (d : Site 2) 0 ≤ (y : Site 2) 0 := by
  by_cases hac : (a : Site 2) 0 ≤ (c : Site 2) 0
  · by_cases hdb : (d : Site 2) 0 ≤ (b : Site 2) 0
    · exact ⟨a, b, p, hp, ha, hb, le_rfl, hac, le_rfl, hdb⟩
    · obtain ⟨x, hxp, hxq⟩ := bottom_rectangle_walks_intersect p q ha hb hc hd
        hac hcb (by omega)
      obtain ⟨p', hp', _⟩ := exists_openWalk_of_mem_support p hp p.start_mem_support hxp
      obtain ⟨q', hq', _⟩ := exists_openWalk_of_mem_support q hq hxq q.end_mem_support
      exact ⟨a, d, p'.append q', hp'.append hq', ha, hd, le_rfl, hac, by omega, le_rfl⟩
  · by_cases hbd : (b : Site 2) 0 ≤ (d : Site 2) 0
    · exact ⟨c, d, q, hq, hc, hd, by omega, le_rfl, hbd, le_rfl⟩
    · obtain ⟨x, hxq, hxp⟩ := bottom_rectangle_walks_intersect q p hc hd ha hb
        (by omega) had (by omega)
      obtain ⟨q', hq', _⟩ := exists_openWalk_of_mem_support q hq q.start_mem_support hxq
      obtain ⟨p', hp', _⟩ := exists_openWalk_of_mem_support p hp hxp p.end_mem_support
      exact ⟨c, b, q'.append p', hq'.append hp', hc, hb, by omega, le_rfl, le_rfl, by omega⟩

end Sandpile.External.RSW
