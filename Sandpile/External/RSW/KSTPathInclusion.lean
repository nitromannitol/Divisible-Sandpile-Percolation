import Sandpile.External.RSW.QuasiCrossing
import Sandpile.External.RSW.CenteredGeometry

/-!
# Embedding KST paths in larger rectangles

An open KST path remains an open KST path when its ambient induced graph is enlarged.
-/

open Set

namespace Sandpile.External.RSW

/-- Inclusion of induced lattice graphs for nested finite vertex sets. -/
def rectangleGraphInclusion {Q R : Finset (Site 2)} (hQR : Q ⊆ R) : rectangleGraph Q →g rectangleGraph R :=
  ⟨fun z => ⟨z.val, hQR z.property⟩, fun h => h⟩

/-- Inclusion of induced lattice graphs is injective. -/
theorem rectangleGraphInclusion_injective {Q R : Finset (Site 2)} (hQR : Q ⊆ R) :
    Function.Injective (rectangleGraphInclusion hQR) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun z : R => (z : Site 2)) h

/-- A KST path remains a KST path in a larger ambient induced graph. -/
theorem IsKSTPath.map_inclusion {Q R : Finset (Site 2)} (hQR : Q ⊆ R)
    {a b : Q} {p : (rectangleGraph Q).Walk a b} {m : ℕ} (hp : IsKSTPath m p) :
    IsKSTPath m (p.map (rectangleGraphInclusion hQR)) := by
  obtain ⟨hpath, ha, hb, haL, haR, hbL, hbR, hsup⟩ := hp
  refine ⟨hpath.map (rectangleGraphInclusion_injective hQR), ha, hb, haL, haR, hbL, hbR, ?_⟩
  intro z hz
  rw [SimpleGraph.Walk.support_map] at hz
  obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
  exact hsup z' hz'

/-- Inclusion of induced graphs preserves open edges. -/
theorem IsBondOpenWalk.map_inclusion {Q R : Finset (Site 2)} (hQR : Q ⊆ R)
    {a b : Q} {p : (rectangleGraph Q).Walk a b} {ω : Sym2 (Site 2) → Bool}
    (hp : IsBondOpenWalk ω p) :
    IsBondOpenWalk ω (p.map (rectangleGraphInclusion hQR)) := by
  apply (isBondOpenWalk_map id (rectangleGraphInclusion hQR) (fun _ => rfl) ω p).mpr
  simpa only [Sym2.map_id, Function.comp_id] using hp

end Sandpile.External.RSW
