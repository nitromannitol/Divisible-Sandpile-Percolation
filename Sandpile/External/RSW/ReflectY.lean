import Sandpile.External.RSW.BridgePieceSymmetry
import Sandpile.External.RSW.TopConnectedPath

/-!
# Reflection in the horizontal axis

Horizontal reflection acts on centered rectangles, open walks, and KST paths.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Reflection of a centered rectangle in the horizontal axis. -/
def reflectYRectangle (W n : ℕ) :
    rectangleGraph (centeredPlaneRectangle W n) →g rectangleGraph (centeredPlaneRectangle W n) where
  toFun z := ⟨reflectPlaneCoordinates false true z, by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp [reflectPlaneCoordinates]
    omega⟩
  map_rel' h := lattice_adj_reflectPlaneCoordinates false true h

/-- The site underlying a reflected vertex is the reflected site. -/
theorem reflectYRectangle_apply (W n : ℕ) (z : centeredPlaneRectangle W n) :
    (reflectYRectangle W n z : Site 2) = reflectPlaneCoordinates false true z := rfl

/-- Horizontal reflection of a centered rectangle is injective. -/
theorem reflectYRectangle_injective (W n : ℕ) : Function.Injective (reflectYRectangle W n) := by
  intro a b hab
  apply Subtype.ext
  have he : reflectPlaneCoordinates false true (a : Site 2) =
      reflectPlaneCoordinates false true (b : Site 2) :=
    congrArg (fun z : centeredPlaneRectangle W n => (z : Site 2)) hab
  exact (reflectPlaneCoordinates_involutive false true).injective he

/-- A reflected open walk is open in the reflected configuration. -/
theorem IsBondOpenWalk.map_reflectY {W n : ℕ} {a b : centeredPlaneRectangle W n}
    {p : (rectangleGraph (centeredPlaneRectangle W n)).Walk a b} {ω : Sym2 (Site 2) → Bool}
    (hp : IsBondOpenWalk ω p) :
    IsBondOpenWalk (ω ∘ Sym2.map (reflectPlaneCoordinates false true))
      (p.map (reflectYRectangle W n)) := by
  apply (isBondOpenWalk_map (reflectPlaneCoordinates false true) (reflectYRectangle W n)
    (fun _ => rfl) _ p).mpr
  have he : (ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∘
      Sym2.map (reflectPlaneCoordinates false true) = ω := by
    funext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Function.comp_apply, Sym2.map_mk]
      rw [reflectPlaneCoordinates_involutive false true x,
        reflectPlaneCoordinates_involutive false true y]
  rw [he]
  exact hp

/-- Reflecting and reversing a KST path yields another KST path at the same scale. -/
theorem IsKSTPath.reverse_map_reflectY {W n m : ℕ}
    {a b : centeredPlaneRectangle W n}
    {p : (rectangleGraph (centeredPlaneRectangle W n)).Walk a b} (hp : IsKSTPath m p) :
    IsKSTPath m (p.reverse.map (reflectYRectangle W n)) := by
  obtain ⟨hpath, ha, hb, haL, haR, hbL, hbR, hsup⟩ := hp
  refine ⟨hpath.reverse.map (reflectYRectangle_injective W n), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change -(b : Site 2) 1 = (m : ℤ)
    omega
  · change -(a : Site 2) 1 = -(m : ℤ)
    omega
  · change -((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0
    exact hbL
  · change (b : Site 2) 0 ≤ ((m / 12 : ℕ) : ℤ)
    exact hbR
  · change -((m / 12 : ℕ) : ℤ) ≤ (a : Site 2) 0
    exact haL
  · change (a : Site 2) 0 ≤ ((m / 12 : ℕ) : ℤ)
    exact haR
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hz'
    have hh := (mem_centeredPlaneRectangle _ _ z').mp (hsup z' hz')
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp only [reflectYRectangle_apply, reflectPlaneCoordinates, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega

end Sandpile.External.RSW
