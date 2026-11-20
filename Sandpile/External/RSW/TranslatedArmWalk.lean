import Sandpile.External.RSW.FourArms
import Sandpile.External.RSW.BondWalk

/-!
# Translated arms in larger rectangles

An arm translated vertically can be represented by an open walk in any centered
rectangle containing its translated support, retaining its endpoint coordinates.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A vertically translated arm gives an open walk in a containing centered rectangle. -/
theorem translated_kstArmEvent_exists_walk (s W H : ℕ) (t : ℤ)
    (hw : s + s / 64 ≤ W) (hbottom : -(H : ℤ) ≤ t - s)
    (htop : t + s ≤ (H : ℤ)) {ω : Sym2 (Site 2) → Bool}
    (hω : (ω ∘ Sym2.map (fun z => z + ![0, t])) ∈ kstArmEvent s) :
    ∃ (a b : centeredPlaneRectangle W H) (p : (rectangleGraph (centeredPlaneRectangle W H)).Walk a b),
      p.IsPath ∧ IsBondOpenWalk ω p ∧ (a : Site 2) 1 = t + s ∧ (b : Site 2) 1 = t - s ∧
      -((s / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0 ∧ (a : Site 2) 0 ≤ (s / 64 : ℕ) ∧
      -((s / 64 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧ (b : Site 2) 0 ≤ (s / 64 : ℕ) ∧
      ∀ z ∈ p.support, t - (s : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ t + s := by
  let Q := centeredPlaneRectangle (s + s / 64) s
  let R := centeredPlaneRectangle W H
  let v : Site 2 := ![0, t]
  have hQR (z : Q) : (z : Site 2) + v ∈ R := by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp only [Pi.add_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_zero]
    push_cast at *
    omega
  let f : rectangleGraph Q →g rectangleGraph R :=
    ⟨fun z => ⟨z.val + v, hQR z⟩, fun h => lattice_adj_translate v h⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hh := congrArg (fun z : R => (z : Site 2)) hab
    exact add_right_cancel hh
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  refine ⟨f a, f b, p.bypass.map f, p.bypass_isPath.map hfinj,
    (isBondOpenWalk_map (fun z => z + v) f (fun _ => rfl) ω p.bypass).mpr hp.bypass,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (a : Site 2) 1 + v 1 = t + (s : ℤ)
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ha.1]
    ring
  · change (b : Site 2) 1 + v 1 = t - (s : ℤ)
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hb.1]
    ring
  · change -((s / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0 + v 0
    simp only [v, Matrix.cons_val_zero, add_zero]
    exact ha.2.1
  · change (a : Site 2) 0 + v 0 ≤ ((s / 64 : ℕ) : ℤ)
    simp only [v, Matrix.cons_val_zero, add_zero]
    exact ha.2.2
  · change -((s / 64 : ℕ) : ℤ) ≤ (b : Site 2) 0 + v 0
    simp only [v, Matrix.cons_val_zero, add_zero]
    exact hb.2.1
  · change (b : Site 2) 0 + v 0 ≤ ((s / 64 : ℕ) : ℤ)
    simp only [v, Matrix.cons_val_zero, add_zero]
    exact hb.2.2
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    have hz' := (mem_centeredPlaneRectangle _ _ z').mp z'.property
    change t - (s : ℤ) ≤ (z' : Site 2) 1 + v 1 ∧ (z' : Site 2) 1 + v 1 ≤ t + s
    simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega

end Sandpile.External.RSW
