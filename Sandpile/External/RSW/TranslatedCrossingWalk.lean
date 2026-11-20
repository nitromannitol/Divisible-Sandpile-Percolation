import Sandpile.External.RSW.AdjacentSixEvents
import Sandpile.External.RSW.BondWalk

/-!
# Translated rectangle crossings

A translated horizontal crossing can be represented by an open walk in any centered
rectangle containing its support.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A translated crossing gives an open walk in a containing centered rectangle. -/
theorem translated_bondCrossingEvent_exists_walk (w h W H : ℕ) (x y : ℤ)
    (hleft : -(W : ℤ) ≤ x) (hright : x + (w : ℤ) ≤ W)
    (hbottom : -(H : ℤ) ≤ y) (htop : y + (h : ℤ) ≤ H)
    {ω : Sym2 (Site 2) → Bool}
    (hω : (ω ∘ Sym2.map (fun z => z + ![x, y])) ∈ bondCrossingEvent w h) :
    ∃ (a b : centeredPlaneRectangle W H)
      (p : (rectangleGraph (centeredPlaneRectangle W H)).Walk a b),
      IsBondOpenWalk ω p ∧ (a : Site 2) 0 = x ∧ (b : Site 2) 0 = x + w ∧
      ∀ z ∈ p.support, x ≤ (z : Site 2) 0 ∧ (z : Site 2) 0 ≤ x + w ∧
        y ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 ≤ y + h := by
  let Q := planeRectangle w h
  let R := centeredPlaneRectangle W H
  let v : Site 2 := ![x, y]
  have hQR (z : Q) : (z : Site 2) + v ∈ R := by
    have hz := (mem_planeRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp only [Pi.add_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    omega
  let f : rectangleGraph Q →g rectangleGraph R :=
    ⟨fun z => ⟨z.val + v, hQR z⟩, fun h => lattice_adj_translate v h⟩
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  refine ⟨f a, f b, p.map f, ?_, ?_, ?_, ?_⟩
  · exact (isBondOpenWalk_map (fun z => z + v) f (fun _ => rfl) ω p).mpr hp
  · have ha' := (mem_rectangleLeft_planeRectangle a).mp ha
    change (a : Site 2) 0 + v 0 = x
    simp only [v, Matrix.cons_val_zero]
    omega
  · have hb' := (mem_rectangleRight_planeRectangle b).mp hb
    change (b : Site 2) 0 + v 0 = x + w
    simp only [v, Matrix.cons_val_zero]
    omega
  · intro z hz
    rw [SimpleGraph.Walk.support_map] at hz
    obtain ⟨z', _, rfl⟩ := List.mem_map.mp hz
    have hz' := (mem_planeRectangle _ _ z').mp z'.property
    change x ≤ (z' : Site 2) 0 + v 0 ∧ (z' : Site 2) 0 + v 0 ≤ x + w ∧
      y ≤ (z' : Site 2) 1 + v 1 ∧ (z' : Site 2) 1 + v 1 ≤ y + h
    simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    omega


/-- Each auxiliary crossing supplies an open walk in the common large rectangle with
its endpoints on the corresponding outer and inner vertical lines. -/
theorem kstAuxCrossingEvent_exists_walk (m : ℕ) (left : Bool)
    {ω : Sym2 (Site 2) → Bool} (hω : ω ∈ kstAuxCrossingEvent m left) :
    ∃ (a b : centeredPlaneRectangle (5 * m) (4 * m))
      (p : (rectangleGraph (centeredPlaneRectangle (5 * m) (4 * m))).Walk a b),
      IsBondOpenWalk ω p ∧
      (a : Site 2) 0 = (if left then -(5 * (m : ℤ))
        else -(3 * (m : ℤ)) + 3 * ((m / 12 : ℕ) : ℤ)) ∧
      (b : Site 2) 0 = (if left then 3 * (m : ℤ) - 3 * ((m / 12 : ℕ) : ℤ)
        else 5 * (m : ℤ)) := by
  have hβ : m / 12 ≤ m := Nat.div_le_self m 12
  have hsub : 3 * (m / 12) ≤ 8 * m := by omega
  let x : ℤ := if left then -(5 * (m : ℤ))
    else -(3 * (m : ℤ)) + 3 * ((m / 12 : ℕ) : ℤ)
  have hleft : -((5 * m : ℕ) : ℤ) ≤ x := by
    dsimp only [x]
    split <;> push_cast <;> omega
  have hright : x + ((8 * m - 3 * (m / 12) : ℕ) : ℤ) ≤ (5 * m : ℕ) := by
    rw [Nat.cast_sub hsub]
    dsimp only [x]
    split <;> push_cast <;> omega
  have hc : (ω ∘ Sym2.map (fun z => z + ![x, -(4 * (m : ℤ))])) ∈
      bondCrossingEvent (8 * m - 3 * (m / 12)) (8 * m) := by
    simpa only [kstAuxCrossingEvent, mem_preimage, kstAuxCrossingShift, x] using hω
  obtain ⟨a, b, p, hp, ha, hb, _⟩ := translated_bondCrossingEvent_exists_walk
    (8 * m - 3 * (m / 12)) (8 * m) (5 * m) (4 * m) x (-(4 * (m : ℤ)))
    hleft hright (by push_cast; omega) (by push_cast; omega) hc
  refine ⟨a, b, p, hp, ha, ?_⟩
  rw [hb, Nat.cast_sub hsub]
  dsimp only [x]
  split <;> push_cast <;> omega

end Sandpile.External.RSW
