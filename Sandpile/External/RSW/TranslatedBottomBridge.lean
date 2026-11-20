import Sandpile.External.RSW.CornerBridge
import Sandpile.External.RSW.BottomWalkChain
import Sandpile.External.RSW.SpanningWalkCrossing

/-!
# Translated bottom bridges

A translated bottom bridge supplies an open bottom walk inside a common larger
rectangle, spanning the translated central interval.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A translated bottom bridge gives a walk spanning its central interval in the
larger centered rectangle. -/
theorem translated_kstBottomBridge_spanning (m : ℕ) (t : ℤ)
    (hleft : -(8 * (m : ℤ)) + ((m / 12 : ℕ) : ℤ) ≤ t)
    (hright : t ≤ 8 * (m : ℤ) - ((m / 12 : ℕ) : ℤ))
    {ω : Sym2 (Site 2) → Bool}
    (h : (ω ∘ Sym2.map (fun z => z + ![t, 0])) ∈ kstBottomBridgeEvent m) :
    ∃ (a b : centeredPlaneRectangle (9 * m) m)
      (p : (rectangleGraph (centeredPlaneRectangle (9 * m) m)).Walk a b),
      IsBondOpenWalk ω p ∧ (a : Site 2) 1 = -(m : ℤ) ∧ (b : Site 2) 1 = -(m : ℤ) ∧
      (a : Site 2) 0 ≤ t - ((m / 12 : ℕ) : ℤ) ∧
      t + ((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 := by
  let Q := centeredPlaneRectangle (m + m / 12) m
  let R := centeredPlaneRectangle (9 * m) m
  let v : Site 2 := ![t, 0]
  have hQR (z : Q) : (z : Site 2) + v ∈ R := by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp only [Pi.add_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_zero]
    push_cast at *
    omega
  let f : rectangleGraph Q →g rectangleGraph R :=
    ⟨fun z => ⟨z.val + v, hQR z⟩, fun h => lattice_adj_translate v h⟩
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨f a, f b, p.map f, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isBondOpenWalk_map (fun z => z + v) f (fun _ => rfl) ω p).mpr hp
  · change (a : Site 2) 1 + v 1 = -(m : ℤ)
    change kstBridgeCorner m true false a at ha
    simp [kstBridgeCorner, v] at ha ⊢
    exact ha.2
  · change (b : Site 2) 1 + v 1 = -(m : ℤ)
    change kstBridgeCorner m false false b at hb
    simp [kstBridgeCorner, v] at hb ⊢
    exact hb.2
  · change (a : Site 2) 0 + v 0 ≤ t - ((m / 12 : ℕ) : ℤ)
    change kstBridgeCorner m true false a at ha
    simp [kstBridgeCorner, v] at ha ⊢
    omega
  · change t + ((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 + v 0
    change kstBridgeCorner m false false b at hb
    simp [kstBridgeCorner, v] at hb ⊢
    omega

end Sandpile.External.RSW
