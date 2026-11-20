import Sandpile.External.RSW.TranslatedArm

/-!
# Targets of translated arms

A translated arm yields a KST path with endpoints in the translated central intervals.
The endpoint information distinguishes the two arms used in the quasi-crossing construction.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A translated arm yields a KST path while retaining both translated endpoint bounds. -/
theorem translated_kstArmEvent_exists_path_with_targets (m : ℕ) (t : ℤ)
    (hleft : -((m / 12 : ℕ) : ℤ) ≤ t - ((m / 64 : ℕ) : ℤ))
    (hright : t + ((m / 64 : ℕ) : ℤ) ≤ (m / 12 : ℕ))
    {ω : Sym2 (Site 2) → Bool}
    (hω : (ω ∘ Sym2.map (fun z => z + ![t, 0])) ∈ kstArmEvent m) :
    ∃ (a b : centeredPlaneRectangle (m + m / 12) m)
      (p : (rectangleGraph (centeredPlaneRectangle (m + m / 12) m)).Walk a b),
      IsKSTPath m p ∧ IsBondOpenWalk ω p ∧
      t - ((m / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0 ∧
      (a : Site 2) 0 ≤ t + ((m / 64 : ℕ) : ℤ) ∧
      t - ((m / 64 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧
      (b : Site 2) 0 ≤ t + ((m / 64 : ℕ) : ℤ) := by
  let Q := centeredPlaneRectangle (m + m / 64) m
  let R := centeredPlaneRectangle (m + m / 12) m
  let v : Site 2 := ![t, 0]
  have hQR (z : Q) : (z : Site 2) + v ∈ R := by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    simp only [Pi.add_apply, v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
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
  refine ⟨f a, f b, p.bypass.map f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨p.bypass_isPath.map hfinj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (a : Site 2) 1 + v 1 = m
      simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
      exact ha.1
    · change (b : Site 2) 1 + v 1 = -(m : ℤ)
      simp only [v, Matrix.cons_val_one, Matrix.cons_val_fin_one, add_zero]
      exact hb.1
    · change -((m / 12 : ℕ) : ℤ) ≤ (a : Site 2) 0 + v 0
      simp only [v, Matrix.cons_val_zero]
      have := ha.2.1
      omega
    · change (a : Site 2) 0 + v 0 ≤ ((m / 12 : ℕ) : ℤ)
      simp only [v, Matrix.cons_val_zero]
      have := ha.2.2
      omega
    · change -((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0 + v 0
      simp only [v, Matrix.cons_val_zero]
      have := hb.2.1
      omega
    · change (b : Site 2) 0 + v 0 ≤ ((m / 12 : ℕ) : ℤ)
      simp only [v, Matrix.cons_val_zero]
      have := hb.2.2
      omega
    · intro z hz
      exact z.property
  · exact (isBondOpenWalk_map (fun z => z + v) f (fun _ => rfl) ω p.bypass).mpr hp.bypass
  · change t - ((m / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0 + v 0
    simp only [v, Matrix.cons_val_zero]
    have := ha.2.1
    omega
  · change (a : Site 2) 0 + v 0 ≤ t + ((m / 64 : ℕ) : ℤ)
    simp only [v, Matrix.cons_val_zero]
    have := ha.2.2
    omega
  · change t - ((m / 64 : ℕ) : ℤ) ≤ (b : Site 2) 0 + v 0
    simp only [v, Matrix.cons_val_zero]
    have := hb.2.1
    omega
  · change (b : Site 2) 0 + v 0 ≤ t + ((m / 64 : ℕ) : ℤ)
    simp only [v, Matrix.cons_val_zero]
    have := hb.2.2
    omega

end Sandpile.External.RSW
