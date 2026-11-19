import Sandpile.External.RSW.ArmToPath

/-!
# Translated arms inside a KST path rectangle

An arm shifted horizontally remains a KST path when its shifted central target stays
inside the wider KST target.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A translated arm yields a KST path when the shifted arm target fits in the KST target. -/
theorem translated_kstArmEvent_subset_kstPathEvent (m : ℕ) (t : ℤ)
    (hleft : -((m / 12 : ℕ) : ℤ) ≤ t - ((m / 64 : ℕ) : ℤ))
    (hright : t + ((m / 64 : ℕ) : ℤ) ≤ (m / 12 : ℕ)) :
    (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + ![t, 0])) ⁻¹'
      kstArmEvent m ⊆ kstPathEvent m := by
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
  intro ω hω
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  refine ⟨f a, f b, p.bypass.map f, ?_, ?_⟩
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

/-- The two shifts used in the arm construction both yield KST paths when the target
separation condition holds. -/
theorem kstArm_shift_four_alpha (m : ℕ) (hsep : 5 * (m / 64) ≤ m / 12) :
    ((fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map
      (fun z => z + ![((4 * (m / 64) : ℕ) : ℤ), 0])) ⁻¹' kstArmEvent m ⊆ kstPathEvent m) ∧
    ((fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map
      (fun z => z + ![-((4 * (m / 64) : ℕ) : ℤ), 0])) ⁻¹' kstArmEvent m ⊆ kstPathEvent m) := by
  have hsep' : (5 : ℤ) * ((m / 64 : ℕ) : ℤ) ≤ (m / 12 : ℕ) := by exact_mod_cast hsep
  constructor
  · apply translated_kstArmEvent_subset_kstPathEvent m
    · push_cast
      omega
    · push_cast
      omega
  · apply translated_kstArmEvent_subset_kstPathEvent m
    · push_cast
      omega
    · push_cast
      omega

/-- The rounded arm target is narrow enough for both translated arms at every scale. -/
theorem five_arm_offsets_le_bridge_offset (m : ℕ) : 5 * (m / 64) ≤ m / 12 := by
  omega

end Sandpile.External.RSW
