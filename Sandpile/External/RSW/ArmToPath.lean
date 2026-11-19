import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.BondWalk

/-!
# Arm paths

Every arm contains a simple vertical path whose endpoints and support satisfy the
scale-`m` path conditions used in quasi-crossings.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The existence of an open KST path in its centered scale rectangle. -/
def kstPathEvent (m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle (m + m / 12) m
  {ω | ∃ (a b : Q) (p : (rectangleGraph Q).Walk a b),
    IsKSTPath m p ∧ IsBondOpenWalk ω p}

/-- Every arm contains an open KST path at the same scale. -/
theorem kstArmEvent_subset_kstPathEvent (m : ℕ) : kstArmEvent m ⊆ kstPathEvent m := by
  let Q := centeredPlaneRectangle (m + m / 64) m
  let R := centeredPlaneRectangle (m + m / 12) m
  have hdiv : m / 64 ≤ m / 12 := Nat.div_le_div_left (by decide : 12 ≤ 64) (by decide : 0 < 12)
  have hQR : Q ⊆ R := by
    intro z hz
    have hz' := (mem_centeredPlaneRectangle _ _ z).mp hz
    apply (mem_centeredPlaneRectangle _ _ z).mpr
    have : ((m / 64 : ℕ) : ℤ) ≤ (m / 12 : ℕ) := by exact_mod_cast hdiv
    push_cast at *
    omega
  let f : rectangleGraph Q →g rectangleGraph R :=
    ⟨fun z => ⟨z.val, hQR z.property⟩, fun h => h⟩
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hh := congrArg (fun z : R => (z : Site 2)) hab
    exact hh
  intro ω hω
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  refine ⟨f a, f b, p.bypass.map f, ?_, ?_⟩
  · have hβ : ((m / 64 : ℕ) : ℤ) ≤ (m / 12 : ℕ) := by exact_mod_cast hdiv
    refine ⟨p.bypass_isPath.map hfinj, ha.1, hb.1, ?_, ?_, ?_, ?_, ?_⟩
    · have := ha.2.1
      change -((m / 12 : ℕ) : ℤ) ≤ (a : Site 2) 0
      omega
    · have := ha.2.2
      change (a : Site 2) 0 ≤ ((m / 12 : ℕ) : ℤ)
      omega
    · have := hb.2.1
      change -((m / 12 : ℕ) : ℤ) ≤ (b : Site 2) 0
      omega
    · have := hb.2.2
      change (b : Site 2) 0 ≤ ((m / 12 : ℕ) : ℤ)
      omega
    · intro z hz
      exact z.property
  · have hopen := (isBondOpenWalk_map id f (fun _ => rfl) ω p.bypass).mpr ?_
    · exact hopen
    · simpa only [Sym2.map_id, Function.comp_id] using hp.bypass

/-- The event that an open KST path exists is increasing. -/
theorem isUpperSet_kstPathEvent (m : ℕ) : IsUpperSet (kstPathEvent m) := by
  intro ω η hωη
  rintro ⟨a, b, p, hp, hopen⟩
  exact ⟨a, b, p, hp, hopen.mono hωη p⟩

/-- The event that an open KST path exists is measurable. -/
theorem measurableSet_kstPathEvent (m : ℕ) : MeasurableSet (kstPathEvent m) := by
  let Q := centeredPlaneRectangle (m + m / 12) m
  let (a b : Q) : Countable ((rectangleGraph Q).Walk a b) :=
    SimpleGraph.Walk.support_injective.countable
  have hm (a b : Q) (p : (rectangleGraph Q).Walk a b) :
      MeasurableSet {ω : Sym2 (Site 2) → Bool | IsKSTPath m p ∧ IsBondOpenWalk ω p} :=
    (MeasurableSet.const _).inter (measurableSet_isBondOpenWalk p)
  change MeasurableSet {ω : Sym2 (Site 2) → Bool | ∃ (a b : Q)
    (p : (rectangleGraph Q).Walk a b), IsKSTPath m p ∧ IsBondOpenWalk ω p}
  simpa only [ofPred_exists] using
    (MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
      MeasurableSet.iUnion fun p => hm a b p)

end Sandpile.External.RSW
