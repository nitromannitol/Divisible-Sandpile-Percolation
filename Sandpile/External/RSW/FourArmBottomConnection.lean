import Sandpile.External.RSW.ReflectY
import Sandpile.External.RSW.FourArmTopConnection

/-!
# Connecting the four-arm configuration to the bottom

Horizontal reflection preserves the four-arm event and turns a top-connected KST path
into a bottom-connected one.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Reflecting an arm in the horizontal axis preserves the arm event. -/
theorem kstArmEvent_reflectY (m : ℕ) {ω : Sym2 (Site 2) → Bool}
    (hω : ω ∈ kstArmEvent m) :
    (ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∈ kstArmEvent m := by
  obtain ⟨a, b, p, ha, hb, hp⟩ := hω
  let f := reflectYRectangle (m + m / 64) m
  refine ⟨f b, f a, p.reverse.map f, ?_, ?_, hp.reverse.map_reflectY⟩
  · change -(b : Site 2) 1 = (m : ℤ) ∧
      -((m / 64 : ℕ) : ℤ) ≤ (b : Site 2) 0 ∧ (b : Site 2) 0 ≤ (m / 64 : ℕ)
    exact ⟨by have := hb.1; omega, hb.2.1, hb.2.2⟩
  · change -(a : Site 2) 1 = -(m : ℤ) ∧
      -((m / 64 : ℕ) : ℤ) ≤ (a : Site 2) 0 ∧ (a : Site 2) 0 ≤ (m / 64 : ℕ)
    exact ⟨by have := ha.1; omega, ha.2.1, ha.2.2⟩

/-- Reflection conjugates an arm translation to its vertically reflected translation. -/
theorem translatedKSTArmEvent_reflectY (m : ℕ) (x y : ℤ)
    {ω : Sym2 (Site 2) → Bool} (hω : ω ∈ translatedKSTArmEvent m ![x, y]) :
    (ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∈ translatedKSTArmEvent m ![x, -y] := by
  have he : (ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∘
      Sym2.map (fun z => z + ![x, -y]) =
      (ω ∘ Sym2.map (fun z => z + ![x, y])) ∘
        Sym2.map (reflectPlaneCoordinates false true) := by
    funext e
    induction e using Sym2.ind with
    | _ u v =>
      have hsite (z : Site 2) :
          reflectPlaneCoordinates false true (z + ![x, -y]) =
            reflectPlaneCoordinates false true z + ![x, y] := by
        ext i
        fin_cases i <;> simp [reflectPlaneCoordinates]
        all_goals ring
      simp only [Function.comp_apply, Sym2.map_mk, hsite]
  change ((ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∘
    Sym2.map (fun z => z + ![x, -y])) ∈ kstArmEvent m
  rw [he]
  exact kstArmEvent_reflectY m hω

/-- Horizontal reflection preserves the four-arm event. -/
theorem kstFourArmEvent_reflectY (m : ℕ) {ω : Sym2 (Site 2) → Bool}
    (hω : ω ∈ kstFourArmEvent m) :
    (ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∈ kstFourArmEvent m := by
  let α : ℤ := (m / 64 : ℕ)
  let t : ℤ := (3 * m / 2 : ℕ)
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hω
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [neg_zero] using translatedKSTArmEvent_reflectY m (4 * α) 0 h₁
  · simpa only [neg_zero] using translatedKSTArmEvent_reflectY m (-(4 * α)) 0 h₂
  · simpa only [neg_neg] using translatedKSTArmEvent_reflectY (5 * m / 2) 0 (-t) h₄
  · exact translatedKSTArmEvent_reflectY (5 * m / 2) 0 t h₃

/-- An open KST path joined to the bottom side of its ambient rectangle. -/
def kstBottomConnectedEvent (W n m : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle W n
  {ω | ∃ (a b x d : Q) (p : (rectangleGraph Q).Walk a b)
      (q : (rectangleGraph Q).Walk x d),
    IsKSTPath m p ∧ x ∈ p.support ∧ (d : Site 2) 1 = -(n : ℤ) ∧
    IsBondOpenWalk ω p ∧ IsBondOpenWalk ω q}

/-- A top-connected path in the reflected configuration yields a bottom-connected path. -/
theorem kstBottomConnectedEvent_of_reflected_top (W n m : ℕ)
    {ω : Sym2 (Site 2) → Bool}
    (hω : (ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ∈ kstTopConnectedEvent W n m) :
    ω ∈ kstBottomConnectedEvent W n m := by
  let f := reflectYRectangle W n
  obtain ⟨a, b, x, d, p, q, hp, hx, hd, hop, hoq⟩ := hω
  refine ⟨f b, f a, f x, f d, p.reverse.map f, q.map f, hp.reverse_map_reflectY, ?_, ?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_map]
    refine List.mem_map.mpr ⟨x, ?_, rfl⟩
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse]
  · change -(d : Site 2) 1 = -(n : ℤ)
    omega
  · apply (isBondOpenWalk_map (reflectPlaneCoordinates false true) f (fun _ => rfl) ω p.reverse).mpr
    exact hop.reverse
  · exact (isBondOpenWalk_map (reflectPlaneCoordinates false true) f (fun _ => rfl) ω q).mpr hoq

/-- The four-arm event yields a KST path connected to the bottom of the vertical rectangle. -/
theorem kstFourArmEvent_subset_bottomConnected (j : ℕ) :
    kstFourArmEvent (kstBaseScale j) ⊆
      kstBottomConnectedEvent (3 * kstBaseScale j - 3 * (kstBaseScale j / 12))
        (4 * kstBaseScale j) (kstBaseScale j) := by
  intro ω hω
  apply kstBottomConnectedEvent_of_reflected_top
  exact kstFourArmEvent_subset_topConnected j (kstFourArmEvent_reflectY _ hω)

end Sandpile.External.RSW
