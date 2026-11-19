import Sandpile.External.RSW.DualRotatedCrossing
import Sandpile.External.RSW.DualSwap

/-!
# Gluing bond crossings

Horizontal crossings of two overlapping rectangles and a vertical crossing of their common
square combine to give a crossing of their union.
-/

open LatticeProb Set Percolation.Literature

namespace Sandpile.External.RSW

/-- A lattice automorphism carries an ordinary crossing to a crossing of its image. -/
theorem bondCrossingEvent_reindex_iff (φ : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2)
    (w h : ℕ) (ω : Sym2 (Site 2) → Bool) :
    (ω ∘ Sym2.map φ) ∈ bondCrossingEvent w h ↔
      openPlaneBonds ω ∈ openCrossing (φ '' (↑(rectangle w h) : Set (Site 2)))
        (φ '' (↑(leftSide w h) : Set (Site 2)))
        (φ '' (↑(rightSide w h) : Set (Site 2))) := by
  rw [mem_bondCrossingEvent_iff_lrCrossing]
  have he := Set.ext_iff.mp (preimage_relabel_openCrossing φ.toEquiv
    (↑(rectangle w h)) (↑(leftSide w h)) (↑(rightSide w h)))
    (openPlaneBonds (ω ∘ Sym2.map φ))
  change BondConfig.relabel (sym2Equiv φ.toEquiv) (openPlaneBonds (ω ∘ Sym2.map φ)) ∈
    openCrossing (φ '' (↑(rectangle w h) : Set (Site 2)))
      (φ '' (↑(leftSide w h) : Set (Site 2)))
      (φ '' (↑(rightSide w h) : Set (Site 2))) ↔ _ at he
  rw [relabel_openPlaneBonds] at he
  exact he.symm

/-- Opening additional bonds preserves an open walk. -/
theorem IsBondOpenWalk.mono {Q : Finset (Site 2)} {ω η : Sym2 (Site 2) → Bool}
    (hωη : ω ≤ η) {a b : Q} (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk ω p) : IsBondOpenWalk η p := by
  induction p with
  | nil => trivial
  | @cons a b c hab p ih =>
    refine ⟨?_, ih hp.2⟩
    have he := hωη s((a : Site 2), (b : Site 2))
    rw [hp.1] at he
    exact le_antisymm le_top he

/-- A horizontal crossing remains open when bonds are opened. -/
theorem isUpperSet_bondCrossingEvent (w h : ℕ) : IsUpperSet (bondCrossingEvent w h) := by
  intro ω η hωη
  rintro ⟨a, b, p, ha, hb, hp⟩
  exact ⟨a, b, p, ha, hb, hp.mono hωη p⟩

/-- The isomorphism carrying a horizontal square crossing to the vertical crossing in the
square shared by two horizontally overlapping rectangles. -/
def glueVerticalIso (m n : ℕ) : LatticeModels.zdGraph 2 ≃g LatticeModels.zdGraph 2 :=
  transposeIso.trans (zdShiftIso (glueShift m n))

/-- The overlap crossing uses coordinate interchange followed by translation. -/
theorem glueVerticalIso_apply (m n : ℕ) (z : Site 2) :
    glueVerticalIso m n z = swapPlaneSite z + glueShift m n := by
  ext i
  fin_cases i <;> simp [glueVerticalIso, swapPlaneSite]

/-- The image of the square under the overlap isomorphism. -/
theorem glueVerticalIso_image_rectangle (m n : ℕ) :
    glueVerticalIso m n '' (↑(rectangle n n) : Set (Site 2)) =
      (· + glueShift m n) '' ↑(rectangle n n) := by
  change ((fun z : Site 2 => z + glueShift m n) ∘ (transposeIso : Site 2 → Site 2)) '' _ = _
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (Set.image (fun z : Site 2 => z + glueShift m n))
      ((image_transposeIso _).trans (preimage_transpose_rectangle n n))

/-- The left side of the square maps to the bottom side of the overlap. -/
theorem glueVerticalIso_image_leftSide (m n : ℕ) :
    glueVerticalIso m n '' (↑(leftSide n n) : Set (Site 2)) =
      (· + glueShift m n) '' ↑(bottomSide n n) := by
  change ((fun z : Site 2 => z + glueShift m n) ∘ (transposeIso : Site 2 → Site 2)) '' _ = _
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (Set.image (fun z : Site 2 => z + glueShift m n))
      ((image_transposeIso _).trans (preimage_transpose_leftSide n n))

/-- The right side of the square maps to the top side of the overlap. -/
theorem glueVerticalIso_image_rightSide (m n : ℕ) :
    glueVerticalIso m n '' (↑(rightSide n n) : Set (Site 2)) =
      (· + glueShift m n) '' ↑(topSide n n) := by
  change ((fun z : Site 2 => z + glueShift m n) ∘ (transposeIso : Site 2 → Site 2)) '' _ = _
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (Set.image (fun z : Site 2 => z + glueShift m n))
      ((image_transposeIso _).trans (preimage_transpose_rightSide n n))

/-- Two horizontal crossings and the vertical crossing of the common square give a
horizontal crossing of the union. -/
theorem bondCrossingEvent_of_glue {m₁ m₂ n : ℕ} (hn₁ : n ≤ m₁) (hn₂ : n ≤ m₂)
    {ω : Sym2 (Site 2) → Bool} (h₁ : ω ∈ bondCrossingEvent m₁ n)
    (hV : (ω ∘ Sym2.map (glueVerticalIso m₁ n)) ∈ bondCrossingEvent n n)
    (h₂ : (ω ∘ Sym2.map (zdShiftIso (glueShift m₁ n))) ∈ bondCrossingEvent m₂ n) :
    ω ∈ bondCrossingEvent (m₁ + m₂ - n) n := by
  apply (mem_bondCrossingEvent_iff_lrCrossing _ _ _).mpr
  apply lrCrossing_of_glue hn₁ hn₂ (openPlaneBonds_subset ω)
    ((mem_bondCrossingEvent_iff_lrCrossing _ _ _).mp h₁)
  · have hv := (bondCrossingEvent_reindex_iff (glueVerticalIso m₁ n) n n ω).mp hV
    rw [glueVerticalIso_image_rectangle, glueVerticalIso_image_leftSide,
      glueVerticalIso_image_rightSide] at hv
    exact hv
  · have hh := (bondCrossingEvent_reindex_iff (zdShiftIso (glueShift m₁ n)) m₂ n ω).mp h₂
    exact hh

end Sandpile.External.RSW
