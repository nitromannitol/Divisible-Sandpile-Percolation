import Sandpile.External.RSW.CenteredBridgeDecomposition
import Sandpile.External.RSW.BridgePieceSymmetry

/-!
# Symmetry of centered bridge pieces

Coordinate reflections reduce the square-root bound for a bridge with an arbitrary
offset to two representative bridge pieces.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Coordinate reflection acts on the centered bridge rectangle. -/
def reflectCenteredBridgeRectangle (m d : ℕ) (flipX flipY : Bool) :
    rectangleGraph (centeredPlaneRectangle (m + d) m) →g
      rectangleGraph (centeredPlaneRectangle (m + d) m) where
  toFun z := ⟨reflectPlaneCoordinates flipX flipY z, by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    cases flipX <;> cases flipY <;>
      simp only [reflectPlaneCoordinates, Bool.false_eq_true, ↓reduceIte,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> omega⟩
  map_rel' h := lattice_adj_reflectPlaneCoordinates flipX flipY h

/-- The site underlying a reflected rectangle vertex is the reflected site. -/
theorem reflectCenteredBridgeRectangle_apply (m d : ℕ) (flipX flipY : Bool)
    (z : centeredPlaneRectangle (m + d) m) :
    (reflectCenteredBridgeRectangle m d flipX flipY z : Site 2) =
      reflectPlaneCoordinates flipX flipY z := rfl

/-- Reflection of a walk preserves its open edges when the configuration is reflected too. -/
theorem IsBondOpenWalk.map_reflectCenteredBridgeRectangle {m d : ℕ} {flipX flipY : Bool}
    {ω : Sym2 (Site 2) → Bool}
    {a b : centeredPlaneRectangle (m + d) m}
    {p : (rectangleGraph (centeredPlaneRectangle (m + d) m)).Walk a b}
    (hp : IsBondOpenWalk ω p) :
    IsBondOpenWalk (ω ∘ Sym2.map (reflectPlaneCoordinates flipX flipY))
      (p.map (reflectCenteredBridgeRectangle m d flipX flipY)) := by
  apply (isBondOpenWalk_map (reflectPlaneCoordinates flipX flipY)
    (reflectCenteredBridgeRectangle m d flipX flipY) (fun _ => rfl) _ p).mpr
  have he : (ω ∘ Sym2.map (reflectPlaneCoordinates flipX flipY)) ∘
      Sym2.map (reflectPlaneCoordinates flipX flipY) = ω := by
    funext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Function.comp_apply, Sym2.map_mk]
      rw [reflectPlaneCoordinates_involutive flipX flipY x,
        reflectPlaneCoordinates_involutive flipX flipY y]
  rw [he]
  exact hp


/-- Reflecting in the horizontal axis exchanges the upper and lower right-corner cases. -/
theorem centeredBridgePiece_one_reflect_y (m d : ℕ) :
    centeredBridgePieceEvent m d 1 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ⁻¹' centeredBridgePieceEvent m d 2 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectCenteredBridgeRectangle m d false true a, reflectCenteredBridgeRectangle m d false true b,
    p.map (reflectCenteredBridgeRectangle m d false true), ?_, ?_, hp.map_reflectCenteredBridgeRectangle⟩
  · change centeredBridgeLeft m d a at ha
    change centeredBridgeLeft m d (reflectCenteredBridgeRectangle m d false true a)
    simp [centeredBridgeLeft, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega
  · change centeredBridgeCorner m d false false b at hb
    change centeredBridgeCorner m d false true (reflectCenteredBridgeRectangle m d false true b)
    simp [centeredBridgeCorner, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates] at hb ⊢
    omega


/-- Reflecting in the horizontal axis also sends the upper right-corner case to the lower one. -/
theorem centeredBridgePiece_two_reflect_y (m d : ℕ) :
    centeredBridgePieceEvent m d 2 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ⁻¹' centeredBridgePieceEvent m d 1 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectCenteredBridgeRectangle m d false true a, reflectCenteredBridgeRectangle m d false true b,
    p.map (reflectCenteredBridgeRectangle m d false true), ?_, ?_, hp.map_reflectCenteredBridgeRectangle⟩
  · change centeredBridgeLeft m d a at ha
    change centeredBridgeLeft m d (reflectCenteredBridgeRectangle m d false true a)
    simp [centeredBridgeLeft, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega
  · change centeredBridgeCorner m d false true b at hb
    change centeredBridgeCorner m d false false (reflectCenteredBridgeRectangle m d false true b)
    simp [centeredBridgeCorner, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates] at hb ⊢
    omega

/-- Reflecting in the vertical axis sends the lower left-corner case into the lower
right-corner case. -/
theorem centeredBridgePiece_three_reflect_x (m d : ℕ) :
    centeredBridgePieceEvent m d 3 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates true false)) ⁻¹' centeredBridgePieceEvent m d 1 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectCenteredBridgeRectangle m d true false b, reflectCenteredBridgeRectangle m d true false a,
    p.reverse.map (reflectCenteredBridgeRectangle m d true false), ?_, ?_, hp.reverse.map_reflectCenteredBridgeRectangle⟩
  · change (b : Site 2) 0 = ((m + d : ℕ) : ℤ) at hb
    change centeredBridgeLeft m d (reflectCenteredBridgeRectangle m d true false b)
    simp [centeredBridgeLeft, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates]
    omega
  · change centeredBridgeCorner m d true false a at ha
    change centeredBridgeCorner m d false false (reflectCenteredBridgeRectangle m d true false a)
    simp [centeredBridgeCorner, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega

/-- Reflecting in both axes sends the upper left-corner case into the lower right-corner case. -/
theorem centeredBridgePiece_four_reflect_xy (m d : ℕ) :
    centeredBridgePieceEvent m d 4 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates true true)) ⁻¹' centeredBridgePieceEvent m d 1 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectCenteredBridgeRectangle m d true true b, reflectCenteredBridgeRectangle m d true true a,
    p.reverse.map (reflectCenteredBridgeRectangle m d true true), ?_, ?_, hp.reverse.map_reflectCenteredBridgeRectangle⟩
  · change (b : Site 2) 0 = ((m + d : ℕ) : ℤ) at hb
    change centeredBridgeLeft m d (reflectCenteredBridgeRectangle m d true true b)
    simp [centeredBridgeLeft, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates]
    omega
  · change centeredBridgeCorner m d true true a at ha
    change centeredBridgeCorner m d false false (reflectCenteredBridgeRectangle m d true true a)
    simp [centeredBridgeCorner, reflectCenteredBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega


/-- The square-root bridge lower bound is attained by either the vertical-side crossing
or the lower right-corner event. -/
theorem measureReal_centeredBridgePiece_max_ge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m d : ℕ) :
    1 - (1 - μ.real (centeredBridgeEvent m d)) ^ (1 / (5 : ℝ)) ≤
      max (μ.real (centeredBridgePieceEvent m d 0)) (μ.real (centeredBridgePieceEvent m d 1)) := by
  have h₂ : μ.real (centeredBridgePieceEvent m d 2) ≤ μ.real (centeredBridgePieceEvent m d 1) := by
    have hp := measurePreserving_reflectPlaneCoordinates μ hs hr false true
    exact (measureReal_mono (centeredBridgePiece_two_reflect_y m d) (measure_ne_top μ _)).trans
      (hp.measureReal_preimage (measurableSet_centeredBridgePieceEvent m d 1).nullMeasurableSet).le
  have h₃ : μ.real (centeredBridgePieceEvent m d 3) ≤ μ.real (centeredBridgePieceEvent m d 1) := by
    have hp := measurePreserving_reflectPlaneCoordinates μ hs hr true false
    exact (measureReal_mono (centeredBridgePiece_three_reflect_x m d) (measure_ne_top μ _)).trans
      (hp.measureReal_preimage (measurableSet_centeredBridgePieceEvent m d 1).nullMeasurableSet).le
  have h₄ : μ.real (centeredBridgePieceEvent m d 4) ≤ μ.real (centeredBridgePieceEvent m d 1) := by
    have hp := measurePreserving_reflectPlaneCoordinates μ hs hr true true
    exact (measureReal_mono (centeredBridgePiece_four_reflect_xy m d) (measure_ne_top μ _)).trans
      (hp.measureReal_preimage (measurableSet_centeredBridgePieceEvent m d 1).nullMeasurableSet).le
  obtain ⟨i, hi⟩ := exists_measureReal_centeredBridgePiece_ge μ ha m d
  fin_cases i
  · exact hi.trans (le_max_left _ _)
  · exact hi.trans (le_max_right _ _)
  · exact hi.trans (h₂.trans (le_max_right _ _))
  · exact hi.trans (h₃.trans (le_max_right _ _))
  · exact hi.trans (h₄.trans (le_max_right _ _))

end Sandpile.External.RSW
