import Sandpile.External.RSW.BridgeDecomposition
import Sandpile.External.RSW.EdgeSymmetry
import Sandpile.External.RSW.BondWalk

/-!
# Symmetry of bridge pieces

Reflections identify the two right-corner cases and bound each left-corner case by a
right-corner case.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Independent reflections of the coordinates of a lattice site. -/
def reflectPlaneCoordinates (flipX flipY : Bool) (z : Site 2) : Site 2 :=
  ![if flipX then -z 0 else z 0, if flipY then -z 1 else z 1]

/-- Independent coordinate reflections are involutions. -/
theorem reflectPlaneCoordinates_involutive (flipX flipY : Bool) :
    Function.Involutive (reflectPlaneCoordinates flipX flipY) := by
  intro z
  ext i
  fin_cases i <;> cases flipX <;> cases flipY <;> simp [reflectPlaneCoordinates]

/-- Independent coordinate reflections preserve lattice adjacency. -/
theorem lattice_adj_reflectPlaneCoordinates (flipX flipY : Bool) {x y : Site 2}
    (h : (lattice 2).Adj x y) :
    (lattice 2).Adj (reflectPlaneCoordinates flipX flipY x) (reflectPlaneCoordinates flipX flipY y) := by
  cases flipX <;> cases flipY
  · convert h using 1 <;> ext i <;> fin_cases i <;> simp [reflectPlaneCoordinates]
  · exact lattice_adj_swap_plane (lattice_adj_reflect_plane (lattice_adj_swap_plane h))
  · exact lattice_adj_reflect_plane h
  · exact lattice_adj_reflect_plane
      (lattice_adj_swap_plane (lattice_adj_reflect_plane (lattice_adj_swap_plane h)))

/-- Coordinate reflection acts on the centered bridge rectangle. -/
def reflectBridgeRectangle (m : ℕ) (flipX flipY : Bool) :
    rectangleGraph (centeredPlaneRectangle (m + m / 12) m) →g
      rectangleGraph (centeredPlaneRectangle (m + m / 12) m) where
  toFun z := ⟨reflectPlaneCoordinates flipX flipY z, by
    have hz := (mem_centeredPlaneRectangle _ _ z).mp z.property
    apply (mem_centeredPlaneRectangle _ _ _).mpr
    cases flipX <;> cases flipY <;>
      simp only [reflectPlaneCoordinates, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> omega⟩
  map_rel' h := lattice_adj_reflectPlaneCoordinates flipX flipY h

/-- The site underlying a reflected rectangle vertex is the reflected site. -/
theorem reflectBridgeRectangle_apply (m : ℕ) (flipX flipY : Bool)
    (z : centeredPlaneRectangle (m + m / 12) m) :
    (reflectBridgeRectangle m flipX flipY z : Site 2) =
      reflectPlaneCoordinates flipX flipY z := rfl

/-- Reflection of a walk preserves its open edges when the configuration is reflected too. -/
theorem IsBondOpenWalk.map_reflectBridgeRectangle {m : ℕ} {flipX flipY : Bool}
    {ω : Sym2 (Site 2) → Bool}
    {a b : centeredPlaneRectangle (m + m / 12) m}
    {p : (rectangleGraph (centeredPlaneRectangle (m + m / 12) m)).Walk a b}
    (hp : IsBondOpenWalk ω p) :
    IsBondOpenWalk (ω ∘ Sym2.map (reflectPlaneCoordinates flipX flipY))
      (p.map (reflectBridgeRectangle m flipX flipY)) := by
  apply (isBondOpenWalk_map (reflectPlaneCoordinates flipX flipY)
    (reflectBridgeRectangle m flipX flipY) (fun _ => rfl) _ p).mpr
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
theorem kstBridgePiece_one_reflect_y (m : ℕ) :
    kstBridgePieceEvent m 1 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ⁻¹' kstBridgePieceEvent m 2 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectBridgeRectangle m false true a, reflectBridgeRectangle m false true b,
    p.map (reflectBridgeRectangle m false true), ?_, ?_, hp.map_reflectBridgeRectangle⟩
  · change kstBridgeLeft m a at ha
    change kstBridgeLeft m (reflectBridgeRectangle m false true a)
    simp [kstBridgeLeft, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega
  · change kstBridgeCorner m false false b at hb
    change kstBridgeCorner m false true (reflectBridgeRectangle m false true b)
    simp [kstBridgeCorner, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at hb ⊢
    omega


/-- Reflecting in the horizontal axis also sends the upper right-corner case to the lower one. -/
theorem kstBridgePiece_two_reflect_y (m : ℕ) :
    kstBridgePieceEvent m 2 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates false true)) ⁻¹' kstBridgePieceEvent m 1 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectBridgeRectangle m false true a, reflectBridgeRectangle m false true b,
    p.map (reflectBridgeRectangle m false true), ?_, ?_, hp.map_reflectBridgeRectangle⟩
  · change kstBridgeLeft m a at ha
    change kstBridgeLeft m (reflectBridgeRectangle m false true a)
    simp [kstBridgeLeft, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega
  · change kstBridgeCorner m false true b at hb
    change kstBridgeCorner m false false (reflectBridgeRectangle m false true b)
    simp [kstBridgeCorner, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at hb ⊢
    omega

/-- Reflecting in the vertical axis sends the lower left-corner case into the lower
right-corner case. -/
theorem kstBridgePiece_three_reflect_x (m : ℕ) :
    kstBridgePieceEvent m 3 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates true false)) ⁻¹' kstBridgePieceEvent m 1 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectBridgeRectangle m true false b, reflectBridgeRectangle m true false a,
    p.reverse.map (reflectBridgeRectangle m true false), ?_, ?_, hp.reverse.map_reflectBridgeRectangle⟩
  · change (b : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) at hb
    change kstBridgeLeft m (reflectBridgeRectangle m true false b)
    simp [kstBridgeLeft, reflectBridgeRectangle_apply, reflectPlaneCoordinates]
    omega
  · change kstBridgeCorner m true false a at ha
    change kstBridgeCorner m false false (reflectBridgeRectangle m true false a)
    simp [kstBridgeCorner, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega

/-- Reflecting in both axes sends the upper left-corner case into the lower right-corner case. -/
theorem kstBridgePiece_four_reflect_xy (m : ℕ) :
    kstBridgePieceEvent m 4 ⊆
      (fun ω : Sym2 (Site 2) → Bool =>
        ω ∘ Sym2.map (reflectPlaneCoordinates true true)) ⁻¹' kstBridgePieceEvent m 1 := by
  intro ω h
  obtain ⟨a, b, p, ha, hb, hp⟩ := h
  refine ⟨reflectBridgeRectangle m true true b, reflectBridgeRectangle m true true a,
    p.reverse.map (reflectBridgeRectangle m true true), ?_, ?_, hp.reverse.map_reflectBridgeRectangle⟩
  · change (b : Site 2) 0 = ((m + m / 12 : ℕ) : ℤ) at hb
    change kstBridgeLeft m (reflectBridgeRectangle m true true b)
    simp [kstBridgeLeft, reflectBridgeRectangle_apply, reflectPlaneCoordinates]
    omega
  · change kstBridgeCorner m true true a at ha
    change kstBridgeCorner m false false (reflectBridgeRectangle m true true a)
    simp [kstBridgeCorner, reflectBridgeRectangle_apply, reflectPlaneCoordinates] at ha ⊢
    omega


/-- A law invariant under coordinate interchange and vertical reflection is invariant under
independent coordinate reflections. -/
theorem measurePreserving_reflectPlaneCoordinates
    (μ : Measure (Sym2 (Site 2) → Bool))
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ)
    (flipX flipY : Bool) :
    MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (reflectPlaneCoordinates flipX flipY)) μ μ := by
  have hy : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (reflectPlaneCoordinates false true)) μ μ := by
    convert hs.comp (hr.comp hs) using 1
    funext ω e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Function.comp_apply, Sym2.map_mk]
      congr 1 <;> ext i <;> fin_cases i <;>
        simp [reflectPlaneCoordinates, swapPlaneSite, reflectPlaneSite]
  cases flipX <;> cases flipY
  · convert MeasurePreserving.id μ using 1
    funext ω e
    induction e using Sym2.ind with
    | _ x y =>
      have hx : reflectPlaneCoordinates false false x = x := by
        ext i
        fin_cases i <;> simp [reflectPlaneCoordinates]
      have hy' : reflectPlaneCoordinates false false y = y := by
        ext i
        fin_cases i <;> simp [reflectPlaneCoordinates]
      simp only [Function.comp_apply, Sym2.map_mk, id_eq, hx, hy']
  · exact hy
  · convert hr using 1
    rfl
  · convert hr.comp hy using 1
    funext ω e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Function.comp_apply, Sym2.map_mk]
      congr 1 <;> ext i <;> fin_cases i <;>
        simp [reflectPlaneCoordinates, reflectPlaneSite]

/-- The square-root bridge lower bound is attained by either the vertical-side crossing
or the lower right-corner event. -/
theorem measureReal_kstBridgePiece_max_ge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ)
    (hr : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map reflectPlaneSite) μ μ) (m : ℕ) :
    1 - (1 - μ.real (kstBridgeEvent m)) ^ (1 / (5 : ℝ)) ≤
      max (μ.real (kstBridgePieceEvent m 0)) (μ.real (kstBridgePieceEvent m 1)) := by
  have h₂ : μ.real (kstBridgePieceEvent m 2) ≤ μ.real (kstBridgePieceEvent m 1) := by
    have hp := measurePreserving_reflectPlaneCoordinates μ hs hr false true
    exact (measureReal_mono (kstBridgePiece_two_reflect_y m) (measure_ne_top μ _)).trans
      (hp.measureReal_preimage (measurableSet_kstBridgePieceEvent m 1).nullMeasurableSet).le
  have h₃ : μ.real (kstBridgePieceEvent m 3) ≤ μ.real (kstBridgePieceEvent m 1) := by
    have hp := measurePreserving_reflectPlaneCoordinates μ hs hr true false
    exact (measureReal_mono (kstBridgePiece_three_reflect_x m) (measure_ne_top μ _)).trans
      (hp.measureReal_preimage (measurableSet_kstBridgePieceEvent m 1).nullMeasurableSet).le
  have h₄ : μ.real (kstBridgePieceEvent m 4) ≤ μ.real (kstBridgePieceEvent m 1) := by
    have hp := measurePreserving_reflectPlaneCoordinates μ hs hr true true
    exact (measureReal_mono (kstBridgePiece_four_reflect_xy m) (measure_ne_top μ _)).trans
      (hp.measureReal_preimage (measurableSet_kstBridgePieceEvent m 1).nullMeasurableSet).le
  obtain ⟨i, hi⟩ := exists_measureReal_kstBridgePiece_ge μ ha m
  fin_cases i
  · exact hi.trans (le_max_left _ _)
  · exact hi.trans (le_max_right _ _)
  · exact hi.trans (h₂.trans (le_max_right _ _))
  · exact hi.trans (h₃.trans (le_max_right _ _))
  · exact hi.trans (h₄.trans (le_max_right _ _))

end Sandpile.External.RSW
