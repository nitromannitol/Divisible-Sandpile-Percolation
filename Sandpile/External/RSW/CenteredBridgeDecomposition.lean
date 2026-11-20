import Sandpile.External.RSW.ArmBridge
import Sandpile.External.RSW.EdgePathProbability
import Sandpile.External.RSW.DualLaw
import LatticeProb.Bonanno.LQGMetric.Gaussian.AssociationSqrt

/-!
# Decomposition of a bridge with an arbitrary offset

A bridge either crosses between the two vertical sides or reaches one of the four
outer horizontal boundary segments. The square-root trick bounds one piece in terms of
the bridge probability.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile.External.RSW

/-- The left target of a centered bridge rectangle with offset `d`. -/
def centeredBridgeLeft (m d : ℕ) (z : centeredPlaneRectangle (m + d) m) : Prop :=
  (z : Site 2) 0 = -((m + d : ℕ) : ℤ) ∨
    ((z : Site 2) 0 ≤ -(d : ℤ) ∧
      ((z : Site 2) 1 = -(m : ℤ) ∨ (z : Site 2) 1 = m))

/-- The right target of a centered bridge rectangle with offset `d`. -/
def centeredBridgeRight (m d : ℕ) (z : centeredPlaneRectangle (m + d) m) : Prop :=
  (z : Site 2) 0 = ((m + d : ℕ) : ℤ) ∨
    ((d : ℤ) ≤ (z : Site 2) 0 ∧
      ((z : Site 2) 1 = -(m : ℤ) ∨ (z : Site 2) 1 = m))

/-- An open connection between the left and right bridge targets. -/
def centeredBridgeEvent (m d : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  bondConnectionEvent (centeredPlaneRectangle (m + d) m)
    {z | centeredBridgeLeft m d z} {z | centeredBridgeRight m d z}

/-- The centered bridge event is increasing. -/
theorem isUpperSet_centeredBridgeEvent (m d : ℕ) :
    IsUpperSet (centeredBridgeEvent m d) :=
  isUpperSet_bondConnectionEvent _ _ _

/-- The centered bridge event is measurable. -/
theorem measurableSet_centeredBridgeEvent (m d : ℕ) :
    MeasurableSet (centeredBridgeEvent m d) :=
  measurableSet_bondConnectionEvent _ _ _

/-- The original KST bridge is a centered bridge with offset `m / 12`. -/
theorem centeredBridgeEvent_kst (m : ℕ) :
    centeredBridgeEvent m (m / 12) = kstBridgeEvent m := rfl

/-- A horizontal boundary segment of the bridge rectangle on the specified side. -/
def centeredBridgeCorner (m d : ℕ) (left top : Bool)
    (z : centeredPlaneRectangle (m + d) m) : Prop :=
  (if left then (z : Site 2) 0 ≤ -((d : ℕ) : ℤ)
    else ((d : ℕ) : ℤ) ≤ (z : Site 2) 0) ∧
  (z : Site 2) 1 = (if top then (m : ℤ) else -(m : ℤ))

/-- The five possible kinds of bridge, with the crossing followed by the four corner cases. -/
def centeredBridgePieceEvent (m d : ℕ) (i : Fin 5) : Set (Sym2 (Site 2) → Bool) :=
  let Q := centeredPlaneRectangle (m + d) m
  (![bondConnectionEvent Q {z | (z : Site 2) 0 = -((m + d : ℕ) : ℤ)}
        {z | (z : Site 2) 0 = ((m + d : ℕ) : ℤ)},
      bondConnectionEvent Q {z | centeredBridgeLeft m d z} {z | centeredBridgeCorner m d false false z},
      bondConnectionEvent Q {z | centeredBridgeLeft m d z} {z | centeredBridgeCorner m d false true z},
      bondConnectionEvent Q {z | centeredBridgeCorner m d true false z}
        {z | (z : Site 2) 0 = ((m + d : ℕ) : ℤ)},
      bondConnectionEvent Q {z | centeredBridgeCorner m d true true z}
        {z | (z : Site 2) 0 = ((m + d : ℕ) : ℤ)}] : Fin 5 → _) i

/-- Each bridge piece is increasing. -/
theorem isUpperSet_centeredBridgePieceEvent (m d : ℕ) (i : Fin 5) :
    IsUpperSet (centeredBridgePieceEvent m d i) := by
  fin_cases i <;> exact isUpperSet_bondConnectionEvent _ _ _

/-- Each bridge piece is measurable. -/
theorem measurableSet_centeredBridgePieceEvent (m d : ℕ) (i : Fin 5) :
    MeasurableSet (centeredBridgePieceEvent m d i) := by
  fin_cases i <;> exact measurableSet_bondConnectionEvent _ _ _

/-- A bridge is the union of its horizontal-crossing and corner cases. -/
theorem centeredBridgeEvent_eq_iUnion_pieces (m d : ℕ) :
    centeredBridgeEvent m d = ⋃ i, centeredBridgePieceEvent m d i := by
  ext ω
  constructor
  · rintro ⟨a, b, p, ha, hb, hp⟩
    rcases ha with ha | ⟨ha, haY | haY⟩
    · rcases hb with hb | ⟨hb, hbY | hbY⟩
      · exact mem_iUnion.mpr ⟨0, ⟨a, b, p, ha, hb, hp⟩⟩
      · exact mem_iUnion.mpr ⟨1, ⟨a, b, p, Or.inl ha, ⟨hb, hbY⟩, hp⟩⟩
      · exact mem_iUnion.mpr ⟨2, ⟨a, b, p, Or.inl ha, ⟨hb, hbY⟩, hp⟩⟩
    · rcases hb with hb | ⟨hb, hbY | hbY⟩
      · exact mem_iUnion.mpr ⟨3, ⟨a, b, p, ⟨ha, haY⟩, hb, hp⟩⟩
      · exact mem_iUnion.mpr ⟨1, ⟨a, b, p, Or.inr ⟨ha, Or.inl haY⟩, ⟨hb, hbY⟩, hp⟩⟩
      · exact mem_iUnion.mpr ⟨2, ⟨a, b, p, Or.inr ⟨ha, Or.inl haY⟩, ⟨hb, hbY⟩, hp⟩⟩
    · rcases hb with hb | ⟨hb, hbY | hbY⟩
      · exact mem_iUnion.mpr ⟨4, ⟨a, b, p, ⟨ha, haY⟩, hb, hp⟩⟩
      · exact mem_iUnion.mpr ⟨1, ⟨a, b, p, Or.inr ⟨ha, Or.inr haY⟩, ⟨hb, hbY⟩, hp⟩⟩
      · exact mem_iUnion.mpr ⟨2, ⟨a, b, p, Or.inr ⟨ha, Or.inr haY⟩, ⟨hb, hbY⟩, hp⟩⟩
  · intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    fin_cases i <;> rcases hi with ⟨a, b, p, ha, hb, hp⟩
    · exact ⟨a, b, p, Or.inl ha, Or.inl hb, hp⟩
    · exact ⟨a, b, p, ha, Or.inr ⟨hb.1, Or.inl hb.2⟩, hp⟩
    · exact ⟨a, b, p, ha, Or.inr ⟨hb.1, Or.inr hb.2⟩, hp⟩
    · exact ⟨a, b, p, Or.inr ⟨ha.1, Or.inl ha.2⟩, Or.inl hb, hp⟩
    · exact ⟨a, b, p, Or.inr ⟨ha.1, Or.inr ha.2⟩, Or.inl hb, hp⟩

/-- Among the five bridge pieces, one has the square-root lower bound. -/
theorem exists_measureReal_centeredBridgePiece_ge (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (m d : ℕ) :
    ∃ i, 1 - (1 - μ.real (centeredBridgeEvent m d)) ^ (1 / (5 : ℝ)) ≤
      μ.real (centeredBridgePieceEvent m d i) := by
  let A := centeredBridgePieceEvent m d
  have hprod : ∏ i, μ.real (A i)ᶜ ≤ μ.real (⋂ i, (A i)ᶜ) := by
    have haux : ∀ s : Finset (Fin 5),
        ∏ i ∈ s, μ.real (A i)ᶜ ≤ μ.real (⋂ i ∈ s, (A i)ᶜ) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.set_biInter_insert]
        have hm : MeasurableSet (⋂ j ∈ s, (A j)ᶜ) :=
          Finset.measurableSet_biInter s fun j _ => (measurableSet_centeredBridgePieceEvent m d j).compl
        have hl : IsLowerSet (⋂ j ∈ s, (A j)ᶜ) :=
          isLowerSet_iInter₂ fun j _ => (isUpperSet_centeredBridgePieceEvent m d j).compl
        exact (mul_le_mul_of_nonneg_left ih measureReal_nonneg).trans
          (bond_measureReal_mul_le_inter_of_lower μ ha
            (isUpperSet_centeredBridgePieceEvent m d i).compl hl
            (measurableSet_centeredBridgePieceEvent m d i).compl hm)
    simpa only [Finset.mem_univ, iInter_true] using haux Finset.univ
  have h := LQGMetric.Pitt.sqrt_trick (P := μ) (A := fun i => (A i)ᶜ)
    (fun i => (measurableSet_centeredBridgePieceEvent m d i).compl.nullMeasurableSet) hprod
  simpa only [A, compl_compl, Fintype.card_fin, Nat.cast_ofNat,
    ← centeredBridgeEvent_eq_iUnion_pieces m d] using h

end Sandpile.External.RSW
