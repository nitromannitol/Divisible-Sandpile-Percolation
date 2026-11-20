import Sandpile.External.RSW.TranslatedBottomBridge
import Sandpile.External.RSW.EdgePathProbability

/-!
# Gluing bottom bridges into a long crossing

Ninety-six translated bottom bridges have overlapping central intervals that cover the
target rectangle. Positive association bounds their intersection probability.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Sandpile.External.RSW

/-- The endpoints of the successive central intervals. -/
def kstBottomGridPoint (m i : ℕ) : ℤ :=
  -(8 * (m : ℤ)) + 2 * (i : ℤ) * ((m / 12 : ℕ) : ℤ)

/-- The translation placing a bottom bridge over its central interval. -/
def kstBottomBridgeShift (m i : ℕ) : Site 2 :=
  ![kstBottomGridPoint m i + ((m / 12 : ℕ) : ℤ), 0]

/-- The event of a bottom bridge at a translated central interval. -/
def translatedKSTBottomBridgeEvent (m i : ℕ) : Set (Sym2 (Site 2) → Bool) :=
  (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + kstBottomBridgeShift m i)) ⁻¹'
    kstBottomBridgeEvent m

/-- Translated bottom bridge events are increasing. -/
theorem isUpperSet_translatedKSTBottomBridgeEvent (m i : ℕ) :
    IsUpperSet (translatedKSTBottomBridgeEvent m i) := by
  intro ω η hω h
  exact isUpperSet_kstBottomBridgeEvent m (fun e => hω _) h

/-- Translated bottom bridge events are measurable. -/
theorem measurableSet_translatedKSTBottomBridgeEvent (m i : ℕ) :
    MeasurableSet (translatedKSTBottomBridgeEvent m i) := by
  apply (measurableSet_kstBottomBridgeEvent m).preimage
  exact Measurable.of_eval (fun e => measurable_pi_apply _)

/-- The central interval endpoints increase with their index. -/
theorem monotone_kstBottomGridPoint (m : ℕ) : Monotone (kstBottomGridPoint m) := by
  intro i j hij
  have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
  have hβ : (0 : ℤ) ≤ ((m / 12 : ℕ) : ℤ) := by positivity
  have hp := mul_nonneg (sub_nonneg.mpr hij') hβ
  dsimp only [kstBottomGridPoint]
  nlinarith

/-- The bottom-bridge centers used in the chain fit in the common rectangle. -/
theorem kstBottomBridgeShift_bounds (m i : ℕ) (hm : 12 ∣ m) (hi : i < 96) :
    -(8 * (m : ℤ)) + ((m / 12 : ℕ) : ℤ) ≤
        kstBottomGridPoint m i + ((m / 12 : ℕ) : ℤ) ∧
      kstBottomGridPoint m i + ((m / 12 : ℕ) : ℤ) ≤
        8 * (m : ℤ) - ((m / 12 : ℕ) : ℤ) := by
  have hm' : (m : ℤ) = 12 * ((m / 12 : ℕ) : ℤ) := by
    have hh : m = 12 * (m / 12) := by
      have hh := Nat.div_mul_cancel hm
      omega
    exact_mod_cast hh
  have hi' : (i : ℤ) ≤ 95 := by exact_mod_cast (show i ≤ 95 by omega)
  have hi0 : (0 : ℤ) ≤ i := by positivity
  have hβ : (0 : ℤ) ≤ ((m / 12 : ℕ) : ℤ) := by positivity
  have hprod := mul_nonneg (sub_nonneg.mpr hi') hβ
  have hprod' := mul_nonneg hi0 hβ
  dsimp only [kstBottomGridPoint]
  constructor <;> nlinarith

/-- The chain starts and ends at the sides of the aspect-eight rectangle. -/
theorem kstBottomGridPoint_endpoints (m : ℕ) (hm : 12 ∣ m) :
    kstBottomGridPoint m 0 = -(8 * (m : ℤ)) ∧ kstBottomGridPoint m 96 = 8 * (m : ℤ) := by
  have hm' : (m : ℤ) = 12 * ((m / 12 : ℕ) : ℤ) := by
    have hh : m = 12 * (m / 12) := by
      have hh := Nat.div_mul_cancel hm
      omega
    exact_mod_cast hh
  constructor
  · simp [kstBottomGridPoint]
  · change -(8 * (m : ℤ)) + 2 * 96 * ((m / 12 : ℕ) : ℤ) = 8 * (m : ℤ)
    linarith

/-- The intersection of the translated bottom bridges produces the centered long crossing. -/
theorem iInter_translatedKSTBottomBridge_subset_crossing (m : ℕ) (hm : 12 ∣ m) :
    (⋂ i : Fin 96, translatedKSTBottomBridgeEvent m i) ⊆
      centeredBondCrossingEvent (8 * m) m := by
  intro ω hω
  have hwalk : ∀ i < 96, ∃ (a b : centeredPlaneRectangle (9 * m) m)
      (p : (rectangleGraph (centeredPlaneRectangle (9 * m) m)).Walk a b),
      IsBondOpenWalk ω p ∧ (a : Site 2) 1 = -(m : ℤ) ∧ (b : Site 2) 1 = -(m : ℤ) ∧
      (a : Site 2) 0 ≤ kstBottomGridPoint m i ∧
      kstBottomGridPoint m (i + 1) ≤ (b : Site 2) 0 := by
    intro i hi
    have hb := (mem_iInter.mp hω) ⟨i, hi⟩
    have hbounds := kstBottomBridgeShift_bounds m i hm hi
    obtain ⟨a, b, p, hp, ha, hb', hal, hbr⟩ :=
      translated_kstBottomBridge_spanning m
        (kstBottomGridPoint m i + ((m / 12 : ℕ) : ℤ)) hbounds.1 hbounds.2 hb
    refine ⟨a, b, p, hp, ha, hb', ?_, ?_⟩
    · linarith
    · have he : kstBottomGridPoint m (i + 1) =
          kstBottomGridPoint m i + 2 * ((m / 12 : ℕ) : ℤ) := by
        simp only [kstBottomGridPoint, Nat.cast_add, Nat.cast_one]
        ring
      rw [he]
      linarith
  obtain ⟨a, b, p, hp, _, _, hal, hbr⟩ :=
    exists_open_bottom_walk_spanning_chain (kstBottomGridPoint m) (monotone_kstBottomGridPoint m)
      96 hwalk 95 (by omega)
  have he := kstBottomGridPoint_endpoints m hm
  apply centeredBondCrossingEvent_of_spanning_walk p hp
  · have : kstBottomGridPoint m 0 = -((8 * m : ℕ) : ℤ) := by push_cast; exact he.1
    rw [← this]
    exact hal
  · have : kstBottomGridPoint m (95 + 1) = ((8 * m : ℕ) : ℤ) := by
      norm_num only
      push_cast
      exact he.2
    rw [← this]
    exact hbr

/-- Positive association glues the translated bottom bridges into an aspect-eight crossing. -/
theorem kstBottomBridge_pow_le_long (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (m : ℕ) (hm : 12 ∣ m) :
    μ.real (kstBottomBridgeEvent m) ^ 96 ≤ μ.real (bondCrossingEvent (16 * m) (2 * m)) := by
  let A : Fin 96 → Set (Sym2 (Site 2) → Bool) := fun i => translatedKSTBottomBridgeEvent m i
  have hp (i : Fin 96) : μ.real (A i) = μ.real (kstBottomBridgeEvent m) :=
    (ht (kstBottomBridgeShift m i)).measureReal_preimage
      (measurableSet_kstBottomBridgeEvent m).nullMeasurableSet
  have hprod := bond_prod_measureReal_le_biInter μ ha A
    (fun i => isUpperSet_translatedKSTBottomBridgeEvent m i)
    (fun i => measurableSet_translatedKSTBottomBridgeEvent m i) Finset.univ
  have hprob : μ.real (kstBottomBridgeEvent m) ^ 96 ≤ μ.real (⋂ i : Fin 96, A i) := by
    simpa only [hp, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.mem_univ, iInter_true] using hprod
  have hcenter : μ.real (centeredBondCrossingEvent (8 * m) m) =
      μ.real (bondCrossingEvent (16 * m) (2 * m)) := by
    have hh := (ht (- ![((8 * m : ℕ) : ℤ), (m : ℤ)])).measureReal_preimage
      (measurableSet_bondCrossingEvent (2 * (8 * m)) (2 * m)).nullMeasurableSet
    have he : 2 * (8 * m) = 16 * m := by omega
    change μ.real ((fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + (- ![((8 * m : ℕ) : ℤ), (m : ℤ)]))) ⁻¹'
      bondCrossingEvent (2 * (8 * m)) (2 * m)) = _
    rw [← he]
    exact hh
  exact hprob.trans ((measureReal_mono (iInter_translatedKSTBottomBridge_subset_crossing m hm)
    (measure_ne_top μ _)).trans hcenter.le)

end Sandpile.External.RSW
