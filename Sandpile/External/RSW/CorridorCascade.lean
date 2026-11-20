import Sandpile.External.RSW.QuasiCascadeProbability

/-!
# The corridor-to-cascade reduction

The corridor construction sends an exceptional path and a smaller quasi-crossing into one
of two translates of the bridge event. Translation invariance and positive association
then yield the division-free cascade estimate.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- A translated bridge event. -/
def translatedKSTBridgeEvent (m : ℕ) (v : Site 2) : Set (Sym2 (Site 2) → Bool) :=
  (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) ⁻¹' kstBridgeEvent m

/-- A translated bridge event is increasing. -/
theorem isUpperSet_translatedKSTBridgeEvent (m : ℕ) (v : Site 2) :
    IsUpperSet (translatedKSTBridgeEvent m v) := by
  intro ω η hω h
  apply isUpperSet_kstBridgeEvent m (fun e => hω _) h

/-- A translated bridge event is measurable. -/
theorem measurableSet_translatedKSTBridgeEvent (m : ℕ) (v : Site 2) :
    MeasurableSet (translatedKSTBridgeEvent m v) := by
  apply (measurableSet_kstBridgeEvent m).preimage
  exact Measurable.of_eval (fun e => measurable_pi_apply _)

/-- Translation invariance preserves the probability of a bridge. -/
theorem measureReal_translatedKSTBridgeEvent (μ : Measure (Sym2 (Site 2) → Bool))
    (m : ℕ) (v : Site 2) (ht : MeasurePreserving
      (fun ω : Sym2 (Site 2) → Bool => ω ∘ Sym2.map (fun z => z + v)) μ μ) :
    μ.real (translatedKSTBridgeEvent m v) = μ.real (kstBridgeEvent m) :=
  ht.measureReal_preimage (measurableSet_kstBridgeEvent m).nullMeasurableSet

/-- The two horizontal translations in the corridor cascade. -/
def kstCorridorShift (m : ℕ) : Site 2 := ![((2 * (m / 12) : ℕ) : ℤ), 0]

/-- The deterministic corridor bridge cover at the three indicated scales. -/
def KSTCorridorBridgeCover (n m k : ℕ) : Prop :=
  kstExceptionalPathEvent n m k ∩ kstQuasiCrossingEvent m k ⊆
    translatedKSTBridgeEvent m (-kstCorridorShift m) ∪
      translatedKSTBridgeEvent m (kstCorridorShift m)

/-- The corridor bridge cover implies the KST cascade probability estimate without division. -/
theorem kstCorridor_cascade_probability (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (n m k : ℕ) (hcover : KSTCorridorBridgeCover n m k) {δ : ℝ} (hδ : δ ≤ 1)
    (hsmall : μ.real (kstQuasiCrossingEvent n k) < δ)
    (hlarge : 1 - (1 - δ) ^ 2 ≤ μ.real (kstQuasiCrossingEvent n m)) :
    δ * μ.real (kstQuasiCrossingEvent m k) ≤ 1 - (1 - μ.real (kstBridgeEvent m)) ^ 2 := by
  let v := kstCorridorShift m
  have hp₁ := measureReal_translatedKSTBridgeEvent μ m (-v) (ht (-v))
  have hp₂ := measureReal_translatedKSTBridgeEvent μ m v (ht v)
  have hh := kstQuasiCascade_probability μ ha n m k
    (isUpperSet_translatedKSTBridgeEvent m (-v)) (isUpperSet_translatedKSTBridgeEvent m v)
    (measurableSet_translatedKSTBridgeEvent m (-v)) (measurableSet_translatedKSTBridgeEvent m v)
    hcover (hp₁.trans hp₂.symm) hδ hsmall hlarge
  rwa [hp₁] at hh

/-- The quotient form of the cascade estimate when the intermediate quasi-crossing has
positive probability. -/
theorem kstCorridor_cascade_max (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (n m k : ℕ) (hcover : KSTCorridorBridgeCover n m k)
    (hpos : 0 < μ.real (kstQuasiCrossingEvent m k)) :
    1 - Real.sqrt (1 - μ.real (kstQuasiCrossingEvent n m)) ≤
      max (μ.real (kstQuasiCrossingEvent n k))
        ((1 - (1 - μ.real (kstBridgeEvent m)) ^ 2) / μ.real (kstQuasiCrossingEvent m k)) := by
  let δ := 1 - Real.sqrt (1 - μ.real (kstQuasiCrossingEvent n m))
  have hδ : δ ≤ 1 := by dsimp [δ]; linarith [Real.sqrt_nonneg (1 - μ.real (kstQuasiCrossingEvent n m))]
  have hlarge : 1 - (1 - δ) ^ 2 ≤ μ.real (kstQuasiCrossingEvent n m) := by
    dsimp only [δ]
    rw [sub_sub_cancel, Real.sq_sqrt (sub_nonneg.mpr measureReal_le_one)]
    linarith
  by_cases hsmall : μ.real (kstQuasiCrossingEvent n k) < δ
  · have hh := kstCorridor_cascade_probability μ ha ht n m k hcover hδ hsmall hlarge
    exact (le_div_iff₀ hpos).2 hh |>.trans (le_max_right _ _)
  · exact (le_of_not_gt hsmall).trans (le_max_left _ _)

end Sandpile.External.RSW
