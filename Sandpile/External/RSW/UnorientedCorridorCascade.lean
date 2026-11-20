import Sandpile.External.RSW.UnorientedCascadeProbability
import Sandpile.External.RSW.CorridorCascade

/-!
# The unoriented corridor cascade

The corridor bridge cover for paths with no smaller subpath in either direction
implies the division-free cascade estimate.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The corridor bridge cover for unoriented exceptional paths. -/
def KSTUnorientedCorridorBridgeCover (n m k : ℕ) : Prop :=
  kstUnorientedExceptionalPathEvent n m k ∩ kstQuasiCrossingEvent m k ⊆
    translatedKSTBridgeEvent m (-kstCorridorShift m) ∪
      translatedKSTBridgeEvent m (kstCorridorShift m)

/-- The unoriented corridor bridge cover implies the division-free cascade estimate. -/
theorem kstUnorientedCorridor_cascade_probability (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (n m k : ℕ) (hcover : KSTUnorientedCorridorBridgeCover n m k) {δ : ℝ} (hδ : δ ≤ 1)
    (hsmall : μ.real (kstQuasiCrossingEvent n k) < δ)
    (hlarge : 1 - (1 - δ) ^ 2 ≤ μ.real (kstQuasiCrossingEvent n m)) :
    δ * μ.real (kstQuasiCrossingEvent m k) ≤ 1 - (1 - μ.real (kstBridgeEvent m)) ^ 2 := by
  let v := kstCorridorShift m
  have hp₁ := measureReal_translatedKSTBridgeEvent μ m (-v) (ht (-v))
  have hp₂ := measureReal_translatedKSTBridgeEvent μ m v (ht v)
  have hh := kstUnorientedQuasiCascade_probability μ ha n m k
    (isUpperSet_translatedKSTBridgeEvent m (-v)) (isUpperSet_translatedKSTBridgeEvent m v)
    (measurableSet_translatedKSTBridgeEvent m (-v)) (measurableSet_translatedKSTBridgeEvent m v)
    hcover (hp₁.trans hp₂.symm) hδ hsmall hlarge
  rwa [hp₁] at hh

end Sandpile.External.RSW
