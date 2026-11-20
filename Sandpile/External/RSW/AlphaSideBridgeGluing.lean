import Sandpile.External.RSW.CenteredBridgeDecomposition
import Sandpile.External.RSW.SmallOverlapGluing

/-!
# Long crossings from narrow bridge crossings

Repeated square-overlap gluing turns the side-to-side piece of the bridge with offset
`m / 64` into an aspect-eight crossing.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The side-to-side bridge piece is the centered rectangle crossing. -/
theorem centeredBridgePiece_zero_eq_alpha_centeredCrossing (m : ℕ) :
    centeredBridgePieceEvent m (m / 64) 0 = centeredBondCrossingEvent (m + m / 64) m := by
  ext ω
  exact (mem_centeredBondCrossingEvent_iff (m + m / 64) m ω).symm

/-- At scales divisible by sixty-four, the side-to-side bridge piece yields the desired long
crossing with a fixed power loss. -/
theorem centeredBridgePiece_zero_pow_le_long (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (m : ℕ) (hm : 64 ∣ m) :
    μ.real (centeredBridgePieceEvent m (m / 64) 0) ^ 895 ≤ μ.real (bondCrossingEvent (16 * m) (2 * m)) := by
  have hp := (ht (- ![((m + m / 64 : ℕ) : ℤ), (m : ℤ)])).measureReal_preimage
    (measurableSet_bondCrossingEvent (2 * (m + m / 64)) (2 * m)).nullMeasurableSet
  have he : μ.real (centeredBridgePieceEvent m (m / 64) 0) =
      μ.real (bondCrossingEvent (2 * (m + m / 64)) (2 * m)) := by
    rw [centeredBridgePiece_zero_eq_alpha_centeredCrossing]
    exact hp
  rw [he]
  have hh := bondCrossing_increment_pow_le μ ha ht hs (2 * m) (2 * (m / 64)) 447
  norm_num only at hh
  have hm' := Nat.div_mul_cancel hm
  have hbase : 2 * m + 2 * (m / 64) = 2 * (m + m / 64) := by omega
  have hlong : 2 * m + 448 * (2 * (m / 64)) = 16 * m := by omega
  rw [hbase, hlong] at hh
  exact hh

end Sandpile.External.RSW
