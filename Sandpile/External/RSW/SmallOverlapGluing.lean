import Sandpile.External.RSW.BridgePieceSymmetry
import Sandpile.External.RSW.AspectGluing

/-!
# Long crossings from small extensions

A crossing of a square extended by a fixed amount can be glued repeatedly across square
overlaps. This supplies the side-crossing case of the bridge estimate.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Repeated square-overlap gluing extends a crossing by an arbitrary fixed increment. -/
theorem bondCrossing_increment_pow_le (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (n d k : ℕ) :
    μ.real (bondCrossingEvent (n + d) n) ^ (2 * k + 1) ≤
      μ.real (bondCrossingEvent (n + (k + 1) * d) n) := by
  let p := μ.real (bondCrossingEvent (n + d) n)
  have hp : 0 ≤ p := measureReal_nonneg
  have hsquare : p ≤ μ.real (bondCrossingEvent n n) :=
    measureReal_mono (bondCrossingEvent_width_height_mono (by omega) (by omega))
      (measure_ne_top μ _)
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, Nat.one_mul, pow_one, le_refl]
  | succ k ih =>
    have hglue := bondCrossing_prob_glue μ ha (m₁ := n + (k + 1) * d) (m₂ := n + d) (n := n)
      (by omega) (by omega) (ht _) hs
    have hw : (n + (k + 1) * d) + (n + d) - n = n + (k + 1 + 1) * d := by
      have he : (n + (k + 1) * d) + (n + d) = (n + (k + 1 + 1) * d) + n := by ring
      omega
    rw [hw] at hglue
    calc
      p ^ (2 * (k + 1) + 1) = (p ^ (2 * k + 1) * p) * p := by
        have he : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
        rw [he, pow_succ, pow_succ]
      _ ≤ (μ.real (bondCrossingEvent (n + (k + 1) * d) n) *
          μ.real (bondCrossingEvent n n)) * p := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul ih hsquare hp measureReal_nonneg) hp
      _ ≤ _ := hglue

/-- The side-to-side bridge piece is the centered rectangle crossing. -/
theorem kstBridgePiece_zero_eq_centeredCrossing (m : ℕ) :
    kstBridgePieceEvent m 0 = centeredBondCrossingEvent (m + m / 12) m := by
  ext ω
  exact (mem_centeredBondCrossingEvent_iff (m + m / 12) m ω).symm

/-- At scales divisible by twelve, the side-to-side bridge piece yields the desired long
crossing with a fixed power loss. -/
theorem kstBridgePiece_zero_pow_le_long (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (m : ℕ) (hm : 12 ∣ m) :
    μ.real (kstBridgePieceEvent m 0) ^ 167 ≤ μ.real (bondCrossingEvent (16 * m) (2 * m)) := by
  have hp := (ht (- ![((m + m / 12 : ℕ) : ℤ), (m : ℤ)])).measureReal_preimage
    (measurableSet_bondCrossingEvent (2 * (m + m / 12)) (2 * m)).nullMeasurableSet
  have he : μ.real (kstBridgePieceEvent m 0) =
      μ.real (bondCrossingEvent (2 * (m + m / 12)) (2 * m)) := by
    rw [kstBridgePiece_zero_eq_centeredCrossing]
    exact hp
  rw [he]
  have hh := bondCrossing_increment_pow_le μ ha ht hs (2 * m) (2 * (m / 12)) 83
  norm_num only at hh
  have hm' := Nat.div_mul_cancel hm
  have hbase : 2 * m + 2 * (m / 12) = 2 * (m + m / 12) := by omega
  have hlong : 2 * m + 84 * (2 * (m / 12)) = 16 * m := by omega
  rw [hbase, hlong] at hh
  exact hh

end Sandpile.External.RSW
