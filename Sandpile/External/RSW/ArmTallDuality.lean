import Sandpile.External.RSW.DualRotatedProbability

/-!
# Duality for the tall crossing

A tall rectangle crossing and a crossing of the rotated dual rectangle have
complementary probabilities with their exact discrete boundary dimensions.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- The complement of the tall crossing is the probability of the long dual crossing
with the one-unit boundary shifts. -/
theorem measureReal_tallCrossing_add_dual_long (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (m : ℕ) (hm : 0 < m) :
    μ.real (bondCrossingEvent (2 * m) (16 * m)) +
      (μ.map dualBondConfig).real (bondCrossingEvent (16 * m + 1) (2 * m - 1)) = 1 := by
  let ν := μ.map dualBondConfig
  have htν : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) ν ν :=
    fun v => measurePreserving_dualBondConfig_translate μ v (ht v)
  have hsν : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) ν ν := measurePreserving_dualBondConfig_swap μ hs
  have hiso := measurePreserving_dualCrossingIso ν (htν _) hsν
  have hwidth : (2 * m - 1) + 1 = 2 * m := by omega
  have h := measureReal_bondCrossing_add_shiftedDual μ ((2 * m - 1) + 1) (16 * m)
  rw [measureReal_shiftedDualCrossing_eq_rotated μ (2 * m - 1) (16 * m) hiso, hwidth] at h
  exact h

end Sandpile.External.RSW
