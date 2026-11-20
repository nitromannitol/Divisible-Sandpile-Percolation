import Sandpile.External.RSW.RectangleGluingProbability

/-!
# Gluing rectangles of integer aspect ratio

A bound on a two-to-one horizontal crossing extends to every larger integer aspect ratio
by repeatedly gluing across squares.
-/

open MeasureTheory Set Percolation.Literature

namespace Sandpile.External.RSW

/-- Reducing the width and increasing the height can only make a bond crossing easier. -/
theorem bondCrossingEvent_width_height_mono {w W h H : ℕ} (hw : w ≤ W) (hh : h ≤ H) :
    bondCrossingEvent W h ⊆ bondCrossingEvent w H := by
  intro ω hω
  apply (mem_bondCrossingEvent_iff_lrCrossing w H ω).mpr
  apply lrCrossing_mono_right w hh
  exact lrCrossing_anti_left hw h (openPlaneBonds_subset ω)
    ((mem_bondCrossingEvent_iff_lrCrossing W h ω).mp hω)

/-- Repeated gluing for a translation- and interchange-invariant associated bond law. -/
theorem bondCrossing_two_pow_le (μ : Measure (Sym2 (Site 2) → Bool))
    [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (n k : ℕ) :
    μ.real (bondCrossingEvent (2 * n) n) ^ (2 * k + 1) ≤
      μ.real (bondCrossingEvent ((k + 2) * n) n) := by
  let p := μ.real (bondCrossingEvent (2 * n) n)
  have hp : 0 ≤ p := measureReal_nonneg
  have hsquare : p ≤ μ.real (bondCrossingEvent n n) :=
    measureReal_mono (bondCrossingEvent_width_height_mono (by omega) (by omega))
      (measure_ne_top μ _)
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, pow_one, le_refl]
  | succ k ih =>
    have hglue := bondCrossing_prob_glue μ ha (m₁ := (k + 2) * n) (m₂ := 2 * n)
      (by nlinarith) (by omega) (ht _) hs
    have hw : (k + 2) * n + 2 * n - n = (k + 1 + 2) * n := by
      have hh : (k + 2) * n + 2 * n = (k + 1 + 2) * n + n := by ring
      omega
    rw [hw] at hglue
    calc
      p ^ (2 * (k + 1) + 1) = (p ^ (2 * k + 1) * p) * p := by
        have he : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
        rw [he, pow_succ, pow_succ]
      _ ≤ (μ.real (bondCrossingEvent ((k + 2) * n) n) *
          μ.real (bondCrossingEvent n n)) * p := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul ih hsquare hp (measureReal_nonneg)) hp
      _ ≤ _ := hglue

/-- Repeated overlap gluing bounds an integer-aspect crossing in terms of the two-to-one
crossing probability. -/
theorem fieldCrossing_two_pow_le (μ : Measure (Site 2 → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSymmetricPlanarLaw μ) (ha : IsAssociatedPlanarLaw μ) (level : ℝ)
    {n : ℕ} (hn : 0 < n) (k : ℕ) :
    μ.real (planarCrossingEvent (2 * n) n level) ^ (2 * k + 1) ≤
      μ.real (planarCrossingEvent ((k + 2) * n) n level) := by
  let p := μ.real (planarCrossingEvent (2 * n) n level)
  have hp : 0 ≤ p := measureReal_nonneg
  have hsquare : p ≤ μ.real (planarCrossingEvent n n level) :=
    measureReal_mono (planarCrossingEvent_width_height_mono (by omega) (by omega) level)
      (measure_ne_top μ _)
  induction k with
  | zero => simp only [Nat.mul_zero, Nat.zero_add, pow_one, le_refl]
  | succ k ih =>
    have hglue := fieldCrossing_prob_glue μ hμ ha level hn
      (m₁ := (k + 2) * n) (m₂ := 2 * n) (by nlinarith) (by omega)
    have hw : (k + 2) * n + 2 * n - n = (k + 1 + 2) * n := by
      have hh : (k + 2) * n + 2 * n = (k + 1 + 2) * n + n := by ring
      omega
    rw [hw] at hglue
    calc
      p ^ (2 * (k + 1) + 1) = (p ^ (2 * k + 1) * p) * p := by
        have he : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
        rw [he, pow_succ, pow_succ]
      _ ≤ (μ.real (planarCrossingEvent ((k + 2) * n) n level) *
          μ.real (planarCrossingEvent n n level)) * p := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul ih hsquare hp (measureReal_nonneg)) hp
      _ ≤ _ := hglue

end Sandpile.External.RSW
