import Sandpile.External.RSW.AdjacentSixEvents
import Sandpile.External.RSW.ScalePowerBounds

/-!
# Reducing adjacent quasi-crossings to arm geometry

The six-event probability bound and comparison-function power bound reduce the
adjacent-scale quasi-crossing estimate to a geometric inclusion and three arm bounds.
-/

open MeasureTheory Set

namespace Sandpile.External.RSW

/-- Three arm bounds and the six-event geometric inclusion imply the adjacent-scale
quasi-crossing bound. -/
theorem measureReal_adjacentQuasi_ge_of_six_events
    (μ : Measure (Sym2 (Site 2) → Bool)) [IsProbabilityMeasure μ]
    (ha : ∀ A B : Set (Sym2 (Site 2) → Bool), IsUpperSet A → IsUpperSet B →
      MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
    (ht : ∀ v : Site 2, MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map (fun z => z + v)) μ μ)
    (hs : MeasurePreserving (fun ω : Sym2 (Site 2) → Bool =>
      ω ∘ Sym2.map swapPlaneSite) μ μ) (j : ℕ) (x : Icc (0 : ℝ) 1)
    (hgeom : kstAdjacentSixEvent (kstBaseScale j) ⊆
      kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j))
    (h₀ : (kstScaleIso 1 x : ℝ) ≤ μ.real (kstArmEvent (kstBaseScale j)))
    (h₁ : (kstScaleIso 1 x : ℝ) ≤ μ.real (kstArmEvent (5 * kstBaseScale j / 2)))
    (h₂ : (kstScaleIso 1 x : ℝ) ≤ μ.real (kstArmEvent (31 * kstBaseScale j / 8))) :
    (kstScaleIso 2 x : ℝ) ≤
      μ.real (kstQuasiCrossingEvent (4 * kstBaseScale j) (kstBaseScale j)) := by
  let f := (kstScaleIso 1 x : ℝ)
  let a := μ.real (kstArmEvent (kstBaseScale j))
  let b := μ.real (kstArmEvent (5 * kstBaseScale j / 2))
  let c := μ.real (kstArmEvent (31 * kstBaseScale j / 8))
  have hf : 0 ≤ f := (kstScaleIso 1 x).property.1
  have h₀' : f ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hf h₀ 2
  have h₁' : f ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hf h₁ 2
  have h₂' : f ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hf h₂ 2
  have hprod : f ^ 6 ≤ a ^ 2 * b ^ 2 * c ^ 2 := by
    calc
      f ^ 6 = (f ^ 2 * f ^ 2) * f ^ 2 := by ring
      _ ≤ (a ^ 2 * b ^ 2) * c ^ 2 :=
        mul_le_mul (mul_le_mul h₀' h₁' (sq_nonneg _) (sq_nonneg _)) h₂'
          (sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact (kstScaleIso_succ_le_pow 1 6 (by omega) (by omega) x).trans
    (hprod.trans ((measureReal_kstAdjacentSixEvent_ge μ ha ht hs j).trans
      (measureReal_mono hgeom (measure_ne_top μ _))))

end Sandpile.External.RSW
