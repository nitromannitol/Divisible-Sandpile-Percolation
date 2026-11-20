import Sandpile.External.Stopping.CubeStabilityNecessity
import Sandpile.External.Stopping.CompletedCubeStartContinuity

/-!
# Realization invariance implied by cube stability

Translation extends any Brownian realization to a family of starting points,
so cube stability entails equality of the values of any two realizations.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Cube stability entails equality of the cube-killed values of any two
Brownian motions at the same starting point and positive horizon. -/
theorem brownianDiscountCube_eq_of_cubeStoppingStability_of_isBrownian
    (h : Sandpile.External.CubeStoppingStability) (d : ℕ) [NeZero d]
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (x : Continuum.Space d)
    (B : ℝ≥0 → Ω → Continuum.Space d) (C : ℝ≥0 → Ω' → Continuum.Space d)
    (hB : Continuum.IsBrownian d x B P) (hC : Continuum.IsBrownian d x C Q)
    (T : ℝ) (hT : 0 < T) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ t z, |G t z| ≤ M) :
    Continuum.brownianDiscountCube B P (fun s z => -G s z) T 1 x =
      Continuum.brownianDiscountCube C Q (fun s z => -G s z) T 1 x := by
  let V : ℝ≥0 → Ω → Continuum.Space d := fun t ω => B t ω - x
  let W : ℝ≥0 → Ω' → Continuum.Space d := fun t ω => C t ω - x
  have hVL := isBrownianSpace_sub_start hB
  have hWL := isBrownianSpace_sub_start hC
  have hV : Continuum.IsBrownian d 0 V P := ⟨hVL.start, hVL.coord, hVL.indep⟩
  have hW : Continuum.IsBrownian d 0 W Q := ⟨hWL.start, hWL.coord, hWL.indep⟩
  let Bfamily : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d := fun y t ω => y + V t ω
  let Cfamily : Continuum.Space d → ℝ≥0 → Ω' → Continuum.Space d := fun y t ω => y + W t ω
  have hBfamily : ∀ y, Continuum.IsBrownian d y (Bfamily y) P :=
    fun y => Sandpile.Support.isBrownian_add_const d P V hV y
  have hCfamily : ∀ y, Continuum.IsBrownian d y (Cfamily y) Q :=
    fun y => Sandpile.Support.isBrownian_add_const d Q W hW y
  have hBeq : Bfamily x = B := by
    funext t ω
    dsimp only [Bfamily, V]
    abel
  have hCeq : Cfamily x = C := by
    funext t ω
    dsimp only [Cfamily, W]
    abel
  have heq := brownianDiscountCube_eq_of_cubeStoppingStability h d
    (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)) P Q Bfamily Cfamily hBfamily hCfamily
    T hT x G hGc M hG
  rwa [hBeq, hCeq] at heq

end Sandpile.External.Stopping
