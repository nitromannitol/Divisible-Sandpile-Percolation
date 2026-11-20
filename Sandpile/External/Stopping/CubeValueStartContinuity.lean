import Sandpile.External.Stopping.CubeStoppingValueLaw
import Sandpile.Support.D23CubeValueRegularity

/-!
# Continuity of cube-killed stopping values in the start

The law invariance of cube-killed values removes any need to assume that a
family of Brownian motions is coupled by translation.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- For bounded continuous rewards, the cube-killed value is continuous in the
starting point for any family of continuous Brownian realizations. -/
theorem continuous_brownianDiscountCube_family_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} [NeZero d]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Continuum.Space d → ℝ≥0 → Ω → Continuum.Space d)
    (hB : ∀ x, Continuum.IsBrownian d x (B x) P)
    (hBm : ∀ x t, Measurable (B x t))
    (hBc : ∀ x ω, Continuous fun t => B x t ω)
    (T : ℝ≥0) (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) :
    Continuous fun x => Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x := by
  have heq : (fun x => Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x) =
      fun x => Continuum.brownianDiscountCube (B 0) P (fun s z => -G s (x + z)) T 1 0 := by
    funext x
    let C : ℝ≥0 → Ω → Continuum.Space d := fun t ω => x + B 0 t ω
    have hC : Continuum.IsBrownian d x C P := Sandpile.Support.isBrownian_add_const d P (B 0) (hB 0) x
    have hCm : ∀ t, Measurable (C t) := fun t => measurable_const.add (hBm 0 t)
    have hCc : ∀ ω, Continuous fun t => C t ω := fun ω => continuous_const.add (hBc 0 ω)
    calc
      Continuum.brownianDiscountCube (B x) P (fun s z => -G s z) T 1 x =
          Continuum.brownianDiscountCube C P (fun s z => -G s z) T 1 x :=
        brownianDiscountCube_eq_of_continuous_isBrownian P P x (B x) C (hB x) hC
          (hBm x) hCm (hBc x) hCc T G hGc M hG
      _ = Continuum.brownianDiscountCube (B 0) P (fun s z => -G s (x + z)) T 1 0 := by
        unfold Continuum.brownianDiscountCube
        exact congrArg sSup (Sandpile.Support.cubeStoppingPayoffs_add_const P (B 0)
          (fun s z => -G s z) T 1 x)
  rw [heq]
  exact Sandpile.Support.continuous_brownianDiscountCube_shift P (B 0) (hB 0)
    (fun s z => -G s z) hGc.neg T 1 (NNReal.coe_nonneg T) zero_le_one

end Sandpile.External.Stopping
