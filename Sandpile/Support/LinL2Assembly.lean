/-
The `L²` assembly of Step 2 of `lem:dgt4-linearization-from-survival`
(`sandpile.tex:5803-5845`): the convex-linear bound of `lem:convex-linear-bound`
gives `∫(A-B)² ≤ C L² V_R + C η(L) B₀` for every `L > 0`, the variance sum `V_R`
tends to zero and `η(L) → 0` at infinity, so `∫(A-B)² → 0`; with the coefficient
replacement `∫C² → 0` the squared difference `∫(A-B-C)² → 0`.
-/
import Sandpile.Support.LinChooseL
import Sandpile.Support.LinL2Split

open MeasureTheory Filter Topology

namespace Sandpile

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `L²` convergence of the tested field from the convex-linear bound, the
vanishing variance sum and the vanishing coefficient replacement. -/
theorem tendsto_l2_of_convex_linear_and_replacement (P : Measure Ω)
    (A B C : ℝ → Ω → ℝ) (V η : ℝ → ℝ) (C₀ B₀ : ℝ)
    (hC₀ : 0 ≤ C₀) (hB₀ : 0 ≤ B₀)
    (hA : ∀ R, Integrable (fun ω => (A R ω - B R ω) ^ 2) P)
    (hCi : ∀ R, Integrable (fun ω => (C R ω) ^ 2) P)
    (hAC : ∀ R, Integrable (fun ω => (A R ω - B R ω - C R ω) ^ 2) P)
    (hV : ∀ᶠ R : ℝ in atTop, 0 ≤ ∫ ω, (A R ω - B R ω) ^ 2 ∂P)
    (hη : Tendsto η atTop (𝓝 0))
    (hbound : ∀ L : ℝ, 0 < L → ∀ᶠ R : ℝ in atTop,
      (∫ ω, (A R ω - B R ω) ^ 2 ∂P) ≤ C₀ * L ^ 2 * V R + C₀ * η L * B₀)
    (hVlim : Tendsto V atTop (𝓝 0))
    (hClim : Tendsto (fun R : ℝ => ∫ ω, (C R ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => ∫ ω, (A R ω - B R ω - C R ω) ^ 2 ∂P) atTop (𝓝 0) := by
  exact tendsto_l2_of_remainder_and_replacement P A B C hA hCi hAC
    (tendsto_zero_of_forall_L (V := fun R => ∫ ω, (A R ω - B R ω) ^ 2 ∂P)
      hC₀ hB₀ hV hη hbound hVlim) hClim

end Sandpile
