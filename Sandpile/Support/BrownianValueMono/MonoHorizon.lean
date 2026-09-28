import Sandpile.Support.BrownianValueMono.PositiveDim
import Sandpile.Support.BrownianValueMono.ZeroDimPackaged

/-!
# The Brownian value of the Gaussian heat potential increases with the horizon

Assembly of `Sandpile.Continuum.brownianValue_mono_horizon_gaussianPotential`, the provider for
the new paper-internal node of `lem:brownian-ball-localization` (`sandpile.tex:1640-1665`): for
the Gaussian heat potential `Z`, the Brownian value `𝒰_Z(s,z)` is at most `𝒰_Z(T,z)` whenever
`0 ≤ s ≤ T`.

The proof case-splits on the dimension. For `1 ≤ d ≤ 3`, `horizonFree_and_bddAbove_positive_dim`
supplies both hypotheses of the horizon-monotonicity lemma
`Sandpile.Continuum.brownianValue_mono_horizon` (`Sandpile/Support/ExplHorizon.lean`) from the
samplewise polynomial growth of the field and the backward heat-increment martingale along the
motion. For `d = 0`, `Space 0` is a single point and the field is exactly affine in time, so
`horizonFree_and_bddAbove_zero_dim` supplies the same two hypotheses by direct computation.
`Sandpile.Continuum.brownianValue_mono_horizon` then finishes both cases identically.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- **The Brownian value of the Gaussian heat potential is nondecreasing in the horizon:**
almost surely, `𝒰_Z(s,z) ≤ 𝒰_Z(T,z)` for every point `z` and every `0 ≤ s ≤ T`. Identical in
statement to `Sandpile.Frozen.brownian_value_mono_horizon`. -/
theorem brownianValue_mono_horizon_gaussianPotential (d : ℕ) (hd : d < 4) :
    ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
      (W : (Space d → ℝ) → ΩW → ℝ),
      IsWhiteNoise d W PW →
    ∀ ν2 : ℝ, 0 ≤ ν2 →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Space d → ℝ≥0 → ΩB → Space d),
      (∀ y : Space d, IsBrownian d y (B y) PB) →
      (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
      (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
    ∀ (Z : ℝ → Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
        ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) →
    ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∀ z : Space d, ∀ s ∈ Set.Icc (0 : ℝ) T,
      brownianValue (B z) PB (fun t x => Z t x ω) s z ≤
        brownianValue (B z) PB (fun t x => Z t x ω) T z := by
  intro ΩW _ PW _ W hW ν2 hν2 ΩB _ PB _ B hB hBc hBm Z hmod hc T hT
  have hcombined : ∀ᵐ ω ∂PW, ∀ x : Space d, ∀ s : ℝ, 0 ≤ s → s ≤ T →
      HorizonFreeIncrement (B x) PB (fun t y => Z t y ω) s T x ∧
        BddAbove (stoppingPayoffs (B x) PB (fun t y => Z t y ω) T) := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      exact horizonFree_and_bddAbove_zero_dim hW ν2 hν2 Z hmod hc B hB hBc hBm T hT
    · exact horizonFree_and_bddAbove_positive_dim hpos (by omega) hW ν2 hν2 Z hmod hc B hB hBc
        hBm T hT
  filter_upwards [hcombined] with ω hω z s hs
  obtain ⟨hs0, hsT⟩ := hs
  obtain ⟨hinc, hbdd⟩ := hω z s hs0 hsT
  exact brownianValue_mono_horizon (B z) PB (fun t x => Z t x ω) s T hs0 hsT z hinc hbdd

end Sandpile.Continuum
