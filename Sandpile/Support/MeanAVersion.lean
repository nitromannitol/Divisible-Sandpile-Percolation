import Sandpile.Support.MeanAKolmogorov
import Sandpile.Support.GrowExternalDischarge
import Sandpile.Continuum.WhiteNoiseExists

/-!
# A continuous, polynomially growing version of the heat potential

The field `Z` of `sandpile.tex:1019-1021`, with the three properties the statements of
`ssec:scaling-dlt4` ask of it. `MeanAKolmogorov` constructs a modification of the Gaussian heat
potential whose paths are almost surely continuous on every strip `[0,T] × ℝ^d`, and
`continuousVersionGrowth` gives the polynomial-growth bound of every such modification, proved
rather than assumed. Putting the two together gives a field with all three properties, applied
here to the white noise the repository builds rather than only assumed about some field.
-/

open MeasureTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **The continuous version of the Gaussian heat potential, with polynomial
growth on every strip.**  Both the modification and its growth are proved. -/
theorem exists_continuous_version_growth
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {ΩW : Type} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW) :
    ∃ Z : ℝ → Space d → ΩW → ℝ,
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) ∧
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
        ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) ∧
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
        ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
          |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k) := by
  obtain ⟨Z, hmod, hcont⟩ := exists_continuous_version hd hd3 hν2 PW W hW
  exact ⟨Z, hmod, hcont, continuousVersionGrowth d hd hd3 ν2 hν2 ΩW PW W hW Z hmod hcont⟩

/-- **The white noise the repository builds carries such a field.** -/
theorem exists_whiteNoise_continuous_version_growth
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2) :
    ∃ (ΩW : Type) (_ : MeasurableSpace ΩW) (PW : Measure ΩW) (_ : IsProbabilityMeasure PW)
      (W : (Space d → ℝ) → ΩW → ℝ) (_ : IsWhiteNoise d W PW)
      (Z : ℝ → Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) ∧
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
        ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω)
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)))) ∧
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∃ C k : ℝ,
        ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set (Space d)),
          |Z p.1 p.2 ω| ≤ C * (1 + ‖p.2‖) ^ k) := by
  obtain ⟨ΩW, mW, PW, hPW, W, hW⟩ := Sandpile.Continuum.exists_isWhiteNoise d
  obtain ⟨Z, h1, h2, h3⟩ := exists_continuous_version_growth hd hd3 hν2 PW W hW
  exact ⟨ΩW, mW, PW, hPW, W, hW, Z, h1, h2, h3⟩

end Sandpile.Support
