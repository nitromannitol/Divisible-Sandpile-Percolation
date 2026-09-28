import Sandpile.Support.ContValueScaling
import Sandpile.Support.MeanAValue

/-! # Continuum value transfer lemmas

The two transfers of `sandpile.tex:1985-1993` that the continuous modification of
`prop:continuum-value-selfsimilar` buys, and the algebraic scaling of the value.

The paper's proof of `prop:continuum-value-selfsimilar` reads: "Stationarity of
white noise gives `𝒰(T,x) =^d 𝒰(T,0)`.  Brownian scaling then gives
`{Z(Ts,√T y)} =^d {T^{1-d/4} Z(s,y)}`.  Rescaling time by `T` identifies Brownian
stopping times bounded by `T` with Brownian stopping times bounded by `1`, and the
stopping value scales by the same factor."

`continuumValue_scaled_transfer` is the last sentence: the value built from a field
`Z` at `(T,x)` is `T^β` times the value of the rescaled field against the rescaled
motion at `(1,0)`, which is `Sandpile.Support.brownianValue_scaled` read through the
definition of `continuumValue`.

`continuumValue_field_transfer` is the transfer the modification buys: the value
reads the field at uncountably many points, so agreement of the modification with
the Gaussian heat potential almost surely at each point is not enough; agreement
almost surely as a function on `[0,T] × ℝ^d` is, and that is what the continuity
clause of the modification supplies.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open Sandpile.Continuum

namespace Sandpile.Support

/-- **The scaling transfer of `sandpile.tex:1991-1993`.**  The value built from the
field `Z` at `(T,x)` is `T^β` times the value of the rescaled field against the
rescaled motion at `(1,0)`. -/
theorem continuumValue_scaled_transfer {ΩW ΩB : Type*} [MeasurableSpace ΩB]
    (d : ℕ) (Z : ℝ → Space d → ΩW → ℝ)
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB)
    {T : ℝ≥0} (hT : T ≠ 0) (x : Space d) (β : ℝ) (ω : ΩW) :
    continuumValue d Z B PB (T : ℝ) x ω
      = (T : ℝ) ^ β * brownianValue (scaledMotion d T x (B x)) PB
          (scaledField d T β x (fun t z => Z t z ω)) 1 0 := by
  exact Sandpile.Support.brownianValue_scaled d hT x (B x) PB β (fun t z => Z t z ω)

/-- **The field transfer.**  If the modification `Z` agrees with the Gaussian heat
potential on the box `[0,T] × ℝ^d` almost surely as a function, then the stopping
value built from `Z` agrees almost surely with the one built from the potential. -/
theorem continuumValue_field_transfer {ΩW ΩB : Type*} [MeasurableSpace ΩW]
    [MeasurableSpace ΩB] (d : ℕ) (ν2 : ℝ) (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW)
    (Z : ℝ → Space d → ΩW → ℝ) (T : ℝ) (hT : 0 < T)
    (hZ : ∀ᵐ ω ∂PW, ∀ t ∈ Set.Icc (0:ℝ) T, ∀ z : Space d,
      Z t z ω = gaussianPotential d ν2 W t z ω)
    (B : Space d → ℝ≥0 → ΩB → Space d) (PB : Measure ΩB) (x : Space d) :
    (fun ω => continuumValue d Z B PB T x ω)
      =ᵐ[PW] fun ω => continuumValue d (fun t z ω => gaussianPotential d ν2 W t z ω)
        B PB T x ω := by
  filter_upwards [hZ] with ω hω
  simp only [continuumValue, brownianValue]
  congr 1
  · exact hω T ⟨le_of_lt hT, le_refl T⟩ x
  · exact Sandpile.Support.brownianDiscount_congr d (B x) PB (fun t z => Z t z ω)
      (fun t z => gaussianPotential d ν2 W t z ω) T (fun r hr hrT z => by
        by_cases h : r ∈ Set.Icc (0:ℝ) T
        · exact hω r h z
        · exact absurd ⟨hr, hrT⟩ h)

end Sandpile.Support
