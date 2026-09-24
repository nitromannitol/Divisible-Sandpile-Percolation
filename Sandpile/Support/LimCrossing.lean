/-
`thm:limiting-odometer-crossing` (`sandpile.tex:2515-2530`) assembled.

  "Apply Lemma [finite-scale extraction] with error `ε/2`.  This gives `c>0` and
   rational scales `s_1,…,s_k∈(0,1)` such that
   `P(⋂_j H_{𝓡_j}(4c; max_i 𝒳_{s_i})) ≥ 1-ε/2`.  Choose `T` so large that
   `P(max_i sup_{u∈⋃_j 𝓡_j} |𝒳_{s_i,T}(u)-𝒳_{s_i}(u)| > c) ≤ ε/2`.  On the
   intersection of these two events, `eq:ball-green-lower-brownian-value` implies
   that `{u : 𝒰_{Z,1}(T,u) > 5dc}` crosses every prescribed rectangle in its
   prescribed direction.  This proves the theorem with `H=5dc`."

The constants are the paper's: `D = 2d` is the factor of
`eq:ball-green-lower-brownian-value`, the level of the extraction is `4c`, the
approximation costs `c`, so the value is above `2d·3c = 6dc` and the theorem's
`H = 5dc` is below it.  The horizon `T` and the level `H` are bound before the
two spaces, as the theorem binds them.

Both the ball fields and the heat potential in the stopping value are their
actual continuous versions. The motion has continuous paths and strongly
measurable evaluations, so the capped ball-exit rule can be used.
-/
import Sandpile.Support.LimValue

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- `thm:limiting-odometer-crossing` from the finite-scale extraction and the
admissible ball-stopped rule. -/
theorem limiting_odometer_crossing_of_inputs
    (hRSWc : Sandpile.External.ContinuumRSW)
    (hPitt : Sandpile.External.PittGaussianFKG)
    (hGauss : Sandpile.External.GaussianLawDeterminedByCovariance)
    {d : ℕ} (hd : d = 2 ∨ d = 3)
    (hZ : ScaleCrossingAS d) (hLaw : MaxBallFieldLaw d)
    (hApp : LocalizedValueApproximation d)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ)
    (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i) (dir : Fin N → Fin 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T H : ℝ, 0 < T ∧ 0 < H ∧
      ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
        Sandpile.Continuum.IsWhiteNoise d W PW →
        (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂PW, Continuous fun u => ballField d W t u ω) →
      ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
          Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
        ContinuousHeatPotential d Z PW →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
        (∀ y, Sandpile.Continuum.IsBrownian d y (B y) PB) →
        (∀ y ω, Continuous fun t => B y t ω) →
        (∀ y t, StronglyMeasurable (B y t)) →
      ENNReal.ofReal (1 - ε) ≤ PW {ω | ∀ j : Fin N,
        Crosses (a j) (b j) (dir j) {u | H < localizedValue d Z PB B T u ω}} := by
  obtain ⟨c, k, s, hc, hk, hs, hext⟩ :=
    finite_scale_extraction_of_inputs hRSWc hPitt hGauss hd hZ hLaw a b hab dir (ε / 2) (by linarith)
  obtain ⟨T, hT, happ⟩ := hApp k s hs N a b c (ε / 2) hc (by linarith)
  haveI : NeZero k := ⟨by omega⟩
  have hdpos : (2 : ℝ) ≤ (d : ℝ) := by
    rcases hd with rfl | rfl <;> norm_num
  refine ⟨T, 5 * (d : ℝ) * c, hT, by nlinarith, ?_⟩
  intro ΩW _ PW _ W hW hcont Z hmod hpot ΩB _ PB _ B hB hBcont hBmeas
  exact crossing_of_extraction_and_value PW a b dir (D := 2 * (d : ℝ)) (c := c)
    (H := 5 * (d : ℝ) * c) (by nlinarith) (by nlinarith) hε
    (fun i u ω => ballField d W (s i : ℝ) u ω)
    (fun u ω => localizedValue d Z PB B T u ω)
    (hext ΩW PW W hW hcont) (happ ΩW PW W hW hcont Z hmod hpot ΩB PB B hB hBcont hBmeas)

end Sandpile.Support
