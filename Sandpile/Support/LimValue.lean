import Sandpile.Support.LimExtraction
import Sandpile.Support.CrossBrownian
import Sandpile.Continuum.Stopping

/-!
# The localized value and its approximation hypothesis

`thm:limiting-odometer-crossing` (`sandpile.tex:2515-2530`) and the paragraph
that prepares it (`sandpile.tex:2495-2511`).

  "Recall […] that `𝒰_{Z,1}` is the Brownian stopping value from
   `eq:continuum-membrane-stopping-value`, with stopping rules killed on exiting
   the unit ball around the starting point. In `d=3` we identify `u∈ℝ²` with
   `(u,0)`. For `0<s<1` and `T<∞`, let `𝒳_{s,T}(u)` be `(2d)^{-1}` times the
   white-noise average against the expected occupation density of Brownian
   motion, started at `u`, stopped at time `T` or when it exits the ball of
   radius `s` around `u`. This rule is admissible for `𝒰_{Z,1}`, so for every
   `0<s<1` and `T>0`, `2d 𝒳_{s,T}(u) ≤ 𝒰_{Z,1}(T,u)`. As `T→∞`, the fields
   `𝒳_{s,T}` converge to `𝒳_s` uniformly in probability on compact rectangles,
   for each fixed finite set of scales."

and the proof itself:

  "Apply Lemma [finite-scale extraction] with error `ε/2`. This gives `c>0` and
   rational scales `s_1,…,s_k∈(0,1)` such that
   `P(⋂_j H_{𝓡_j}(4c; max_i 𝒳_{s_i})) ≥ 1-ε/2`. Choose `T` so large that
   `P(max_i sup_{u∈⋃_j 𝓡_j} |𝒳_{s_i,T}(u)-𝒳_{s_i}(u)| > c) ≤ ε/2`. On the
   intersection of these two events, `eq:ball-green-lower-brownian-value` implies
   that `{u : 𝒰_{Z,1}(T,u) > 5dc}` crosses every prescribed rectangle in its
   prescribed direction. This proves the theorem with `H=5dc`."

The two facts of the preparatory paragraph are used only through their
combination: off an event of probability at most `δ`, the localized value at `u`
dominates `2d(𝒳_{s_i}(u)-c)` for every prescribed scale and every `u` in the
rectangles. That combination is `LocalizedValueApproximation` below, with the
horizon bound before the spaces, as the theorem's own statement binds it. The
rest of the proof is the two-event argument and the deterministic step, which is
`crossing_of_extraction_and_value`.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The two-event argument of `sandpile.tex:2531-2557` with the lower bound on
the stopping value carried directly, rather than through a separate field. -/
theorem crossing_of_extraction_and_value {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (dir : Fin N → Fin 2)
    {k : ℕ} [NeZero k] {c D H ε : ℝ} (hD : 0 < D) (hH : H < 3 * D * c) (hε : 0 < ε)
    (F : Fin k → Sandpile.Continuum.Space 2 → Ω → ℝ)
    (U : Sandpile.Continuum.Space 2 → Ω → ℝ)
    (hcross : ENNReal.ofReal (1 - ε / 2) ≤ P {ω | ∀ j : Fin N,
      Crosses (a j) (b j) (dir j) {u | 4 * c ≤ ⨆ i : Fin k, F i u ω}})
    (hgood : P {ω | ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2),
        (∃ j, u ∈ rectSet (a j) (b j)) → D * (F i u ω - c) ≤ U u ω}ᶜ
      ≤ ENNReal.ofReal (ε / 2)) :
    ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ j : Fin N,
      Crosses (a j) (b j) (dir j) {u | H < U u ω}} := by
  refine le_trans (ofReal_one_sub_le_inter P hε hcross hgood) (measure_mono ?_)
  rintro ω ⟨hω1, hω2⟩ j
  refine crosses_of_mem_on (fun u hu hmem => ?_) (hω1 j)
  have hsup : 4 * c ≤ ⨆ i : Fin k, F i u ω := hmem
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin k => F i u ω)
  have hFi : 4 * c ≤ F i u ω := by rw [hi]; exact hsup
  have hDU : D * (F i u ω - c) ≤ U u ω := hω2 i u ⟨j, hu⟩
  have hDG : D * (3 * c) ≤ D * (F i u ω - c) :=
    mul_le_mul_of_nonneg_left (by linarith) hD.le
  show H < U u ω
  nlinarith

/-- `𝒰_{Z,1}(T,u)` of `sandpile.tex:2495-2498`, at the plane point `u`, for the
scenery of variance one. -/
noncomputable def localizedValue {ΩW ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ) (PB : Measure ΩB)
    (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d) (T : ℝ)
    (u : Sandpile.Continuum.Space 2) (ω : ΩW) : ℝ :=
  Sandpile.Continuum.brownianValueBall (B (planePoint u)) PB
    (fun t z => Z t z ω) T 1 (planePoint u)

/-- The actual heat potential is the continuous version fixed in
`sandpile.tex:1019-1021`, on each nonnegative finite time interval. -/
def ContinuousHeatPotential {Ω : Type*} [MeasurableSpace Ω] (d : ℕ)
    (Z : ℝ → Sandpile.Continuum.Space d → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
    ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => Z p.1 p.2 ω)
      (Set.Icc 0 T ×ˢ (Set.univ : Set (Sandpile.Continuum.Space d)))

/-- The two facts of `sandpile.tex:2499-2511` in the one form the proof uses
them: the ball-stopped rule is admissible for `𝒰_{Z,1}`, and its payoff is
within `c` of `𝒳_s` on the prescribed rectangles once the horizon is large, so
that off an event of probability at most `δ` the localized value dominates
`2d(𝒳_{s_i}-c)` at every prescribed scale and every point of the rectangles.
The horizon is bound before the spaces, as `thm:limiting-odometer-crossing`
binds it, since the fields have a fixed law. Both fields are their actual
continuous versions. The Brownian paths are continuous and their evaluations
strongly measurable, as needed for the capped exit rule. -/
def LocalizedValueApproximation (d : ℕ) : Prop :=
  ∀ (k : ℕ) (s : Fin k → ℚ), (∀ i, 0 < s i ∧ s i < 1) →
  ∀ (N : ℕ) (a b : Fin N → Fin 2 → ℝ) (c δ : ℝ), 0 < c → 0 < δ →
  ∃ T : ℝ, 0 < T ∧
    ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
      (W : (Sandpile.Continuum.Space d → ℝ) → ΩW → ℝ),
      Sandpile.Continuum.IsWhiteNoise d W PW →
      (∀ s : ℝ, 0 < s → s ≤ 1 → ∀ᵐ ω ∂PW, Continuous fun u => ballField d W s u ω) →
    ∀ (Z : ℝ → Sandpile.Continuum.Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Sandpile.Continuum.Space d),
        Z t x =ᵐ[PW] fun ω => Sandpile.Continuum.gaussianPotential d 1 W t x ω) →
      ContinuousHeatPotential d Z PW →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Sandpile.Continuum.Space d → ℝ≥0 → ΩB → Sandpile.Continuum.Space d),
      (∀ y, Sandpile.Continuum.IsBrownian d y (B y) PB) →
      (∀ y ω, Continuous fun t => B y t ω) →
      (∀ y t, StronglyMeasurable (B y t)) →
    PW {ω | ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2),
        (∃ j, u ∈ rectSet (a j) (b j)) →
        2 * (d : ℝ) * (ballField d W (s i : ℝ) u ω - c) ≤ localizedValue d Z PB B T u ω}ᶜ
      ≤ ENNReal.ofReal δ

end Sandpile.Support
