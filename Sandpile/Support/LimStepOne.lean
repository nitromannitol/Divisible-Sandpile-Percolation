import Sandpile.Support.CrossFiniteScale
import Sandpile.Support.CrossScale
import Sandpile.Support.CrossExtract

/-!
# Step 1 of finite-scale extraction: the zero-one upgrade

Step 1 of the proof of `lem:finite-scale-extraction` (`sandpile.tex:2431-2484`).

  "We prove that for one rectangle `𝓡` and one crossing direction,
   `P(⋂_{L≥1} ⋂_{j≥1} ⋃_{s∈(0,1/j)∩ℚ} H_𝓡(L b(s); 𝒳_s)) = 1`.
   For every `j,L≥1`, `eq:rescaled-crossing-estimate` gives
   `P(⋃_{s∈(0,1/j)∩ℚ} H_𝓡(L b(s); 𝒳_s)) ≥ p`, with `p>0` independent of `j` and
   `L`. […] We now show that `P(𝓔)=1`. Let `U` be a finite union of unit cubes
   […]. Choose a bounded orthonormal basis `(e_i)` of `L²(U)`. The coordinates
   `𝒲(e_i)` are independent standard Gaussians and determine `𝒲|_U`. We claim
   that `𝓔` belongs to their tail sigma-field […]. Kolmogorov's zero-one law,
   together with `P(𝓔)≥p`, gives `P(𝓔)=1`."

The first half of the display, `P(𝓔) ≥ p`, is proved in this repository:
`Sandpile.Support.union_rational_scales_ge` derives it from
`prop:fixed-scale-crossings` through the rescaled crossing estimate. The second
half, the passage from `P(𝓔) ≥ p` to `P(𝓔) = 1`, is the tail argument quoted
above. It is not the crossing geometry; it is a statement about the white noise
itself, namely that the field on a bounded set is read off countably many
independent Gaussian coordinates and that the event is insensitive to any finite
number of them. `IsWhiteNoise` records the Gaussian character, the mean and the
covariance of the family, and nothing about a basis of `L²(U)`; the argument
needs the basis, the independence of the coordinates, and the realization of the
event on the coordinate space, where Mathlib's Kolmogorov zero-one law
(`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`) applies.

That step is isolated here as `ScaleCrossingAS`, in its almost-sure form: the
paper's `P(𝓔)=1` is an equality of the probability of an event which is
measurable on the coordinate space but is not known to be measurable on an
abstract space carrying the white noise, and for a set that is not measurable
`P(𝓔)=1` does not force the complement to be null. The almost-sure form is what
the rest of the proof uses and is what the paper's argument produces.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings

/-- The event `𝓔` of Step 1 (`sandpile.tex:2437-2447`): for every level
parameter `L ≥ 1` and every bound `1/(m+1)`, some rational scale below that bound
carries a crossing of the rectangle at level `L b(s)`. -/
def ScaleCrossings {Ω : Type*} (d : ℕ) (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (a b : Fin 2 → ℝ) (i : Fin 2) (ω : Ω) : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∀ m : ℕ, ∃ s : ℚ, 0 < s ∧ (s : ℝ) < ((m : ℝ) + 1)⁻¹ ∧
    Crosses a b i {u | L * crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω}

/-- The lower bound of Step 1 (`sandpile.tex:2437-2447`):

  "For every `j,L≥1`, `eq:rescaled-crossing-estimate` gives
   `P(⋃_{s∈(0,1/j)∩ℚ} H_𝓡(L b(s); 𝒳_s)) ≥ p`, with `p>0` independent of `j` and
   `L`: choose a rational `s < min{1/j, s_0}`."

in the form `Sandpile.Support.rescaled_crossing_estimate` proves it from
`prop:fixed-scale-crossings`, for the rectangles `[-al,al]×[0,2h]` in the
left-right direction: not for the union over the small rational scales but for
each of them separately, which is what the rescaled estimate gives and what the
passage to a general rectangle needs. -/
def ScaleCrossingLower {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (P : Measure Ω)
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ) : Prop :=
  ∀ al h : ℝ, 0 < al → 0 < h → ∃ p : ℝ, 0 < p ∧ ∀ L : ℝ, 1 ≤ L →
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℚ, 0 < (s : ℝ) → (s : ℝ) < s₀ →
      ENNReal.ofReal p ≤ P {ω | Crosses ![-al, 0] ![al, 2 * h] 0
        {u | L * crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω}}

/-- The same bound at an arbitrary axis-parallel rectangle and either coordinate
direction, which is where Step 1 applies it. -/
def ScaleCrossingLowerAt {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (P : Measure Ω)
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ) (a b : Fin 2 → ℝ) (i : Fin 2) : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∀ L : ℝ, 1 ≤ L → ∃ s₀ : ℝ, 0 < s₀ ∧
    ∀ s : ℚ, 0 < (s : ℝ) → (s : ℝ) < s₀ →
      ENNReal.ofReal p ≤ P {ω | Crosses a b i
        {u | L * crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω}}

/-- The conclusion of Step 1 of `lem:finite-scale-extraction`
(`sandpile.tex:2431-2484`): the zero-one upgrade.

  "We now show that `P(𝓔)=1`.  Let `U` be a finite union of unit cubes […].
   Choose a bounded orthonormal basis `(e_i)` of `L²(U)`.  The coordinates
   `𝒲(e_i)` are independent standard Gaussians and determine `𝒲|_U`.  We claim
   that `𝓔` belongs to their tail sigma-field […].  Kolmogorov's zero-one law,
   together with `P(𝓔)≥p`, gives `P(𝓔)=1`."

Everything else in Step 1 is proved in this repository: the lower bound at the
centred rectangles is `scaleCrossingLower_of_fixed_scale`, and its passage to an
arbitrary rectangle and direction is `scaleCrossingLowerAt_of_lower`, by the
symmetry in law of the ball field.  What is left, and what is assumed here, is
exactly the passage from a positive probability to probability one. -/
def ScaleCrossingAS (d : ℕ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ),
    Sandpile.Continuum.IsWhiteNoise d W P →
    (∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω) →
  ∀ (a b : Fin 2 → ℝ), (∀ k : Fin 2, a k < b k) → ∀ i : Fin 2,
    ScaleCrossingLowerAt d P W a b i → ∀ᵐ ω ∂P, ScaleCrossings d W a b i ω

/-- Step 1 applied to the whole prescribed list of rectangles, in the form the
continuity from below of Step 2 consumes: almost surely every rectangle carries a
crossing at some rational scale in `(0,1)` at the level `b(s)`. -/
theorem ae_exists_scale_crossing_all {d : ℕ} (hZ : ScaleCrossingAS d)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (Sandpile.Continuum.Space d → ℝ) → Ω → ℝ)
    (hW : Sandpile.Continuum.IsWhiteNoise d W P)
    (hcont : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ᵐ ω ∂P, Continuous fun u => ballField d W t u ω)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (hab : ∀ (j : Fin N) (i : Fin 2), a j i < b j i)
    (dir : Fin N → Fin 2)
    (hlow : ∀ j : Fin N, ScaleCrossingLowerAt d P W (a j) (b j) (dir j)) :
    ∀ᵐ ω ∂P, ∀ j : Fin N, ∃ s : ℚ, 0 < s ∧ s < 1 ∧
      Crosses (a j) (b j) (dir j)
        {u | crossScale d (s : ℝ) ≤ ballField d W (s : ℝ) u ω} := by
  have hall : ∀ᵐ ω ∂P, ∀ j : Fin N, ScaleCrossings d W (a j) (b j) (dir j) ω :=
    ae_all_iff.mpr fun j => hZ Ω P W hW hcont (a j) (b j) (hab j) (dir j) (hlow j)
  filter_upwards [hall] with ω hω j
  obtain ⟨s, hs0, hs1, hcr⟩ := hω j 1 le_rfl 0
  refine ⟨s, hs0, ?_, ?_⟩
  · have : (s : ℝ) < 1 := by simpa using hs1
    exact_mod_cast this
  · simpa using hcr

end Sandpile.Support
