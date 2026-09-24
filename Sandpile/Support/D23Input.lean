/-
The block-crossing estimate of the dimension-two and dimension-three
percolation proof, `eq:d23-block-crossing-estimate` (`sandpile.tex:2605-2612`):

  "By this domination statement, the deterministic implication above, and
   monotonicity of the odometer, it suffices to prove that `P(E_R) ≥ 1 - δ` for
   all large `R`, uniformly over the laws in the theorem statement."

Here `E_R = 𝓔_R(𝒪_R)` is the event that the localized level set
`𝒪_R = {x : u^{Q(x,R)}_{⌊R²T⌋}(x) > cR^{2-d/2}}` of `sandpile.tex:2600-2604`
contains the prescribed crossings of the rectangles `R·𝓡_j`.  The rectangles are
the four of the block construction, so `E_R` at the coarse site `z` is
`BlockGood R (d23Field d R ⌊R²T⌋ ζ) (cR^{2-d/2}) z`.

`δ` is quantified first, and `c`, `T` and the threshold scale after it, as the
paper's proof orders them: `δ` comes from the dependence range of the block
event through \citet[Corollary~1.4]{LSS}, then
Theorem~\ref{thm:limiting-odometer-crossing} with error `δ/4` gives the time `T`
and the level `H`, and only then is `c = ν₀H/2` fixed.
-/
import Sandpile.Support.D23Range

open MeasureTheory ProbabilityTheory

noncomputable section
namespace Sandpile

/-- The block-crossing estimate `eq:d23-block-crossing-estimate`, uniformly over
the laws of the theorem. -/
def D23BlockCrossing (d : ℕ) (ν₀ θ₀ K₀ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ ∃ R₀ : ℕ, 1 ≤ R₀ ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ R : ℕ, R₀ ≤ R → ∀ z : Site 2,
          LatticeProb.iidLaw d ν
              {ζ : Site d → ℝ | ¬ BlockGood R
                (d23Field d R ⌊(R : ℝ) ^ 2 * T⌋₊ ζ) (c * (R : ℝ) ^ (2 - (d : ℝ) / 2)) z}
            ≤ ENNReal.ofReal δ

end Sandpile
