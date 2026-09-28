import Sandpile.Continuum.Kernel
import LatticeProb.Prob.L2JointVersion
import Mathlib

/-!
# White noise and the Gaussian point field

White noise on `ℝ^d` and the point field `Z` of `sandpile.tex`, `ssec:continuum-membrane-fields`
(lines 954-1069): "Let `𝒲` be white noise on `ℝ^d`, that is, the mean-zero Gaussian linear
functional on `L²(ℝ^d)` with covariance `Cov(𝒲(f), 𝒲(g)) = ∫ f g`."

Mathlib 4.32 has Gaussian processes (`ProbabilityTheory.IsGaussianProcess`) but no construction
of white noise and no Kolmogorov extension theorem, so white noise is a PREDICATE `IsWhiteNoise`
on a family `W` of random variables indexed by test functions on a probability space, exactly
transcribing the four properties the paper asks of it: Gaussian finite-dimensional laws, mean
zero, the `L²` covariance, and linearity in the test function. Joint versions along strongly
measurable `L²` families are also recorded (`IsWhiteNoise.jointMeas_univ`); the covariance
identity proves that this clause is satisfied by the same construction. Every statement that
mentions white noise is universally quantified over a space carrying such a family.

The point field `"Z(t,x) = √Var(ζ(0)) 𝒲(g_t^{BM}(x,·))"` (`eq:dlt4-linear-gaussian-potential`) is
`gaussianPotential`. It is a genuine point field only for `d ≤ 3`, where `g_t^{BM}(x,·) ∈
L²(ℝ^d)`; the definition itself does not need that.
-/

open MeasureTheory ProbabilityTheory

namespace Sandpile.Continuum

universe u

/-- `W` is white noise on `ℝ^d` under `P`: a mean-zero Gaussian family indexed by
square-integrable functions, linear in the index, with covariance the `L²` inner
product. -/
structure IsWhiteNoise {Ω : Type u} [MeasurableSpace Ω] (d : ℕ)
    (W : (Space d → ℝ) → Ω → ℝ) (P : Measure Ω) : Prop where
  /-- The finite-dimensional laws are Gaussian. -/
  gaussian : IsGaussianProcess W P
  /-- Each `W f` is measurable. -/
  meas : ∀ f : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) → Measurable (W f)
  /-- Each `W f` is centred. -/
  mean : ∀ f : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) →
    ∫ ω, W f ω ∂P = 0
  /-- The covariance is the `L²` inner product. -/
  cov : ∀ f g : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) →
    MemLp g 2 (volume : Measure (Space d)) →
    ∫ ω, W f ω * W g ω ∂P = ∫ y : Space d, f y * g y
  /-- Additivity in the index. -/
  add : ∀ f g : Space d → ℝ, MemLp f 2 (volume : Measure (Space d)) →
    MemLp g 2 (volume : Measure (Space d)) →
    W (f + g) =ᵐ[P] fun ω => W f ω + W g ω
  /-- Homogeneity in the index. -/
  smul : ∀ (a : ℝ) (f : Space d → ℝ), MemLp f 2 (volume : Measure (Space d)) →
    W (a • f) =ᵐ[P] fun ω => a * W f ω
  /-- Along each strongly measurable spatial L2 family there is a jointly measurable
  version, equal to the specified coordinate almost surely at every parameter. -/
  jointMeas : ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [SigmaFinite μ]
      (f : U → Space d → ℝ) (hf : ∀ u, MemLp (f u) 2 volume),
      StronglyMeasurable (fun u => (hf u).toLp (f u)) →
      ∃ g : U → Ω → ℝ, StronglyMeasurable (Function.uncurry g) ∧
        ∀ u, g u =ᵐ[P] W (f u)

/-- Joint versions along parameter spaces in an arbitrary universe. -/
theorem IsWhiteNoise.jointMeas_univ {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (μ : Measure U) [SigmaFinite μ]
    (f : U → Space d → ℝ) (hf : ∀ u, MemLp (f u) 2 volume)
    (hs : StronglyMeasurable (fun u => (hf u).toLp (f u))) :
    ∃ g : U → Ω → ℝ, StronglyMeasurable (Function.uncurry g) ∧
      ∀ u, g u =ᵐ[P] W (f u) := by
  exact LatticeProb.exists_joint_version_of_covariance volume P W
    (fun q => (hW.gaussian.hasGaussianLaw_eval q).memLp_two) hW.cov f hf hs

/-- The point field `Z(t,x) = √Var(ζ(0)) 𝒲(g_t^{BM}(x,·))`. -/
noncomputable def gaussianPotential {Ω : Type*} (d : ℕ) (ν2 : ℝ)
    (W : (Space d → ℝ) → Ω → ℝ) (t : ℝ) (x : Space d) (ω : Ω) : ℝ :=
  Real.sqrt ν2 * W (fun y => greenTimeBM d t x y) ω

end Sandpile.Continuum
