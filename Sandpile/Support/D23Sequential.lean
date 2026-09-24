/-
The contradiction step of the dimension-two and dimension-three percolation proof
(`sandpile.tex:2613-2620`):

  "We argue by contradiction.  If `eq:d23-block-crossing-estimate` failed, then there
   would be `R_n → ∞` and mean-zero i.i.d. fields `ζ^{(n)}` satisfying the same variance
   and exponential-moment bounds such that the corresponding events `E_{R_n}` have
   probability at most `1 - δ`.  The exponential-moment bound gives a uniform upper bound
   on `Var(ζ^{(n)}(0))`."

Both halves are here: the uniform variance bound from the exponential moment, and the
reduction of the uniform block-crossing estimate to the absence of such a sequence.
-/
import Sandpile.Support.D23Input
import Sandpile.Support.ExponentialMoments

open LatticeProb

open MeasureTheory ProbabilityTheory Filter

noncomputable section
namespace Sandpile

/-- The exponential-moment bound gives a uniform upper bound on the variance. -/
theorem evariance_le_of_exp_moment {ν : Measure ℝ} [IsProbabilityMeasure ν] {θ K : ℝ}
    (hθ : 0 < θ) (hmean : ∫ z, z ∂ν = 0)
    (hexp : Integrable (fun x : ℝ => Real.exp (θ * |x|)) ν)
    (hK : (∫ x : ℝ, Real.exp (θ * |x|) ∂ν) ≤ K) :
    evariance id ν ≤ ENNReal.ofReal ((4 / θ ^ 2) * K) := by
  have hint : Integrable (fun x : ℝ => x ^ 2) ν := integrable_sq_of_exp hθ hexp
  have hsq : (∫ x : ℝ, x ^ 2 ∂ν) ≤ (4 / θ ^ 2) * K := integral_sq_le_of_exp hθ hexp hK
  have hlint : evariance id ν = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂ν := by
    rw [evariance_eq_lintegral_ofReal]
    simp only [id_eq] at hmean ⊢
    refine lintegral_congr fun x => ?_
    rw [hmean]
    simp
  have hofReal : ENNReal.ofReal (∫ x : ℝ, x ^ 2 ∂ν) = ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg x)
  rw [hlint, ← hofReal]
  exact ENNReal.ofReal_le_ofReal hsq

/-- The block-crossing estimate follows from the absence of a sequence of counterexamples
along scales tending to infinity, which is the form the coupling of
`rem:dlt4-killed-scaling` is stated in: a sequence of laws with a common exponential-moment
bound, hence with variances in a fixed compact interval. -/
theorem d23BlockCrossing_of_sequential (d : ℕ) (ν₀ θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hseq : ∀ δ : ℝ, 0 < δ → ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ (Rs : ℕ → ℕ) (laws : ℕ → Measure ℝ) (zs : ℕ → Site 2),
        (∀ n, n + 1 ≤ Rs n) →
        (∀ n, IsProbabilityMeasure (laws n)) →
        (∀ n, ∫ z, z ∂(laws n) = 0) →
        (∀ n, ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id (laws n)) →
        (∀ n, evariance id (laws n) ≤ ENNReal.ofReal ((4 / θ₀ ^ 2) * K₀)) →
        (∀ n, Integrable (fun z => Real.exp (θ₀ * |z|)) (laws n)) →
        (∀ n, ∫ z, Real.exp (θ₀ * |z|) ∂(laws n) ≤ K₀) →
        ¬ (∀ n, ENNReal.ofReal δ < LatticeProb.iidLaw d (laws n)
              {ζ : Site d → ℝ | ¬ BlockGood (Rs n)
                (d23Field d (Rs n) ⌊((Rs n : ℝ)) ^ 2 * T⌋₊ ζ)
                (c * ((Rs n : ℝ)) ^ (2 - (d : ℝ) / 2)) (zs n)})) :
    D23BlockCrossing d ν₀ θ₀ K₀ := by
  intro δ hδ
  obtain ⟨c, T, hc, hT, hno⟩ := hseq δ hδ
  refine ⟨c, T, hc, hT, ?_⟩
  by_contra hcon
  push Not at hcon
  choose laws hprob hmean hvar hint hexp Rs hRs zs hzs using
    fun n : ℕ => hcon (n + 1) (by omega)
  refine hno Rs laws zs hRs hprob hmean hvar (fun n => ?_) hint hexp hzs
  haveI := hprob n
  exact evariance_le_of_exp_moment hθ₀ (hmean n) (hint n) (hexp n)

end Sandpile
