/-
The Bolzano-Weierstrass step of the dimension-two and dimension-three percolation
proof (`sandpile.tex:2616-2620`):

  "The exponential-moment bound gives a uniform upper bound on
   `Var(ζ^{(n)}(0))`, so along a further subsequence
   `Var(ζ^{(n)}(0)) → ν²`, `ν ≥ ν₀`."

`Sandpile/Support/D23Sequential.lean` supplies the uniform upper bound
`evariance_le_of_exp_moment`; this module supplies the extraction of the
subsequence and the lower bound on the limit, which is what the crossing theorem
is then applied at.
-/
import Sandpile.Support.D23Sequential

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace Sandpile

/-- A sequence of variances confined to a compact interval has a subsequence
converging to a limit inside that interval. -/
theorem exists_subseq_tendsto_variance {a b : ℝ} (_hab : a ≤ b) (v : ℕ → ℝ)
    (hlo : ∀ n, a ≤ v n) (hhi : ∀ n, v n ≤ b) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : ℝ, a ≤ L ∧ L ≤ b ∧
      Tendsto (fun n => v (φ n)) atTop (𝓝 L) := by
  have hmem : ∀ n, v n ∈ Set.Icc a b := fun n => ⟨hlo n, hhi n⟩
  obtain ⟨L, hL, φ, hφ, htend⟩ :=
    IsCompact.tendsto_subseq (isCompact_Icc (a := a) (b := b)) hmem
  exact ⟨φ, hφ, L, hL.1, hL.2, htend⟩

end Sandpile
