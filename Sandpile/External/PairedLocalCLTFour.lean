/-
External input from Lawler–Limic, Random Walk: A Modern Introduction,
Theorem 2.1.3, Eq. (2.8), cited in `sandpile.tex:1145-1161` and used in
`sandpile.tex:1171-1172` to prove `lem:d4-double-heat-kernel`.

The paired estimate controls the error by `C n⁻³` in dimension four,
uniformly over the displacement. It is the `k = 4` specialization of the
cited estimate: its polynomial times Gaussian factor is bounded uniformly,
as is `n⁻¹ᐟ²` for `n ≥ 1`. The covariance of one step is `I/4`, so twice
the Gaussian density is `8/(π² n²) exp(-2 |x-y|²/n)`. Pairing the two
successive times includes the parity factor without restricting the sites.

The qualitative `External.LocalCLT` limit alone does not state this
summable remainder. The constant is bound before time and both sites.
The squared Euclidean distance is written as its coordinate sum, and all
denominators are nonzero because `1 ≤ n`.
-/
import Sandpile.Support.Kernel

/-- The dimension-four specialization of the paired local limit estimate,
Lawler–Limic Theorem 2.1.3, Eq. (2.8). Assumed, not proved. -/
def Sandpile.External.PairedLocalCLTFour : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site 4,
    |Sandpile.heatKernel 4 n x y + Sandpile.heatKernel 4 (n + 1) x y -
      8 / (Real.pi ^ 2 * (n : ℝ) ^ 2) *
        Real.exp (-2 * (∑ i : Fin 4, ((x i - y i : ℤ) : ℝ) ^ 2) / n)| ≤
      C / (n : ℝ) ^ 3
