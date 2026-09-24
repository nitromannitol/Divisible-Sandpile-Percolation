/-
Lemma on the doubled heat kernel in dimension four of sandpile.tex, frozen.
`sandpile.tex:1164-1169` (label `lem:d4-double-heat-kernel`):

  "Uniformly for $t\geq2$ and $x,y\in\Z^4$ with $|x-y|^2\leq t$,
   \[
     \sum_{a,b=0}^{t-1}p_{a+b}(x,y)
     = \frac4{\pi^2}\log\frac{t}{1+|x-y|^2}+O(1)\, .
   \]"

The word "uniformly" is the whole content of the statement, so the `O(1)` is a
single constant bound before `t`, `x` and `y`: the conclusion is
`∃ C, ∀ t ≥ 2, ∀ x y, |x-y|² ≤ t → |… − …| ≤ C`.
The squared Euclidean distance is written as the real number `sqDist x y`
defined below; the paper's `|x-y|^2` never appears except squared, so no square
root is taken.  The double sum is the literal `∑_{a<t} ∑_{b<t} p_{a+b}(x,y)`
over `Finset.range t`, with `Sandpile.heatKernel 4` for `p`.
The summable local limit remainder used by the proof is exposed through
`External.PairedLocalCLTFour`, the dimension-four specialization of the cited
Lawler–Limic Theorem 2.1.3, Eq. (2.8). The qualitative `External.LocalCLT`
input is retained.

The threshold `2 ≤ t` and the constraint `sqDist x y ≤ t` keep the argument of
`Real.log` strictly positive, so the logarithm never takes its junk value at `0`.
-/
import Sandpile.Support.DoubleHeatKernel
import Sandpile.External.LocalCLT

open MeasureTheory ProbabilityTheory Filter Topology

/-- The squared Euclidean distance `|x-y|^2` between two lattice sites, as a
real number. -/
noncomputable def Sandpile.sqDist {d : ℕ} (x y : Sandpile.Site d) : ℝ :=
  ∑ i, ((x i - y i : ℤ) : ℝ) ^ 2

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.d4_double_heat_kernel
    (hLocalCLT : Sandpile.External.LocalCLT)
    (hPaired : Sandpile.External.PairedLocalCLTFour) :
    ∃ C : ℝ, ∀ t : ℕ, 2 ≤ t → ∀ x y : Sandpile.Site 4, Sandpile.sqDist x y ≤ (t : ℝ) →
      |(∑ a ∈ Finset.range t, ∑ b ∈ Finset.range t, Sandpile.heatKernel 4 (a + b) x y) -
          4 / Real.pi ^ 2 * Real.log ((t : ℝ) / (1 + Sandpile.sqDist x y))| ≤ C
-- FROZEN-STATEMENT-END
:= by
  have _hQualitative := hLocalCLT
  simpa only [Sandpile.sqDist] using Sandpile.exists_double_heat_kernel_four_bound hPaired
