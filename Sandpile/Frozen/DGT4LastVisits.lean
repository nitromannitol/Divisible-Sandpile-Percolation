import Sandpile.Walk
import Sandpile.Support.LinLastVisit

/-!
# Weighted last-visits lemma

Lemma of sandpile.tex, frozen.  `sandpile.tex:4831-4847`
(label `lem:dgt4-weighted-last-visits`):

  "Let $X$ be simple random walk started at the origin.  For integers
   $0\leq i\leq j$, let
     $I_{i,j}(X)\coloneqq\one_{\{X_i\ne X_r\text{ for every }r\text{ with }i<r\leq j\}}$.
   Then, for every $\varepsilon\in(0,1)$, as $n\to\infty$,
     $\max_{0\leq j\leq\lfloor(1-\varepsilon)n\rfloor}
      \mathbf E_0\left|G(0,0)\sum_{i=0}^j\frac{I_{i,j}(X)}{n-i}
      +\log\left(1-\frac jn\right)\right|\longrightarrow0$."

Modelling decisions.

`E_0` is expectation for simple random walk started at the origin, so it is an
integral over path space against `Sandpile.walkLaw d 0`; `X` is the integration
variable.  `I_{i,j}` is `lastVisitIndicator` below, real valued so that it can
be summed and integrated.

The maximum over `0 ≤ j ≤ ⌊(1-ε)n⌋` is not written as a supremum: a `sSup` or a
`Finset.sup'` over a range would carry a junk value, so the convergence of the
maximum to zero is unfolded into its definition, "for every `η > 0` and all
large `n`, every `j` in the range has integral at most `η`".  This is exactly
`max → 0` for a nonnegative quantity, with no junk value anywhere, and it keeps
the paper's quantifier order: `ε` is fixed first, then the limit in `n`.

The two junk hazards inside the integrand are avoided by the range of `j`: for
`j ≤ ⌊(1-ε)n⌋` one has `1 - j/n ≥ ε > 0`, so `Real.log` is not evaluated at a
nonpositive argument, and `i ≤ j < n`, so `n - i` is a positive real (the
subtraction is in `ℝ`, not truncated).  The sum `∑_{i=0}^j` is over
`Finset.range (j+1)`.

`G(0,0)` is `Sandpile.green d 0 0`, the genuine Green function because `d ≥ 5`;
the paper's subsection fixes `d ≥ 5` throughout.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Frozen.DGT4LastVisits

/-- The last-visit indicator of `sandpile.tex:4757-4761`: "For integers
$0\leq i\leq j$, let
$I_{i,j}(X)\coloneqq\one_{\{X_i\ne X_r\text{ for every }r\text{ with }i<r\leq j\}}$." -/
noncomputable def lastVisitIndicator {d : ℕ} (i j : ℕ) (X : ℕ → Sandpile.Site d) : ℝ :=
  Set.indicator {Y : ℕ → Sandpile.Site d | ∀ r : ℕ, i < r → r ≤ j → Y i ≠ Y r} (fun _ => 1) X

/-- The paper's `I_{i,j}` is the indicator that the walk, read relative to its
position at time `i`, avoids its starting point during its next `j - i` steps. -/
theorem lastVisitIndicator_eq_visitInd {d : ℕ} (i j : ℕ) (X : ℕ → Sandpile.Site d) :
    lastVisitIndicator i j X = Sandpile.visitInd i (j - i) X := by
  have hiff : (X ∈ {Y : ℕ → Sandpile.Site d | ∀ r : ℕ, i < r → r ≤ j → Y i ≠ Y r})
      ↔ Sandpile.relPath i X ∈ Sandpile.noRet d (j - i) := by
    simp only [Set.mem_setOf_eq, Sandpile.noRet, Sandpile.relPath, Nat.add_zero, sub_self]
    constructor
    · intro h s hs1 hs2
      have hij : i ≤ j := by
        by_contra hc
        have : j - i = 0 := by omega
        omega
      have hr : i < i + s := by omega
      have hr2 : i + s ≤ j := by omega
      exact fun hc => h (i + s) hr hr2 (by
        have hz : X (i + s) - X i = 0 := hc
        exact (sub_eq_zero.mp hz).symm)
    · intro h r hr1 hr2 hc
      have hs1 : 1 ≤ r - i := by omega
      have hs2 : r - i ≤ j - i := by omega
      have hkey := h (r - i) hs1 hs2
      apply hkey
      have hri : i + (r - i) = r := by omega
      rw [hri, ← hc, sub_self]
  simp only [lastVisitIndicator, Sandpile.visitInd]
  by_cases h : X ∈ {Y : ℕ → Sandpile.Site d | ∀ r : ℕ, i < r → r ≤ j → Y i ≠ Y r}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hiff.mpr hc))]

/-- The paper's weighted last-visit sum is `Sandpile.lvSum`. -/
theorem sum_lastVisitIndicator_eq {d : ℕ} (n j : ℕ) (X : ℕ → Sandpile.Site d) :
    (∑ i ∈ Finset.range (j + 1), lastVisitIndicator i j X / ((n : ℝ) - (i : ℝ)))
      = Sandpile.lvSum n j X := by
  simp only [Sandpile.lvSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lastVisitIndicator_eq_visitInd, Sandpile.wcoef, mul_one_div]

end Sandpile.Frozen.DGT4LastVisits

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_last_visits
    (d : ℕ) (hd : 5 ≤ d) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, j ≤ ⌊(1 - ε) * (n : ℝ)⌋₊ →
      ∫ X, |Sandpile.green d 0 0 *
            (∑ i ∈ Finset.range (j + 1),
              Sandpile.Frozen.DGT4LastVisits.lastVisitIndicator i j X / ((n : ℝ) - i)) +
          Real.log (1 - (j : ℝ) / (n : ℝ))| ∂(Sandpile.walkLaw d 0) ≤ η
-- FROZEN-STATEMENT-END
:= by
  haveI : NeZero d := ⟨by omega⟩
  have hd3 : 3 ≤ d := by omega
  filter_upwards [Sandpile.lastVisit_eventually (d := d) hd3 hε.1 hε.2 hη] with n hn
  intro j hj
  have hkey := hn j hj
  have hcongr : ∀ X : ℕ → Sandpile.Site d,
      |Sandpile.green d 0 0 *
          (∑ i ∈ Finset.range (j + 1),
            Sandpile.Frozen.DGT4LastVisits.lastVisitIndicator i j X / ((n : ℝ) - (i : ℝ))) +
          Real.log (1 - (j : ℝ) / (n : ℝ))|
        = |Sandpile.green d 0 0 * Sandpile.lvSum n j X +
            Real.log (1 - (j : ℝ) / (n : ℝ))| := fun X => by
    rw [Sandpile.Frozen.DGT4LastVisits.sum_lastVisitIndicator_eq]
  rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  exact hkey
