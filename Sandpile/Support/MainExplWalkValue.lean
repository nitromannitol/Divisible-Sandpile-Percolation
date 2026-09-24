/-
Attainable values of the unkilled walk at a bounded horizon.

The optimal-stopping value `stoppingSup n x F` is a supremum over walk stopping
times bounded by `n`, so the junk value of an unbounded supremum is excluded as
soon as the set of attainable payoffs is bounded above.  For a reward that reads
the walk only through its position at the stopping time, the bound is free: the
walk run for `n` steps stays in the lattice box of radius `n` about its start, so
the payoff is at most the sum of the finitely many values of the reward on that
box.  This is the unkilled analogue of `Sandpile.bddAbove_killedSet_stopped_value`
and it is what makes the two suprema of the four-term bound of
`sandpile.tex:1881-1890` legitimate at rewards with no global bound.
-/
import Sandpile.Support.StoppedOdometer
import Sandpile.Support.ExplStability

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **The attainable payoffs of the unkilled walk at a bounded horizon are bounded above**,
for every reward that reads the walk through its position at the stopping time. -/
theorem bddAbove_walk_stopped_value (hd : 1 ≤ d) (x : Site d) (n : ℕ) (F : ℕ → Site d → ℝ) :
    BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) (X (τ X)) ∂(walkLaw d x)} := by
  letI : NeZero d := ⟨by omega⟩
  letI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  let M : ℝ := ∑ j ∈ Finset.range (n + 1), ∑ z ∈ boxFinset x n, |F j z|
  refine ⟨M, ?_⟩
  rintro a ⟨τ, hτ, ht, rfl⟩
  have hb : ∀ᵐ X ∂(walkLaw d x), F (τ X) (X (τ X)) ≤ M := by
    filter_upwards [ae_boxDist_walk hd x] with X hX
    have ha : |F (τ X) (X (τ X))| ≤ ∑ z ∈ boxFinset x n, |F (τ X) z| :=
      Finset.single_le_sum (f := fun z => |F (τ X) z|) (fun _ _ => abs_nonneg _)
        (mem_boxFinset ((hX _).trans (ht X)))
    have hb : (∑ z ∈ boxFinset x n, |F (τ X) z|) ≤ M :=
      Finset.single_le_sum (f := fun j => ∑ z ∈ boxFinset x n, |F j z|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (ht X)))
    exact (le_abs_self _).trans (ha.trans hb)
  have he := integral_mono_ae (integrable_stopped_value hd x n F hτ ht)
    (integrable_const M) hb
  simpa using he

/-- **The optimal-stopping value sees the reward only up to the horizon.**  Two rewards that
agree at every step at most `n` have the same value, because every admissible stopping time is
bounded by `n`.  This is what lets the exact identity of `sandpile.tex:1881-1890`, whose reward
is written with the ELAPSED time, be read as the reward of the stability input, which is
written with the REMAINING time: the two agree exactly where the value looks. -/
theorem stoppingSup_congr_of_le (n : ℕ) (x : Site d) (F G : ℕ → (ℕ → Site d) → ℝ)
    (h : ∀ k, k ≤ n → ∀ X : ℕ → Site d, F k X = G k X) :
    stoppingSup n x F = stoppingSup n x G := by
  have hset : {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) X ∂(walkLaw d x)} =
      {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, G (τ X) X ∂(walkLaw d x)} := by
    ext a
    constructor
    · rintro ⟨τ, hτ, hτn, rfl⟩
      exact ⟨τ, hτ, hτn,
        integral_congr_ae (Filter.Eventually.of_forall fun X => h (τ X) (hτn X) X)⟩
    · rintro ⟨τ, hτ, hτn, rfl⟩
      exact ⟨τ, hτ, hτn,
        integral_congr_ae (Filter.Eventually.of_forall fun X => (h (τ X) (hτn X) X).symm)⟩
  simp only [stoppingSup, hset]


end Sandpile
