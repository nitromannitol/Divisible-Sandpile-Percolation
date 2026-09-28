import Sandpile.Support.CrossBasic

/-!
# The two-event crossing argument

The proof of `thm:limiting-odometer-crossing` (`sandpile.tex:2531-2557`), in the form it
takes once the two events it intersects are named.

  "Apply Lemma [finite-scale extraction] with error `ε/2`. This gives `c > 0` and rational
   scales `s_1,…,s_k ∈ (0,1)` such that `P(⋂_j H_{𝓡_j}(4c; max_i 𝒳_{s_i})) ≥ 1 - ε/2`.
   Choose `T` so large that `P(max_i sup_{u ∈ ⋃_j 𝓡_j} |𝒳_{s_i,T}(u) - 𝒳_{s_i}(u)| > c) ≤
   ε/2`. On the intersection of these two events, [the admissibility bound] implies that
   `{u : 𝒰_{Z,1}(T,u) > 5dc}` crosses every prescribed rectangle in its prescribed
   direction."

`F i` is `𝒳_{s_i}`, `G i` is `𝒳_{s_i,T}`, `U` is `𝒰_{Z,1}(T,·)`, `D` is the factor `2d` of
`eq:ball-green-lower-brownian-value` and `H` is the paper's `5dc`, which is below
`3Dc = 6dc`. `ofReal_one_sub_le_inter` is the abstract two-event probability bound,
`crosses_all_of_max_and_approx` is the deterministic core (`sandpile.tex:2549-2556`), and
`crossing_of_extraction_and_approx` assembles the two into the probabilistic statement.
Nothing here is specific to the ball fields: the statement is the paper's two-event
argument, and the two events are supplied by the finite-scale extraction and by the choice
of `T`.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace Sandpile.Support

open Sandpile.Frozen.FixedScaleCrossings

/-- The two-event bound: an event of probability at least `1 - ε/2` meets an
event whose complement has probability at most `ε/2` with probability at least
`1 - ε`.  Neither event need be measurable. -/
theorem ofReal_one_sub_le_inter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {A B : Set Ω} {ε : ℝ} (hε : 0 < ε)
    (hA : ENNReal.ofReal (1 - ε / 2) ≤ P A) (hB : P Bᶜ ≤ ENNReal.ofReal (ε / 2)) :
    ENNReal.ofReal (1 - ε) ≤ P (A ∩ B) := by
  rcases le_or_gt 1 ε with h | h
  · have : (1 : ℝ) - ε ≤ 0 := by linarith
    simp [ENNReal.ofReal_eq_zero.mpr this]
  · have key : ENNReal.ofReal (1 - ε) + ENNReal.ofReal (ε / 2)
        = ENNReal.ofReal (1 - ε / 2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      ring_nf
    have hchain : ENNReal.ofReal (1 - ε) + ENNReal.ofReal (ε / 2)
        ≤ P (A ∩ B) + ENNReal.ofReal (ε / 2) := by
      rw [key]
      exact le_trans hA (le_trans (measure_le_inter_add_compl P A B)
        (add_le_add le_rfl hB))
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain

/-- The deterministic core of `sandpile.tex:2549-2556`: on the intersection of
the crossing event and the uniform-approximation event, the superlevel set of
`U` above `H` crosses every prescribed rectangle. -/
theorem crosses_all_of_max_and_approx {N : ℕ} (a b : Fin N → Fin 2 → ℝ)
    (dir : Fin N → Fin 2) {k : ℕ} [NeZero k] {c D H : ℝ} (hD : 0 < D)
    (hH : H < 3 * D * c)
    (F G : Fin k → Sandpile.Continuum.Space 2 → ℝ)
    (U : Sandpile.Continuum.Space 2 → ℝ)
    (happ : ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2),
      (∃ j, u ∈ rectSet (a j) (b j)) → F i u - c ≤ G i u)
    (hadm : ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2), D * G i u ≤ U u)
    (hcross : ∀ j : Fin N, Crosses (a j) (b j) (dir j)
      {u | 4 * c ≤ ⨆ i : Fin k, F i u}) :
    ∀ j : Fin N, Crosses (a j) (b j) (dir j) {u | H < U u} := by
  intro j
  refine crosses_of_mem_on (fun u hu hmem => ?_) (hcross j)
  have hsup : 4 * c ≤ ⨆ i : Fin k, F i u := hmem
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin k => F i u)
  have hFi : 4 * c ≤ F i u := by rw [hi]; exact hsup
  have hGi : 3 * c ≤ G i u := by
    have := happ i u ⟨j, hu⟩
    linarith
  have hDG : D * (3 * c) ≤ D * G i u := mul_le_mul_of_nonneg_left hGi hD.le
  have hDU := hadm i u
  show H < U u
  nlinarith

/-- `thm:limiting-odometer-crossing` in the form its proof gives: the crossing of
the maximum of the finitely many ball fields at level `4c`, together with a
uniform approximation of those fields by their finite-time payoffs, crosses the
superlevel set of the Brownian stopping value above any `H < 3Dc`. -/
theorem crossing_of_extraction_and_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N : ℕ} (a b : Fin N → Fin 2 → ℝ) (dir : Fin N → Fin 2)
    {k : ℕ} [NeZero k] {c D H ε : ℝ} (hD : 0 < D) (hH : H < 3 * D * c) (hε : 0 < ε)
    (F G : Fin k → Sandpile.Continuum.Space 2 → Ω → ℝ)
    (U : Sandpile.Continuum.Space 2 → Ω → ℝ)
    (hcross : ENNReal.ofReal (1 - ε / 2) ≤ P {ω | ∀ j : Fin N,
      Crosses (a j) (b j) (dir j) {u | 4 * c ≤ ⨆ i : Fin k, F i u ω}})
    (hgood : P {ω | ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2),
        (∃ j, u ∈ rectSet (a j) (b j)) → F i u ω - c ≤ G i u ω}ᶜ
      ≤ ENNReal.ofReal (ε / 2))
    (hadm : ∀ (i : Fin k) (u : Sandpile.Continuum.Space 2) (ω : Ω),
      D * G i u ω ≤ U u ω) :
    ENNReal.ofReal (1 - ε) ≤ P {ω | ∀ j : Fin N,
      Crosses (a j) (b j) (dir j) {u | H < U u ω}} := by
  refine le_trans (ofReal_one_sub_le_inter P hε hcross hgood) (measure_mono ?_)
  rintro ω ⟨hω1, hω2⟩
  exact crosses_all_of_max_and_approx a b dir hD hH (fun i u => F i u ω)
    (fun i u => G i u ω) (fun u => U u ω) hω2 (fun i u => hadm i u ω) hω1

end Sandpile.Support
