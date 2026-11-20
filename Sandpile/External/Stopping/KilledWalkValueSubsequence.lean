import Sandpile.External.Stopping.KilledWalkStoppingRewardSubsequence

/-!
# Subsequential upper bounds for killed walk values

Near-optimal killed stopping rules yield subsequential upper bounds on their
lattice values in terms of the limiting Brownian cube value.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Along a subsequence, killed lattice values are within any positive error
of the Brownian cube stopping value of the limiting path law. -/
theorem exists_killed_walk_value_subsequence {d : ℕ} [NeZero d]
    {ι : Type*} [Countable ι]
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop)
    (q : ℕ → Site d) (H : ℕ → ℝ≥0) (T c : ℝ≥0) (hc : 0 < c)
    (hH : Tendsto H atTop (𝓝 T)) (hHc : ∀ n, H n ≤ c)
    (ν : ProbabilityMeasure C(ℝ≥0, Continuum.Space d))
    (hpath : Tendsto (fun n => diffusiveWalkPathLaw d (R n) (q n)) atTop (𝓝 ν))
    (a : Continuum.Space d)
    (hstart : Tendsto (fun n => Lclt.scaledSite (R n) (q n)) atTop (𝓝 a))
    (hB : Continuum.IsBrownian d a (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
      (ν : Measure C(ℝ≥0, Continuum.Space d)))
    (time : ι → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b → ∃ i, a < time i ∧ time i < b)
    (G : ℝ → Continuum.Space d → ℝ)
    (hGc : Continuous (fun p : ℝ × Continuum.Space d => G p.1 p.2))
    (M : ℝ) (hG : ∀ s z, |G s z| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᶠ n in atTop,
      killedStoppingSup (supBox (q (φ n)) (R (φ n)))
          ⌊R (φ n) ^ 2 * (H (φ n) : ℝ)⌋₊ (q (φ n)) (fun k X =>
            G (((⌊R (φ n) ^ 2 * (H (φ n) : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R (φ n) ^ 2)
              (Lclt.scaledSite (R (φ n)) (X k))) <
        Continuum.brownianDiscountCube (fun t (f : C(ℝ≥0, Continuum.Space d)) => f t)
          (ν : Measure C(ℝ≥0, Continuum.Space d)) (fun s z => -G s z) T 1 a + ε := by
  classical
  let F (n : ℕ) (k : ℕ) (X : ℕ → Site d) :=
    G (((⌊R n ^ 2 * (H n : ℝ)⌋₊ : ℕ) - (k : ℝ)) / R n ^ 2)
      (Lclt.scaledSite (R n) (X k))
  have hnear (n : ℕ) : ∃ τ : (ℕ → Site d) → ℕ,
      IsWalkStopping τ ∧ (∀ X, τ X ≤ ⌊R n ^ 2 * (H n : ℝ)⌋₊) ∧
      (∀ X j, j < τ X → X j ∈ supBox (q n) (R n)) ∧
      killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (H n : ℝ)⌋₊ (q n) (F n) - ε / 2 <
        ∫ X, F n (τ X) X ∂(walkLaw d (q n)) := by
    have hv : killedStoppingSup (supBox (q n) (R n)) ⌊R n ^ 2 * (H n : ℝ)⌋₊ (q n) (F n) - ε / 2 <
        sSup (killedSet (supBox (q n) (R n)) ⌊R n ^ 2 * (H n : ℝ)⌋₊ (q n) (F n)) := by
      rw [killedStoppingSup_eq_sSup]
      linarith
    obtain ⟨v, ⟨τ, hτ, hτH, hkill, rfl⟩, hv⟩ :=
      exists_lt_of_lt_csSup (killedSet_nonempty _ _ _ _) hv
    exact ⟨τ, hτ, hτH, hkill, hv⟩
  choose τ hτ hτH hkill hnear using hnear
  obtain ⟨φ, L, hφ, hlim, hbound⟩ :=
    exists_killed_walk_stopping_reward_subsequence R hRpos hR q H T c hc hH hHc
      τ hτ hτH hkill ν hpath a hstart hB time hdense G hGc M hG
  refine ⟨φ, hφ, ?_⟩
  have hclose := hlim.eventually (Iio_mem_nhds (show L < L + ε / 2 by linarith))
  filter_upwards [hclose] with n hn
  have hn' := hnear (φ n)
  dsimp only [F] at hn'
  linarith

end Sandpile.External.Stopping
