import Mathlib

/-!
# Compact-uniform convergence from sequential convergence

Compactness reduces a uniform large-scale estimate to convergence along
sequences whose parameters have convergent subsequences.
-/

open Filter Topology

namespace Sandpile.External.Stopping

/-- If every diverging scale sequence and every convergent sequence of compact
parameters make an error tend to zero, then the error vanishes uniformly. -/
theorem exists_large_scale_uniform_of_compact_sequences
    {X : Type*} [MetricSpace X] (K : Set X) (hK : IsCompact K)
    (E : ℝ → X → ℝ)
    (hseq : ∀ (R : ℕ → ℝ) (z : ℕ → X) (p : X),
      Tendsto R atTop atTop → (∀ n, z n ∈ K) → Tendsto z atTop (𝓝 p) →
      Tendsto (fun n => E (R n) (z n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ z ∈ K, |E R z| ≤ ε := by
  intro ε hε
  by_contra hn
  push Not at hn
  have hbad (n : ℕ) : ∃ R : ℝ, (n : ℝ) + 1 ≤ R ∧ ∃ z ∈ K, ε < |E R z| :=
    hn ((n : ℝ) + 1) (by positivity)
  choose R hR z hzK hzbad using hbad
  obtain ⟨p, hpK, φ, hφ, hφlim⟩ := hK.tendsto_subseq hzK
  have hRlim : Tendsto R atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    exact Filter.Eventually.of_forall fun n => (le_add_of_nonneg_right (by norm_num)).trans (hR n)
  have hlim := hseq (R ∘ φ) (z ∘ φ) p (hRlim.comp hφ.tendsto_atTop)
    (fun n => hzK (φ n)) hφlim
  have hsmall : ∀ᶠ n in atTop, |E (R (φ n)) (z (φ n))| < ε := by
    have h := hlim.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
    filter_upwards [h] with n hn'
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, Function.comp_apply] using hn'
  obtain ⟨n, hn'⟩ := hsmall.exists
  exact (not_lt_of_ge (hzbad (φ n)).le) hn'

end Sandpile.External.Stopping
