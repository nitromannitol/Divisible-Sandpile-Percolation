import Sandpile.Continuum.Stopping

/-!
# Uniform continuity of clipped rewards

On a compact set of starting points and a bounded horizon, a continuous reward
along a continuous path varies uniformly in time and space over all clipped stops.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Along a continuous path, clipped rewards are uniformly continuous in the
horizon and starting point, uniformly over all stopping times. -/
theorem Sandpile.Support.uniform_clipped_reward_continuity
    {d : ℕ} (T : ℝ≥0) (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hG : ContinuousOn (fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2)
      (Set.Icc 0 (T : ℝ) ×ˢ Set.univ))
    (b : ℝ≥0 → Sandpile.Continuum.Space d) (hb : Continuous b)
    (K : Set (Sandpile.Continuum.Space d)) (hK : IsCompact K) :
    ∀ ε > 0, ∃ δ > 0, ∀ u ≤ T, ∀ v ≤ T, ∀ y ∈ K, ∀ z ∈ K,
      dist u v < δ → dist y z < δ → ∀ s ≤ T,
        |G ((u : ℝ) - min s u) (y + b (min s u)) -
          G ((v : ℝ) - min s v) (z + b (min s v))| < ε := by
  let I := Set.Icc (0 : ℝ≥0) T
  let : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let φ : (I × K) × I → ℝ := fun p =>
    G ((p.1.1.1 : ℝ) - min p.2.1 p.1.1.1) (p.1.2.1 + b (min p.2.1 p.1.1.1))
  have hφ : Continuous φ := by
    change Continuous ((fun p : ℝ × Sandpile.Continuum.Space d => G p.1 p.2) ∘
      fun p : (I × K) × I =>
        ((p.1.1.1 : ℝ) - min p.2.1 p.1.1.1, p.1.2.1 + b (min p.2.1 p.1.1.1)))
    apply hG.comp_continuous
    · fun_prop
    · intro p
      refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
      · exact sub_nonneg.mpr (by exact_mod_cast (min_le_right p.2.1 p.1.1.1))
      · exact (sub_le_self _ (min p.2.1 p.1.1.1).coe_nonneg).trans (by exact_mod_cast p.1.1.2.2)
  intro ε hε
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hφ) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u hu v hv y hy z hz huv hyz s hs
  have hh := hδφ
    (a := ((⟨u, zero_le, hu⟩, ⟨y, hy⟩), ⟨s, zero_le, hs⟩))
    (b := ((⟨v, zero_le, hv⟩, ⟨z, hz⟩), ⟨s, zero_le, hs⟩))
    (by simpa only [Prod.dist_eq, Subtype.dist_eq, dist_self, max_lt_iff, hδ, and_true] using And.intro huv hyz)
  simpa only [Real.dist_eq, φ] using hh
