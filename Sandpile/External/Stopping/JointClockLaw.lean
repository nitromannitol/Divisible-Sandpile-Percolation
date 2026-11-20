import Sandpile.External.Stopping.JointClockCompactness

/-!
# Joint laws of paths and bounded clocks

Weakly converging path laws and compact-valued random clocks admit convergent
joint-law subsequences, and bounded continuous joint rewards converge along
each such subsequence. This is the compactness step in the randomized stopping
argument of Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace Sandpile.External.Stopping

/-- A sequence of measurable paths and compact-valued clocks admits a joint
weak limit with the same path marginal as the limiting path law. -/
theorem exists_subseq_path_clock_law
    {Ω E T : Type*} [MeasurableSpace Ω] [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace T] [SecondCountableTopology T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T]
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (X : ℕ → Ω → E) (τ : ℕ → Ω → T)
    (hX : ∀ n, Measurable (X n)) (hτ : ∀ n, Measurable (τ n))
    (ν : ProbabilityMeasure E)
    (hlim : Tendsto (β := ProbabilityMeasure E) (fun n => (⟨(P n).map (X n),
      (Measure.isProbabilityMeasure_map_iff (hX n).aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure E)) atTop (𝓝 ν)) :
    ∃ (φ : ℕ → ℕ) (ρ : ProbabilityMeasure (E × T)), StrictMono φ ∧
      ρ.map Prod.fst = ν ∧
      ∀ f : (E × T) →ᵇ ℝ,
        Tendsto (fun n => ∫ ω, f (X (φ n) ω, τ (φ n) ω) ∂(P (φ n)))
          atTop (𝓝 (∫ z, f z ∂(ρ : Measure (E × T)))) := by
  let μ : ℕ → ProbabilityMeasure (E × T) := fun n =>
    ⟨(P n).map (fun ω => (X n ω, τ n ω)),
      (Measure.isProbabilityMeasure_map_iff ((hX n).prodMk (hτ n)).aemeasurable).2 inferInstance⟩
  have hmarg (n : ℕ) : (μ n).map Prod.fst =
      (⟨(P n).map (X n),
        (Measure.isProbabilityMeasure_map_iff (hX n).aemeasurable).2 inferInstance⟩ :
          ProbabilityMeasure E) := by
    apply Subtype.ext
    exact Measure.fst_map_prodMk (hX n) (hτ n)
  have hmarglim : Tendsto (fun n => (μ n).map Prod.fst) atTop (𝓝 ν) := by
    simpa only [hmarg] using hlim
  obtain ⟨φ, ρ, hφ, hρ, hm⟩ :=
    exists_subseq_joint_law_of_compact_clock_of_tendsto μ ν hmarglim
  refine ⟨φ, ρ, hφ, hm, fun f => ?_⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hρ) f
  have heq (n : ℕ) : ∫ z, f z ∂(μ (φ n) : Measure (E × T)) =
      ∫ ω, f (X (φ n) ω, τ (φ n) ω) ∂(P (φ n)) := by
    exact integral_map ((hX _).prodMk (hτ _)).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simpa only [heq] using h

end Sandpile.External.Stopping
