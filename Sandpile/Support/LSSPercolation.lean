import Sandpile.External.LSSDomination
import LatticeProb.Prob.Percolation.LSS.Countable
import LatticeProb.Prob.Percolation.Peierls

/-!
# Percolation of high-density dependent fields

The LSS domination theorem and the planar Peierls bound imply percolation for
fields whose laws satisfy the finite-range dependence condition of LSS.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Sandpile

/-- High-density fields percolate when their laws satisfy the LSS dependence condition. -/
theorem percolation_of_lss_kDependent :
    ∀ k : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Site 2 → Ω → Bool),
      (∀ z, Measurable (X z)) →
      LatticeProb.Percolation.LSS.KDependent k (P.map (fun ω z => X z ω)) →
      (∀ z, 1 - δ ≤ (P {ω | X z ω = true}).toReal) →
      ∀ᵐ ω ∂P, HasInfiniteComponent {z | X z ω} := by
  intro k
  obtain ⟨p₀, hp₀, hp⟩ := LatticeProb.Percolation.peierls_hasInfiniteComponent_ae
  obtain ⟨p, hp1, hdom⟩ := LatticeProb.Percolation.LSS.xlse_lss_general 2 k (by omega)
    p₀ (NNReal.coe_nonneg _) (by exact_mod_cast hp₀)
  refine ⟨(1 - p) / 2, by linarith, ?_⟩
  intro Ω _ P _ X hX hdep hmarg
  have hmap : Measurable (fun ω z => X z ω) := Measurable.of_eval hX
  let μ := P.map (fun ω z => X z ω)
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hmap.aemeasurable).2 inferInstance
  let E : Set (Site 2 → Bool) := {ω | HasInfiniteComponent {z | ω z = true}}
  have hE : MeasurableSet E := by
    exact LatticeProb.GraphPercolation.measurableSet_hasInfiniteComponent 2
  have hinc : LatticeProb.Percolation.LSS.IsIncreasingEvent E := by
    intro ω ω' hω hle
    exact hasInfiniteComponent_mono (fun z hz => hle z hz) hω
  have hm : ∀ z : Site 2, ENNReal.ofReal p ≤ μ {ω | ω z = true} := by
    intro z
    have hsite : p ≤ (P {ω | X z ω = true}).toReal := by
      have h := hmarg z
      linarith
    calc
      ENNReal.ofReal p ≤ ENNReal.ofReal (P {ω | X z ω = true}).toReal := ENNReal.ofReal_le_ofReal hsite
      _ = P {ω | X z ω = true} := ENNReal.ofReal_toReal (measure_ne_top _ _)
      _ = μ {ω | ω z = true} := by
        symm
        exact Measure.map_apply hmap (measurableSet_singleton true |>.preimage (measurable_pi_apply z))
  have hprod : LatticeProb.Percolation.LSS.sitePercolation 2 p₀ E = 1 := by
    change LatticeProb.Percolation.sitePercolation 2 p₀ E = 1
    rw [LatticeProb.Percolation.sitePercolation_eq_sitePercolationLaw p₀ hp₀.le]
    have : IsProbabilityMeasure (LatticeProb.Percolation.sitePercolationLaw p₀ hp₀.le) := by
      unfold LatticeProb.Percolation.sitePercolationLaw
      infer_instance
    exact (mem_ae_iff_prob_eq_one hE).1 (hp p₀ le_rfl hp₀.le)
  have hμ : μ E = 1 := by
    apply le_antisymm prob_le_one
    rw [← hprod]
    exact hdom μ inferInstance hdep hm E hE hinc
  have hae : ∀ᵐ ω ∂μ, ω ∈ E := (mem_ae_iff_prob_eq_one hE).2 hμ
  exact (ae_map_iff hmap.aemeasurable hE).1 hae

end Sandpile
