/-
Reindexing lemmas for the subsequential convergence of `thm:dgt4-many-limits`
(`sandpile.tex:5900-5928`).

The frozen statement indexes the family by a real `L` and reads it at
`R_{k_{⌊L⌋}}`, so convergence along `atTop` on `ℝ` is convergence along
`ℓ → ∞`; the two lemmas here are what lets a convergence statement proved for
the real-indexed family be read at the natural subsequence, and conversely.
-/
import Sandpile.Support.ContNonconvergence
import Sandpile.Continuum.Membrane

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

/-- A subsequence of a real-valued family converging in distribution converges to
the same law. -/
theorem tendstoInDistribution_comp_atTop_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → ℝ)
    (μ' : Measure ℝ) [IsProbabilityMeasure μ']
    (Rs : ℝ → ℝ) (hRs : Tendsto Rs atTop atTop)
    (h : TendstoInDistribution F atTop (id : ℝ → ℝ) (fun _ => P) μ') :
    TendstoInDistribution (fun k : ℝ => F (Rs k)) atTop (id : ℝ → ℝ) (fun _ => P) μ' :=
  ⟨fun k => h.forall_aemeasurable (Rs k), h.aemeasurable_limit, h.tendsto.comp hRs⟩

/-- Tightness in negative Sobolev spaces is preserved by reindexing along a map
that stays at least one. -/
theorem TightInNegSobolev.comp_atTop {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {s : ℝ} {P : Measure Ω}
    {F : ℝ → Ω → (Space d → ℝ) → ℝ}
    (h : TightInNegSobolev d s P F) {g : ℝ → ℝ}
    (hg1 : ∀ L : ℝ, 1 ≤ L → 1 ≤ g L) :
    TightInNegSobolev d s P (fun L => F (g L)) := by
  intro D hD ε hε
  obtain ⟨M, hM, hMR⟩ := h D hD ε hε
  exact ⟨M, hM, fun R hR => hMR (g R) (hg1 R hR)⟩

/-- Convergence in negative Sobolev spaces is preserved by reindexing along a
map that tends to infinity and stays at least one. -/
theorem TendstoInNegSobolev.comp_atTop {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {s : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℝ → Ω → (Space d → ℝ) → ℝ} {K : (Space d → ℝ) → (Space d → ℝ) → ℝ}
    (h : TendstoInNegSobolev d s P F K) {g : ℝ → ℝ}
    (hg : Tendsto g atTop atTop) (hg1 : ∀ L : ℝ, 1 ≤ L → 1 ≤ g L) :
    TendstoInNegSobolev d s P (fun L => F (g L)) K := by
  exact ⟨fun φ hφ => tendstoInDistribution_comp_atTop_real P (fun R ω => F R ω φ)
    (gaussianReal 0 (Real.toNNReal (K φ φ))) g hg (h.1 φ hφ), TightInNegSobolev.comp_atTop h.2 hg1⟩

end Sandpile.Support
