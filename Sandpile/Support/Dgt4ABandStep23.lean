/-
The bridge from Step 2 to Step 3.

Step 2 produces the contact estimates along ONE scale, with the rate sequence
`κ_k = 1 + 1/ϑ_k`.  Step 3 consumes `UniformContactThresholdsAlong` at a FIXED
`κ`, and its hypothesis is that the rate sequence converges to that `κ`.  Along
the full sequence it does not: the exponents `ϑ_k` are chosen so that their set of
subsequential limits is all of `[1,2]`, which is precisely what produces a
continuum of distinct limits.

So the bridge is a subsequence, exactly as the paper takes one and as the frozen
statement states.  Step 1 already supplies, for every `κ` in the range, a strictly
increasing `kl` along which the rate converges to `κ`; what is missing is that the
Step 2 output survives composition with it.

This also settles a predicate flagged during the audit: `Dgt4AStep2Input` asks for
a single scale serving EVERY `κ`, which no scale can do, since one rate sequence
cannot converge to two different limits.  The route below does not use it.
-/
import Sandpile.Support.Dgt4ABandStep2

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- **Step 2's output survives a subsequence.**  Both of its clauses are
`∀ᶠ k in atTop` statements, and a strictly increasing reindexing tends to
infinity, so each transfers. -/
theorem dgt4AStep2Output_comp (d : ℕ) (ν : Measure ℝ) (kseq Rseq : ℕ → ℝ)
    (kl : ℕ → ℕ) (hkl : StrictMono kl) (h : Dgt4AStep2Output d ν kseq Rseq) :
    Dgt4AStep2Output d ν (kseq ∘ kl) (Rseq ∘ kl) := by
  intro T hT
  obtain ⟨h1, h2⟩ := h T hT
  have hkl' : Tendsto kl atTop atTop := hkl.tendsto_atTop
  exact ⟨fun δ hδ η hη => hkl'.eventually (h1 δ hδ η hη),
    fun δ hδ η hη => hkl'.eventually (h2 δ hδ η hη)⟩

/-- **The Step 2 to Step 3 bridge.**  One scale, and for each `κ` in the range a
subsequence of it along which the contact thresholds are uniform at that `κ`.

Proof.  `exists_dgt4AStep2Output` gives the scale and the output; Step 1's own
clause gives, for each `κ`, a strictly increasing `kl` with the rate converging to
`κ`; `dgt4AStep2Output_comp` transfers the output along `kl`; and
`uniformContactThresholdsAlong_of_step2` then applies at the fixed `κ`.

The subsequence is chosen BEFORE the horizon, not after.  Step 3's input asks for
one subsequence serving every horizon, and `Dgt4AStep2Output` is itself
`∀ T > 0, …`, so the composition preserves that order; stating it the other way
round would not compose. -/
theorem exists_uniformContactThresholdsAlong (P : BandParameters) (hd : 5 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hsq : Integrable (fun z : ℝ => z ^ 2) ν)
    (hnondeg : ∀ z : ℝ, ν ≠ Measure.dirac z)
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hgap : P.lam0 < θ₀ / LatticeProb.greenRatioSup d)
    (hprof : BandIntegratedProfile P ν) (hbp : BandProfile P ν)
    (hdens : BandDensity P ν) (hlow : BandLowerIsolation P ν)
    (hsub : ∀ κ : ℝ, κ ∈ Icc ((3 : ℝ) / 2) 2 →
      ∃ kl : ℕ → ℕ, StrictMono kl ∧
        Tendsto (fun n => 1 + 1 / P.theta (kl n)) atTop (𝓝 κ)) :
    ∃ R : ℕ → ℝ, StrictMono R ∧ Tendsto R atTop atTop ∧
      ∀ κ : ℝ, κ ∈ Icc ((3 : ℝ) / 2) 2 →
        ∃ kl : ℕ → ℕ, StrictMono kl ∧
          ∀ T : ℝ, 0 < T → UniformContactThresholdsAlong d ν κ T (R ∘ kl) := by
  obtain ⟨R, hRmono, hRtop, hout⟩ := exists_dgt4AStep2Output P hd ν hatom hint hmean hsq
    hnondeg hθ₀ hexp hgap hprof hbp hdens hlow
  refine ⟨R, hRmono, hRtop, fun κ hκ => ?_⟩
  obtain ⟨kl, hkl, hk⟩ := hsub κ hκ
  refine ⟨kl, hkl, fun T hT => ?_⟩
  have hκ0 : 0 < κ := by linarith [hκ.1]
  exact uniformContactThresholdsAlong_of_step2 d ν ((fun k => 1 + 1 / P.theta k) ∘ kl) (R ∘ kl)
    (hRtop.comp hkl.tendsto_atTop) κ T hκ0 hT hk
    (dgt4AStep2Output_comp d ν _ R kl hkl hout)

end Sandpile.Support
