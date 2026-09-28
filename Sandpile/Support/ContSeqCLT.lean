import LatticeProb.Prob.WeightedCLT
import Sandpile.Support.SceneryBridge
import Sandpile.Support.FiniteCoord

/-!
# The Lindeberg-Feller step along a real parameter

The Lindeberg-Feller step of the scaling limits of `ssec:dgt4-membrane`, in the form the
frozen statements need: convergence in distribution along `R → ∞` in `ℝ`, of a pairing
written as a finite linear functional of the scenery.

The paper's step (`sandpile.tex:4718-4731`) is: write `𝓕_R(φ) = ∑_z a_R(z) ζ(z)`; the
coefficient bound gives Lindeberg's condition, and the convergence of `∑_z a_R(z)^2` gives
the variance, so the Lindeberg-Feller theorem gives the Gaussian limit. The library's
`LatticeProb.weighted_iid_central_limit_pick` is that theorem for a sequence indexed by
`ℕ`; `atTop` on `ℝ` is countably generated, so convergence along every sequence tending to
infinity is convergence along `atTop` (`tendstoInDistribution_atTop_of_seq`), and combined
with the coefficient hypotheses this gives `tendstoInDistribution_linear_pick`, with
`tendstoInDistribution_congr_atTop` recording that the limit depends on the family only
through its eventual values.

The last lemma, `tendstoInDistribution_linear_pick_mass`, carries the limit from the i.i.d.
law of the scenery to the centred mass law of `σ = 1 + 2dζ`, which is the law the frozen
statements integrate over.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- Convergence in distribution along `atTop` on `ℝ` follows from convergence
along every sequence tending to infinity, since `atTop` on `ℝ` is countably
generated. -/
theorem tendstoInDistribution_atTop_of_seq {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {X : ℝ → Ω → E} {Z : Ω' → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (hX : ∀ R : ℝ, AEMeasurable (X R) μ) (hZ : AEMeasurable Z μ')
    (h : ∀ u : ℕ → ℝ, Tendsto u atTop atTop →
      TendstoInDistribution (fun n : ℕ => X (u n)) atTop Z (fun _ => μ) μ') :
    TendstoInDistribution X atTop Z (fun _ => μ) μ' := by
  refine ⟨hX, hZ, ?_⟩
  rw [Filter.tendsto_iff_seq_tendsto]
  intro u hu
  exact (h u hu).tendsto

/-- Convergence in distribution along `atTop` on `ℝ` depends on the family only
through its eventual values. -/
theorem tendstoInDistribution_congr_atTop {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {X Y : ℝ → Ω → E} {Z : Ω' → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (hX : ∀ R : ℝ, AEMeasurable (X R) μ)
    (hXY : ∀ᶠ R : ℝ in atTop, X R = Y R)
    (h : TendstoInDistribution Y atTop Z (fun _ => μ) μ') :
    TendstoInDistribution X atTop Z (fun _ => μ) μ' := by
  refine ⟨hX, h.aemeasurable_limit, ?_⟩
  refine Filter.Tendsto.congr' ?_ h.tendsto
  filter_upwards [hXY] with R hR
  refine Subtype.ext ?_
  simp only [hR]

/-- The Lindeberg-Feller step, along `R → ∞` in `ℝ`: a family of finite linear
functionals of a centred square-integrable i.i.d. scenery whose coefficients are
uniformly small and whose squares sum to `Q` converges in distribution to the
centred Gaussian of variance `(∫ z^2 dν) Q`. -/
theorem tendstoInDistribution_linear_pick (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (N : ℝ → ℕ) (a : (R : ℝ) → Fin (N R) → ℝ)
    (e : (R : ℝ) → Fin (N R) → Site d) (he : ∀ R, Function.Injective (e R))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ i, |a R i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun R : ℝ => ∑ i, a R i ^ 2) atTop (𝓝 Q)) :
    TendstoInDistribution (fun (R : ℝ) (ζ : Site d → ℝ) => ∑ i, a R i * ζ (e R i))
      atTop (id : ℝ → ℝ) (fun _ => LatticeProb.iidLaw d ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q))) := by
  have hm (R : ℝ) : Measurable (fun ζ : Site d → ℝ => ∑ i, a R i * ζ (e R i)) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply (e R i))
  refine tendstoInDistribution_atTop_of_seq (fun R => (hm R).aemeasurable)
    measurable_id.aemeasurable fun u hu => ?_
  exact weighted_iid_central_limit_pick ν hsq hmean (fun n => N (u n))
    (fun n => a (u n)) (fun n => e (u n)) (fun n => he (u n))
    (fun δ hδ => hu.eventually (hsmall δ hδ)) Q (hQ.comp hu)

/-- The same limit read on the centred mass law of `σ = 1 + 2dζ`, the law the
frozen statements integrate over. -/
theorem tendstoInDistribution_linear_pick_mass (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (N : ℝ → ℕ) (a : (R : ℝ) → Fin (N R) → ℝ)
    (e : (R : ℝ) → Fin (N R) → Site d) (he : ∀ R, Function.Injective (e R))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ i, |a R i| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun R : ℝ => ∑ i, a R i ^ 2) atTop (𝓝 Q)) :
    TendstoInDistribution
      (fun (R : ℝ) (σ : Site d → ℝ) => ∑ i, a R i * Sandpile.scenery d σ (e R i))
      atTop (id : ℝ → ℝ) (fun _ => Sandpile.centeredMassLaw d ν)
      (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q))) := by
  have hclt := tendstoInDistribution_linear_pick (d := d) ν hsq hmean N a e he hsmall Q hQ
  have hm (R : ℝ) : Measurable (fun ζ : Site d → ℝ => ∑ i, a R i * ζ (e R i)) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul (measurable_pi_apply (e R i))
  have hmp : MeasurePreserving (Sandpile.scenery d) (Sandpile.centeredMassLaw d ν)
      (LatticeProb.iidLaw d ν) :=
    ⟨Sandpile.measurable_scenery d, Sandpile.map_scenery_centeredMassLaw d ν hd⟩
  refine ⟨fun R => ((hm R).comp hmp.measurable).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  convert hclt.tendsto using 2 with R
  refine Subtype.ext ?_
  have hmap := Measure.map_map (μ := Sandpile.centeredMassLaw d ν) (hm R) hmp.measurable
  rw [hmp.map_eq] at hmap
  simpa only [Function.comp_def] using hmap.symm

end Sandpile.Support
