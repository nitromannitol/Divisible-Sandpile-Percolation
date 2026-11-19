import Sandpile.Support.SquareSummableTruncation
import Sandpile.Support.ContSeqCLT

/-!
# Finite-row central limit theorem for square-summable coefficients

Square-summable coefficient rows can be truncated to finite subsets with
vanishing squared error. If the coefficients tend uniformly to zero and their
squared masses converge, the corresponding finite weighted sums converge to a
centered Gaussian by `LatticeProb.weighted_iid_central_limit_pick` in
`LatticeProb/Prob/WeightedCLT.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

/-- Square-summable rows with uniformly vanishing coefficients admit finite
truncations whose weighted sums satisfy the central limit theorem. The omitted
squared mass is bounded by `exp (-R)` for every real `R`. -/
theorem exists_finset_tendstoInDistribution_linear_pick
    {d : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : MemLp (id : ℝ → ℝ) 2 ν) (hmean : ∫ z, z ∂ν = 0)
    (a : ℝ → Sandpile.Site d → ℝ) (ha : ∀ R, Summable (fun x => a R x ^ 2))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ R : ℝ in atTop, ∀ x, |a R x| ≤ δ)
    (Q : ℝ) (hQ : Tendsto (fun R => ∑' x, a R x ^ 2) atTop (𝓝 Q)) :
    ∃ s : ℝ → Finset (Sandpile.Site d),
      (∀ R, (∑' x : ((s R)ᶜ : Set (Sandpile.Site d)), a R x ^ 2) < Real.exp (-R)) ∧
      TendstoInDistribution
        (fun (R : ℝ) (ζ : Sandpile.Site d → ℝ) =>
          ∑ x ∈ s R, a R x * ζ x)
        atTop (id : ℝ → ℝ) (fun _ => LatticeProb.iidLaw d ν)
        (gaussianReal 0 (Real.toNNReal ((∫ z, z ^ 2 ∂ν) * Q))) := by
  have hexp : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  obtain ⟨s, htail, hmass⟩ := exists_finset_rows_sq_tendsto atTop a ha
    (fun R => Real.exp (-R)) (fun R => Real.exp_pos _) hexp Q hQ
  refine ⟨s, htail, ?_⟩
  have hclt := tendstoInDistribution_linear_pick ν hsq hmean (fun R => (s R).card)
    (fun R i => a R (Sandpile.siteEnum (s R) i))
    (fun R => Sandpile.siteEnum (s R)) (fun R => Sandpile.siteEnum_injective (s R))
    (fun δ hδ => (hsmall δ hδ).mono fun _ h i => h _) Q ?_
  · convert hclt using 1
    funext R ζ
    exact (Sandpile.sum_siteEnum (s R) (fun x => a R x * ζ x)).symm
  · convert hmass using 1
    funext R
    exact Sandpile.sum_siteEnum (s R) (fun x => a R x ^ 2)

end Sandpile.Support
