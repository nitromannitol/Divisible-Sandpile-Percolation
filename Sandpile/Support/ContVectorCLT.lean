/-
The finite-dimensional convergence that `prop:dlt4-heat-potential-invariance`
(`sandpile.tex:1841-1848`) asks for: a VECTOR of finite linear functionals of the
scenery converges in distribution to the vector of the values of the white noise
at the limiting indices.

The scalar Lindeberg-Feller step is already in the repository
(`tendstoInDistribution_linear_pick_mass`), and it produces a `gaussianReal`.
Three things turn it into the vector statement.  The Cramér-Wold device reduces
the vector convergence to the convergence of every dot product, and a dot product
of finite linear functionals of the scenery is again one, with the coefficients
combined.  The law of the limiting dot product is identified by
`map_whiteNoise_combination`: a finite linear combination of the values of the
white noise is a centred Gaussian whose variance is the square of the `L²` norm
of the combination of the indices.  What remains, and is the hypothesis `hQvar`
here, is the only analytic input: the limit of the sums of the squares of the
lattice coefficients is that `L²` norm divided by the variance of the one-site
law.
-/
import Sandpile.Support.ContSeqCLT
import LatticeProb.Prob.CramerWold
import Sandpile.Support.ContWhiteNoise

open LatticeProb.CramerWold

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-- Exchanging the two finite sums in a vector dot product. -/
theorem sum_dot_eq_sum_pick {m n : ℕ} (t : Fin m → ℝ) (a : Fin m → Fin n → ℝ)
    (v : Fin n → ℝ) :
    ∑ i, (∑ k, a i k * v k) * t i = ∑ k, (∑ i, t i * a i k) * v k := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- **The vector Lindeberg-Feller step.**  A family of vectors of finite linear
functionals of a centred square-integrable i.i.d. scenery, whose combined
coefficients are uniformly small and whose sums of squares converge, converges in
distribution to the vector of the values of a white noise at indices whose `L²`
inner products match the limits. -/
theorem tendstoInDistribution_vector_pick_mass (hd : 1 ≤ d)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsq : MemLp (id : ℝ → ℝ) 2 ν)
    (hmean : ∫ z, z ∂ν = 0)
    {m : ℕ} (F : ℝ → (Site d → ℝ) → Fin m → ℝ)
    (N : ℝ → ℕ) (a : (R : ℝ) → Fin m → Fin (N R) → ℝ)
    (e : (R : ℝ) → Fin (N R) → Site d) (he : ∀ R, Function.Injective (e R))
    (hF : ∀ (R : ℝ) (σ : Site d → ℝ) (i : Fin m),
      F R σ i = ∑ k, a R i k * Sandpile.scenery d σ (e R k))
    {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ) (hW : Sandpile.Continuum.IsWhiteNoise d W PW)
    (g : Fin m → Space d → ℝ) (hg : ∀ i, MemLp (g i) 2 (volume : Measure (Space d)))
    (Q : (Fin m → ℝ) → ℝ)
    (hsmall : ∀ (t : Fin m → ℝ) (δ : ℝ), 0 < δ →
      ∀ᶠ R : ℝ in atTop, ∀ k, |∑ i, t i * a R i k| ≤ δ)
    (hQlim : ∀ t : Fin m → ℝ,
      Tendsto (fun R : ℝ => ∑ k, (∑ i, t i * a R i k) ^ 2) atTop (𝓝 (Q t)))
    (hQvar : ∀ t : Fin m → ℝ, (∫ z, z ^ 2 ∂ν) * Q t
      = ∫ y : Space d, (∑ i, t i * g i y) * ∑ i, t i * g i y) :
    TendstoInDistribution F atTop (fun (ω : ΩW) (i : Fin m) => W (g i) ω)
      (fun _ => Sandpile.centeredMassLaw d ν) PW := by
  classical
  have hmeasF : ∀ R : ℝ, AEMeasurable (F R) (Sandpile.centeredMassLaw d ν) := by
    intro R
    refine Measurable.aemeasurable (measurable_pi_lambda _ fun i => ?_)
    have hfun : (fun σ : Site d → ℝ => F R σ i)
        = fun σ : Site d → ℝ => ∑ k, a R i k * Sandpile.scenery d σ (e R k) :=
      funext fun σ => hF R σ i
    rw [hfun]
    refine Finset.measurable_sum _ fun k _ => measurable_const.mul ?_
    exact (measurable_pi_apply (e R k)).comp (Sandpile.measurable_scenery d)
  have hmeasZ : AEMeasurable (fun (ω : ΩW) (i : Fin m) => W (g i) ω) PW :=
    (measurable_pi_lambda _ fun i => hW.meas (g i) (hg i)).aemeasurable
  refine tendstoInDistribution_pi_atTop_of_forall_dot F
    (fun (ω : ΩW) (i : Fin m) => W (g i) ω) (Sandpile.centeredMassLaw d ν) PW
    hmeasF hmeasZ ?_
  intro t
  have hfam : (fun (R : ℝ) (σ : Site d → ℝ) => ∑ i, F R σ i * t i)
      = fun (R : ℝ) (σ : Site d → ℝ) =>
        ∑ k, (∑ i, t i * a R i k) * Sandpile.scenery d σ (e R k) := by
    funext R σ
    simp only [hF]
    exact sum_dot_eq_sum_pick t (a R) (fun k => Sandpile.scenery d σ (e R k))
  rw [hfam]
  have hclt := tendstoInDistribution_linear_pick_mass hd ν hsq hmean N
    (fun R k => ∑ i, t i * a R i k) e he (hsmall t) (Q t) (hQlim t)
  have hZmeas : AEMeasurable (fun ω : ΩW => ∑ i, W (g i) ω * t i) PW := by
    refine Measurable.aemeasurable (Finset.measurable_sum _ fun i _ => ?_)
    exact (hW.meas (g i) (hg i)).mul_const _
  refine tendstoInDistribution_of_map_eq hclt _ hZmeas ?_
  have hcomb := map_whiteNoise_combination W PW hW t g hg
  have hfun2 : (fun ω : ΩW => ∑ i, W (g i) ω * t i)
      = fun ω : ΩW => ∑ i, t i * W (g i) ω := by
    funext ω
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hfun2, hcomb, hQvar t]

end Sandpile.Support
