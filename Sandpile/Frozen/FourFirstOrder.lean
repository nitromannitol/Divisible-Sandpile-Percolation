import Sandpile.Support.D4Applications

/-!
# First-order odometer convergence at `d = 4`, frozen

Theorem 1.3(ii)(a), second clause, of `sandpile.tex`, frozen (`sandpile.tex:245-246`, label
`thm:main-explosion`, part (ii)(a)): at `d = 4`, for every fixed `x ∈ ℤ⁴`, the ratio
`u_t(x)/E u_t(0)` converges to `1` in `L²` and almost surely.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.four_first_order
    (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    ∀ x : Sandpile.Site 4,
      Tendsto (fun t : ℕ => ∫ σ, (Sandpile.odometer σ t x /
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t - 1) ^ 2
          ∂(Sandpile.centeredMassLaw 4 ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
        Tendsto (fun t : ℕ => Sandpile.odometer σ t x /
          Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t) atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  obtain ⟨c, C, hc, hC, t₀, hb, hlimit⟩ :=
    Sandpile.exists_critical_bounds_fixed_four ν hmean hvar hvar' θ₀ hθ₀ hexp
  exact hlimit
