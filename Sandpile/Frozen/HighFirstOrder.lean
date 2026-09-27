/-
Theorem 1.3(iii)(a) of sandpile.tex, frozen.  `sandpile.tex:263-265`
(label `thm:main-explosion`, part (iii)(a)):

  "[$d\geq5$] For each fixed $x\in\Z^d$, $u_t(x)/\E u_t(0)\to1$ in $L^2$ and
   almost surely.  Moreover, the mean diverges: there is $c>0$ such that
   $\E u_t(0)\geq c(\log t)^{2/d}$ for all large $t$."

The paper proves this part by `thm:dgt4-height-lower`, whose proof cites
`eq:dgt4-green-tail` and `eq:dgt4-green-l2`; the `d ≥ 5` Green estimates are
proved unconditionally in this repository, `Sandpile.External.greenBoundsHigh`
(`Sandpile/External/GreenBoundsHighProved.lean`), so they are not carried here
as an explicit hypothesis.  The variance lower bound `ν₀` and the
exponential-moment bound `K₀` that `thm:dgt4-height-lower` quantifies over are
read off the law itself here, since this statement fixes the law first.
-/
import Sandpile.Law
import Sandpile.Frozen.DGT4HeightLower
import Sandpile.External.GreenBoundsHighProved

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.high_first_order
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀) (hexp : Integrable (fun z => Real.exp (θ₀ * |z|)) ν) :
    (∀ x : Sandpile.Site d,
      Tendsto (fun t : ℕ => ∫ σ, (Sandpile.odometer σ t x /
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t - 1) ^ 2
          ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0) ∧
      ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
        Tendsto (fun t : ℕ => Sandpile.odometer σ t x /
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 1)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ ((2 : ℝ) / d) ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  have hv : 0 < (evariance (id : ℝ → ℝ) ν).toReal :=
    ENNReal.toReal_pos (ne_of_gt hvar) (ne_of_lt hvar')
  set ν₀ : ℝ := Real.sqrt (evariance (id : ℝ → ℝ) ν).toReal with hν₀def
  have hν₀ : 0 < ν₀ := Real.sqrt_pos.mpr hv
  have hν₀sq : ENNReal.ofReal (ν₀ ^ 2) ≤ evariance (id : ℝ → ℝ) ν := by
    rw [hν₀def, Real.sq_sqrt hv.le, ENNReal.ofReal_toReal (ne_of_lt hvar')]
  obtain ⟨c, C, hc, hC, t₀, hmain⟩ :=
    Sandpile.Frozen.dgt4_height_lower d hd ν₀ θ₀
      (∫ z, Real.exp (θ₀ * |z|) ∂ν) hν₀ hθ₀
  obtain ⟨h1, -, h3⟩ := hmain ν hprob hmean hν₀sq hexp le_rfl
  exact ⟨h3, ⟨c, hc, Filter.eventually_atTop.2 ⟨t₀, h1⟩⟩⟩
