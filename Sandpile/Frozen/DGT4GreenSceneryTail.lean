/-
Lemma (lower tail of a finite Green average of the scenery) of sandpile.tex,
frozen.  `sandpile.tex:4385-4402`
(label `lem:dgt4-stretched-green-scenery-tail`):

  "Suppose $\gamma\in[1,\infty)$, with $\gamma\ne d/2$.  Assume
   \eqref{eq:dgt4-exp-moment} and suppose that, for some $c_1>0$,
   $C_1<\infty$, and $s_{0}>0$, for every $s\geq s_{0}$,
     $\P(\zeta(0)\leq -s)\leq C_1e^{-c_1s^\gamma}$.
   Then there are constants $c,C>0$ such that, for all $m\geq1$ and all
   $s\geq1$,
     $\P\left(\sum_{y\in\Z^d}g_m(0,y)\zeta(y)\leq -s\right)
      \leq C\exp\{-c s^{\min\{\gamma,d/2\}}\}$."

The cited hypothesis `eq:dgt4-exp-moment` of `sandpile.tex:4104-4106` is
  "$\E e^{\theta_0|\zeta(0)|}\leq K_0$"
for some `θ₀ > 0` and `K₀ < ∞`; it is transcribed as integrability of
`exp (θ₀ |z|)` together with the bound `≤ K₀`, so a non-integrable law cannot
satisfy it through the junk value `∫ = 0`.  The statement is about the scenery
alone, so the field is `ζ` with i.i.d. law `LatticeProb.iidLaw d ν`, and
`g_m(0,y)` is `Sandpile.greenTime d m 0 y`.  The sum runs over all of `ℤ^d`, so
it is a `tsum`; a non-summable family would take the junk value `0`, which for
`s ≥ 1` lies outside `(-∞, -s]` and would make the probability bound hold
vacuously.  To exclude that, the conclusion asserts summability of the family
for every scenery and every `m ≥ 1` as a first conjunct: this is true because
`g_m(0, ·)` is supported in the ball of radius `m`, so the family is finitely
supported.  The probability itself is compared in `ℝ≥0∞` against
`ENNReal.ofReal` of the right side, so no `toReal` junk enters.  The standing
hypotheses of the section, `E ζ(0) = 0` and `0 < Var(ζ(0)) < ∞`, are listed.
-/
import Sandpile.Support.GreenSceneryTail

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_green_scenery_tail
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (c₁ C₁ s₀ : ℝ) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hs₀ : 0 < s₀)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₁ * Real.exp (-(c₁ * s ^ γ)))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ (m : ℕ) (ζ : Sandpile.Site d → ℝ), 1 ≤ m →
          Summable fun y : Sandpile.Site d => Sandpile.greenTime d m 0 y * ζ y) ∧
        ∀ m : ℕ, 1 ≤ m → ∀ s : ℝ, 1 ≤ s →
          LatticeProb.iidLaw d ν
              {ζ : Sandpile.Site d → ℝ |
                ∑' y : Sandpile.Site d, Sandpile.greenTime d m 0 y * ζ y ≤ -s} ≤
            ENNReal.ofReal (C * Real.exp (-(c * s ^ min γ ((d : ℝ) / 2))))
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  -- The variance hypotheses are the standing ones of the section and are not
  -- used: the bound depends on the law only through its exponential moment and
  -- its lower tail.
  have _hvar := hvar
  have _hvar' := hvar'
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  rcases eq_or_lt_of_le hγ with hone | hgt
  · obtain ⟨c, C, hc, hC, hbound⟩ :=
      Sandpile.exists_scenery_tail_linear hGreenHigh hd ν θ₀ K₀ hθ₀ hexpint hexp hmean
    refine ⟨c, C, hc, hC, fun m ζ _ => Sandpile.summable_greenTime_mul m 0 ζ,
      fun m hm s hs => ?_⟩
    have hmin : min γ ((d : ℝ) / 2) = 1 := by
      rw [← hone]; exact min_eq_left (by linarith)
    rw [hmin, Real.rpow_one]
    exact hbound m hm s hs
  · obtain ⟨c, C, hc, hC, hbound⟩ :=
      Sandpile.exists_scenery_tail_stretched hGreenHigh hd ν θ₀ K₀ hθ₀ hexpint hexp hmean
        γ c₁ C₁ s₀ hgt hγd hc₁ hC₁ hs₀ htail
    exact ⟨c, C, hc, hC, fun m ζ _ => Sandpile.summable_greenTime_mul m 0 ζ, hbound⟩
