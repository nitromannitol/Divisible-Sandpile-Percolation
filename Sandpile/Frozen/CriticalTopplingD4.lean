/-
Theorem of Section 5 of sandpile.tex, frozen.  `sandpile.tex:2692-2721`
(label `thm:critical-toppling-d4`):

  "Fix $\nu_{0}>0$, $\theta_{0}>0$, and $K_{0}<\infty$.  There are constants
   $c=c(\nu_{0},\theta_{0},K_{0})>0$, $C=C(\nu_{0},\theta_{0},K_{0})<\infty$, and
   $t_0=t_0(\nu_{0},\theta_{0},K_{0})<\infty$ such that, for every mean-zero
   i.i.d.\ field $(\zeta(x))_{x\in\Z^4}$ satisfying
   $\Var(\zeta(0))\geq\nu_{0}^2$, $\E e^{\theta_{0}|\zeta(0)|}\leq K_{0}$,
   and every $t\geq t_0$,
   $c\log t\leq \E u_t(0)\leq C\log t$.
   Moreover, for every $x\in\Z^4$, $t\geq2$, and $s\geq0$,
   $\P(|u_t(x)-\E u_t(0)|>s)\leq C\exp\{-c\min(s^2/\log t,s)\}$.
   Consequently, $u_t(x)/\E u_t(0)\to1$ in $L^2$ and almost surely for every
   fixed $x$."

The scenery `ζ` is carried by its one-site law `ν`, and the field itself by
`centeredMassLaw 4 ν`, the law of `σ = 1 + 8ζ`; `E u_t(0)` is `meanOdometer`.
`c`, `C` and `t₀` are bound after `ν₀, θ₀, K₀` and before the law, as the paper
orders them, so they are uniform over every law satisfying the two bounds.  The
three clauses have different ranges of `t`: the mean bound holds for `t ≥ t₀`,
the concentration bound for all `t ≥ 2`, and the first-order limit is a
statement about `t → ∞`, so they are three conjuncts under the law rather than
one clause under a single `∀ t`.  The concentration bound is stated on the
measure of the deviation event in `ℝ≥0∞`, against `ENNReal.ofReal` of the
paper's right-hand side, so that no `toReal` junk value can weaken it;
`t ≥ 2` keeps `log t` away from zero in the ratio `s²/log t`.

The exponential-moment bound is stated together with the integrability of the
exponential, as the paper's `K₀ < ∞` requires: the Bochner integral of a
non-integrable nonnegative function is zero, so the bound alone would hold for
every law with no exponential moment.
-/
import Sandpile.Law
import Sandpile.External.VarianceScale
import Sandpile.Support.D4Convergence
import Sandpile.Support.D4Mean

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.critical_toppling_d4
    (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ t₀ : ℕ, ∀ (ν : Measure ℝ), IsProbabilityMeasure ν →
      ∫ z, z ∂ν = 0 → ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
      Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
      ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
      (∀ t : ℕ, t₀ ≤ t →
          c * Real.log t ≤ Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ∧
            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t ≤ C * Real.log t) ∧
        (∀ x : Sandpile.Site 4, ∀ t : ℕ, 2 ≤ t → ∀ s : ℝ, 0 ≤ s →
          Sandpile.centeredMassLaw 4 ν
              {σ | s < |Sandpile.odometer σ t x -
                Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t|} ≤
            ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2 / Real.log t) s)))) ∧
        (∀ x : Sandpile.Site 4,
          Tendsto (fun t : ℕ => ∫ σ, (Sandpile.odometer σ t x /
            Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t - 1) ^ 2
              ∂(Sandpile.centeredMassLaw 4 ν)) atTop (𝓝 0) ∧
          ∀ᵐ σ ∂(Sandpile.centeredMassLaw 4 ν),
            Tendsto (fun t : ℕ => Sandpile.odometer σ t x /
              Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t) atTop (𝓝 1))
-- FROZEN-STATEMENT-END
:= by
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  obtain ⟨cL, hcL, tL, hlower⟩ :=
    Sandpile.exists_log_mean_lower_four hVarScale ν₀ θ₀ K₀ hν₀ hθ₀
  obtain ⟨CU, hCU, hupper⟩ :=
    Sandpile.exists_crude_log_upper_four_uniform hVarScale θ₀ K₀ hθ₀
  obtain ⟨cc, CC, hcc, hCC, hconc⟩ :=
    Sandpile.exists_odometer_conc_four hVarScale θ₀ K₀ hθ₀
  refine ⟨min cL cc, max (2 * CU) CC, lt_min hcL hcc,
    lt_of_lt_of_le hCC (le_max_right _ _), max tL 2, ?_⟩
  intro ν hprob hmean hvar hexpint hexp
  haveI := hprob
  have hint := LatticeProb.integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    hint.abs.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
      exact max_le (le_abs_self z) (abs_nonneg z))
  have hl : ∀ t : ℕ, tL ≤ t → cL * Real.log t ≤
      Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t := by
    intro t ht
    rw [Sandpile.meanOdometer_eq 4 ν (by norm_num) t]
    exact hlower ν hprob hmean hvar hexpint hexp t ht
  have hc := hconc ν hprob hexpint hexp
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have htL : tL ≤ t := (le_max_left _ _).trans ht
    have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
    have hlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))
    constructor
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hlog).trans (hl t htL)
    · rw [Sandpile.meanOdometer_eq 4 ν (by norm_num) t]
      have h1 := hupper ν hprob hmean hexpint hexp hint hpos t
      have h2 := mul_le_mul_of_nonneg_left (Sandpile.log_add_two_le_two_log t ht2) hCU.le
      have h3 := mul_le_mul_of_nonneg_right (le_max_left (2 * CU) CC) hlog
      nlinarith
  · intro x t ht s hs
    have hsub : {σ : Sandpile.Site 4 → ℝ | s < |Sandpile.odometer σ t x -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t|} ⊆
        {σ | s ≤ |Sandpile.odometer σ t x - Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t|} :=
      by
        intro σ h
        change s < |Sandpile.odometer σ t x - Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t| at h
        change s ≤ |Sandpile.odometer σ t x - Sandpile.meanOdometer (Sandpile.centeredMassLaw 4 ν) t|
        exact h.le
    refine (measure_mono hsub).trans ((hc x t ht s hs).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have hmin : 0 ≤ min (s ^ 2 / Real.log (t : ℝ)) s :=
      le_min (div_nonneg (sq_nonneg s)
        (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t)))) hs
    exact mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) hmin)))
      (Real.exp_nonneg _) (hCC.le.trans (le_max_right _ _))
  · intro x
    exact ⟨Sandpile.tendsto_ratio_L2_four hVarScale ν
        (Sandpile.integrable_sq_of_exp_moment ν θ₀ hθ₀ hexpint) hcL hl x,
      Sandpile.tendsto_ratio_ae_four ν hpos hint hmean hcc hCC hcL hc hl x⟩
