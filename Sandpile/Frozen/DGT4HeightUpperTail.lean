/-
Theorem (Refined high-dimensional upper bound) of sandpile.tex, frozen.
`sandpile.tex:4501-4512` (label `thm:dgt4-height-upper-tail`):

  "Assume \eqref{eq:dgt4-exp-moment}.  Suppose that there are
   $\gamma\in[1,\infty)$, $\gamma\ne d/2$, and $c_0,C_0,s_{0}>0$ such that for
   every $s\geq s_{0}$
     $\P(\zeta(0)\leq -s)\leq C_0e^{-c_0s^\gamma}$.
   Then there is $C<\infty$ such that for every $t\geq 2$,
     $\E u_t(0)\leq C(\log t)^{1/\min\{\gamma,d/2\}}$."

The cited hypothesis `eq:dgt4-exp-moment` of `sandpile.tex:4104-4106` is
  "$\E e^{\theta_0|\zeta(0)|}\leq K_0$"
for some `θ₀ > 0` and `K₀ < ∞`; it is transcribed as integrability of
`exp (θ₀ |z|)` together with the bound `≤ K₀`, so a non-integrable law cannot
satisfy it through the junk value `∫ = 0`.  The remaining standing hypotheses
of the section, `E ζ(0) = 0` and `0 < Var(ζ(0)) < ∞`, are listed.  The law of
`ζ(0)` is `ν` and the mass field is `σ = 1 + 2dζ`, so the law of `σ` is
`centeredMassLaw d ν` and `E u_t(0)` is `meanOdometer`.  `γ ≠ d/2` is a
hypothesis, not a side condition on the conclusion.  `C` is bound after the
law and after `γ, c₀, C₀, s₀`, and before `t`, so it depends on all of them
and not on `t`.  The threshold `t ≥ 2` is the paper's, and it keeps
`Real.log t` positive, so the junk value `Real.log 0 = Real.log 1 = 0` cannot
make the bound trivial.
-/
import Sandpile.Law
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.RefinedIncrement

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_height_upper_tail
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (γ : ℝ) (hγ : 1 ≤ γ) (hγd : γ ≠ (d : ℝ) / 2)
    (c₀ C₀ s₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hs₀ : 0 < s₀)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ν (Set.Iic (-s)) ≤ ENNReal.ofReal (C₀ * Real.exp (-(c₀ * s ^ γ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, 2 ≤ t →
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t ≤
        C * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2))
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hprob
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hint : Integrable id ν := LatticeProb.integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hposν : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  set β : ℝ := min γ ((d : ℝ) / 2) with hβdef
  have hβ1 : (1 : ℝ) ≤ β := le_min hγ (by linarith)
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le one_pos hβ1
  obtain ⟨c, C, hc, hC, hstep⟩ :=
    Sandpile.exists_refined_increment hGreenHigh hd ν hprob hmean hvar hvar' θ₀ K₀ hθ₀
      hexpint hexp γ hγ hγd c₀ C₀ s₀ hc₀ hC₀ hs₀ htail
  have h0 : (∫ ζ, Sandpile.odometerOf ζ 0 0 ∂(LatticeProb.iidLaw d ν)) = 0 := by
    simp [Sandpile.odometerOf]
  obtain ⟨C', hC', hbound⟩ :=
    Sandpile.exists_log_upper_of_stretched_increment C c β hC hc hβ0
      (fun t : ℕ => ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν)) h0
      (Sandpile.meanOdometerOf_mono ν hposν) hstep
  refine ⟨C' * 2 ^ (1 / β), by positivity, ?_⟩
  intro t ht
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (by linarith)
  have hsq : ((t : ℝ) + 2) ≤ (t : ℝ) ^ 2 := by nlinarith
  have hlog2 : Real.log ((t : ℝ) + 2) ≤ 2 * Real.log (t : ℝ) := by
    have h1 : Real.log ((t : ℝ) + 2) ≤ Real.log ((t : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) hsq
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hlognn : (0 : ℝ) ≤ Real.log ((t : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hpow : (Real.log ((t : ℝ) + 2)) ^ (1 / β)
      ≤ 2 ^ (1 / β) * (Real.log (t : ℝ)) ^ (1 / β) := by
    have h1 : (Real.log ((t : ℝ) + 2)) ^ (1 / β) ≤ (2 * Real.log (t : ℝ)) ^ (1 / β) :=
      Real.rpow_le_rpow hlognn hlog2 (by positivity)
    rwa [Real.mul_rpow (by norm_num) hlogt.le] at h1
  have hmeq : Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t
      = ∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν) :=
    Sandpile.meanOdometer_eq d ν hd1 t
  rw [hmeq]
  calc (∫ ζ, Sandpile.odometerOf ζ t 0 ∂(LatticeProb.iidLaw d ν))
      ≤ C' * (Real.log ((t : ℝ) + 2)) ^ (1 / β) := hbound t
    _ ≤ C' * (2 ^ (1 / β) * (Real.log (t : ℝ)) ^ (1 / β)) :=
        mul_le_mul_of_nonneg_left hpow hC'.le
    _ = C' * 2 ^ (1 / β) * (Real.log (t : ℝ)) ^ (1 / β) := by ring
