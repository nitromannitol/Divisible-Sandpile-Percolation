/-
Proposition (Refined lower bound under a stretched-exponential lower-tail
bound) of sandpile.tex, frozen.  `sandpile.tex:4339-4350`
(label `prop:dgt4-height-lower-stretched`):

  "Suppose \eqref{eq:dgt4-exp-moment} holds.  Suppose also that there are
   $\gamma,a,A,s_{0}>0$ such that for every $s\geq s_{0}$,
     $\P(\zeta(0)\leq -s)\geq ae^{-As^\gamma}$.
   There is $c>0$ such that, for all large $t$,
     $\E u_t(0)\geq c(\log t)^{1/\min\{\gamma,d/2\}}$."

The cited hypothesis `eq:dgt4-exp-moment` of `sandpile.tex:4104-4106` is
  "$\E e^{\theta_0|\zeta(0)|}\leq K_0$"
for some `θ₀ > 0` and `K₀ < ∞`; it is transcribed here as integrability of
`exp (θ₀ |z|)` together with the bound `≤ K₀`, so that a non-integrable law
cannot satisfy it through the junk value `∫ = 0`.  The remaining standing
hypotheses of the section, `E ζ(0) = 0` and `0 < Var(ζ(0)) < ∞`, are listed
too.  The law of `ζ(0)` is `ν` and the mass field is `σ = 1 + 2dζ`, so the law
of `σ` is `centeredMassLaw d ν` and `E u_t(0)` is `meanOdometer`.  "For all
large `t`" is `∀ᶠ t in atTop` over `t : ℕ`.  Both `s ^ γ` and
`(log t) ^ (1 / min γ (d/2))` are real powers.
-/
import Sandpile.Law
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.IncrementBall
import Sandpile.Support.Increment
import Sandpile.Support.SceneryBridge

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_height_lower_stretched
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀)
    (hexpint : Integrable (fun z => Real.exp (θ₀ * |z|)) ν)
    (hexp : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀)
    (γ a A s₀ : ℝ) (hγ : 0 < γ) (ha : 0 < a) (hA : 0 < A) (hs₀ : 0 < s₀)
    (htail : ∀ s : ℝ, s₀ ≤ s →
      ENNReal.ofReal (a * Real.exp (-(A * s ^ γ))) ≤ ν (Set.Iic (-s))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℕ in atTop,
      c * (Real.log t) ^ (1 / min γ ((d : ℝ) / 2)) ≤
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t
-- FROZEN-STATEMENT-END
:= by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have _ := hGreenHigh
  have _ := hvar
  have _ := hvar'
  have _ := hexp
  set P := LatticeProb.iidLaw d ν with hP
  -- integrability of the one-site law from the exponential moment
  have habs : Integrable (fun z : ℝ => |z|) ν := by
    refine Integrable.mono' (hexpint.const_mul (1 / θ₀))
      measurable_id.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    have hle := LatticeProb.le_exp_self (θ₀ * |z|)
    have hbd : |z| ≤ 1 / θ₀ * Real.exp (θ₀ * |z|) := by
      rw [show (1 : ℝ) / θ₀ * Real.exp (θ₀ * |z|) = Real.exp (θ₀ * |z|) / θ₀ by ring,
        le_div_iff₀ hθ₀]
      nlinarith [hle]
    rw [Real.norm_eq_abs, abs_abs]
    exact hbd
  have hintν : Integrable (id : ℝ → ℝ) ν :=
    Integrable.mono' habs measurable_id.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => le_of_eq (Real.norm_eq_abs z))
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' habs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  -- the mean sequence
  set u : ℕ → ℝ := fun t => ∫ ζ, Sandpile.odometerOf ζ t 0 ∂P with hu
  have hu0 : u 0 = 0 := by
    rw [hu]
    simp [Sandpile.odometerOf]
  have humono : Monotone u := by
    refine monotone_nat_of_le_succ fun n => ?_
    refine integral_mono (Sandpile.integrable_odometerOf d ν hpos n 0)
      (Sandpile.integrable_odometerOf d ν hpos (n + 1) 0) fun ζ => ?_
    exact Sandpile.odometerOf_le_succ ζ n 0
  -- the universal branch: the scenery is below `-s₀` with a fixed probability
  set q₀ : ℝ := a * Real.exp (-(A * s₀ ^ γ)) with hq₀def
  have hq₀ : 0 < q₀ := by rw [hq₀def]; positivity
  have hcoord : ∀ z : Sandpile.Site d, q₀ ≤ P.real {ζ : Sandpile.Site d → ℝ | ζ z ≤ -s₀} := by
    intro z
    rw [Sandpile.measureReal_coord_le ν z (-s₀), Measure.real]
    have hqe : ENNReal.ofReal q₀ ≤ ν (Set.Iic (-s₀)) := htail s₀ le_rfl
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top ν _)).mpr hqe
    rwa [ENNReal.toReal_ofReal hq₀.le] at this
  obtain ⟨C₁, hC₁, hincr₁⟩ :=
    Sandpile.exists_increment_finite_ball hd1 ν hintν hmean hpos s₀ q₀ hs₀ hq₀ hcoord
  -- the mean diverges
  have hdiv : Filter.Tendsto u Filter.atTop Filter.atTop := by
    refine Sandpile.tendsto_atTop_of_increment u (by rw [hu0]) humono
      (fun x => s₀ / 2 * Real.exp (-(C₁ * (x + 1) ^ ((d : ℝ) / 2)))) (fun x => by positivity)
      (fun x y hx hxy => ?_) (fun n => hincr₁ n)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by linarith)
    have hxy1 : (x + 1) ^ ((d : ℝ) / 2) ≤ (y + 1) ^ ((d : ℝ) / 2) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by positivity)
    nlinarith [hC₁.le]
  -- the two branches
  set β : ℝ := min γ ((d : ℝ) / 2) with hβdef
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hd
    linarith
  have hβ : 0 < β := lt_min hγ hd2
  obtain ⟨c₂, C₂, M, hc₂, hC₂, hstep⟩ :
      ∃ c₂ C₂ M : ℝ, 0 < c₂ ∧ 0 < C₂ ∧
        ∀ n : ℕ, M ≤ u n → c₂ * Real.exp (-(C₂ * (u n + 1) ^ β)) ≤ u (n + 1) - u n := by
    rcases le_or_gt ((d : ℝ) / 2) γ with hcase | hcase
    · refine ⟨s₀ / 2, C₁, 0, by linarith, hC₁, fun n _ => ?_⟩
      have hβval : β = (d : ℝ) / 2 := by rw [hβdef]; exact min_eq_right hcase
      rw [hβval]
      exact hincr₁ n
    · refine ⟨(a / 2) ^ (3 ^ d), (3 : ℝ) ^ d * A * 6 ^ γ, max ((s₀ - 2) / 4) 0,
        by positivity, by positivity, fun n hn => ?_⟩
      have hβval : β = γ := by rw [hβdef]; exact min_eq_left hcase.le
      rw [hβval]
      have hbig : s₀ ≤ 4 * u n + 2 := by
        have h1 : (s₀ - 2) / 4 ≤ u n := le_trans (le_max_left _ _) hn
        linarith
      exact Sandpile.increment_stretched_step hd1 ν hintν hmean hpos γ a A s₀ hγ ha hA htail n hbig
  obtain ⟨c', hc', hev⟩ :=
    Sandpile.exists_log_lower_of_increment c₂ C₂ M β hc₂ hC₂ hβ u humono hdiv hstep
  refine ⟨c', hc', ?_⟩
  filter_upwards [hev] with t ht
  rw [Sandpile.meanOdometer_eq d ν hd1 t]
  exact ht
