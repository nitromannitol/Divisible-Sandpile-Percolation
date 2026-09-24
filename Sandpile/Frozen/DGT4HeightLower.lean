/-
Theorem (High-dimensional mean growth) of sandpile.tex, frozen.
`sandpile.tex:4168-4191` (label `thm:dgt4-height-lower`):

  "Fix $\nu_0>0$, $\theta_0>0$, and $K_0<\infty$.  There are $c,C>0$ and
   $t_0<\infty$, depending only on $d,\nu_0,\theta_0,K_0$, such that every
   mean-zero i.i.d.\ field satisfying
     $\Var(\zeta(0))\geq\nu_0^2$, $\E e^{\theta_0|\zeta(0)|}\leq K_0$
   satisfies, for every $t\geq t_0$,
     $\E u_t(0)\geq c(\log t)^{2/d}$.
   Moreover, for every $x\in\Z^d$, $t\geq0$, and $s\geq0$,
     $\P(|u_t(x)-\E u_t(0)|\geq s)\leq C\exp\{-c\min(s^2,s)\}$.
   Consequently, for every fixed $x\in\Z^d$,
     $u_t(x)/\E u_t(0)\to1$ in $L^2$ and almost surely."

The field is the scenery `ζ` of the section, so the mass field is
`σ = 1 + 2dζ` and the law is `centeredMassLaw d ν` for a one-site law `ν` of
`ζ(0)`; `E u_t(0)` is `meanOdometer`.  `c`, `C`, `t₀` are bound after
`d, ν₀, θ₀, K₀` and before `ν`, which is the paper's "depending only on
$d,\nu_0,\theta_0,K_0$".  The exponential moment is transcribed as
integrability together with the bound `≤ K₀`, so that a non-integrable law
cannot satisfy the hypothesis through the junk value `∫ = 0`.  The
concentration bound is stated in `ℝ≥0∞` against `ENNReal.ofReal` of the right
side, avoiding `toReal` on the left.  Finiteness of the variance is not
listed: it follows from the exponential moment, and the theorem's own
hypothesis list is `Var ≥ ν₀²` together with `E e^{θ₀|ζ(0)|} ≤ K₀`.
-/
import Sandpile.Law
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.HeightLower

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.dgt4_height_lower
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν₀ θ₀ K₀ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ t₀ : ℕ,
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        ENNReal.ofReal (ν₀ ^ 2) ≤ evariance id ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        (∀ t : ℕ, t₀ ≤ t →
            c * (Real.log t) ^ ((2 : ℝ) / d) ≤
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) ∧
          (∀ (x : Sandpile.Site d) (t : ℕ) (s : ℝ), 0 ≤ s →
            Sandpile.centeredMassLaw d ν
                {σ | s ≤ |Sandpile.odometer σ t x -
                  Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t|} ≤
              ENNReal.ofReal (C * Real.exp (-(c * min (s ^ 2) s)))) ∧
          ∀ x : Sandpile.Site d,
            Tendsto (fun t : ℕ => ∫ σ, (Sandpile.odometer σ t x /
              Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t - 1) ^ 2
                ∂(Sandpile.centeredMassLaw d ν)) atTop (𝓝 0) ∧
            ∀ᵐ σ ∂(Sandpile.centeredMassLaw d ν),
              Tendsto (fun t : ℕ => Sandpile.odometer σ t x /
                Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) atTop (𝓝 1)
-- FROZEN-STATEMENT-END
:= by
  classical
  have hd1 : 1 ≤ d := le_trans (by norm_num) hd
  have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  obtain ⟨a, q, ha, hq0, hq1, htail⟩ := Sandpile.exists_uniform_left_tail ν₀ θ₀ K₀ hν₀ hθ₀
  obtain ⟨c₁, hc₁, t₀, hlow⟩ :=
    Sandpile.exists_mean_lower_uniform (d := d) hd1 hd2 a q ha hq0 hq1
  obtain ⟨c₂, C₂, hc₂, hC₂, hconc⟩ :=
    Sandpile.exists_odometer_conc (d := d) hGreenHigh hd θ₀ K₀ hθ₀
  refine ⟨min c₁ c₂, C₂, lt_min hc₁ hc₂, hC₂, max t₀ 1, ?_⟩
  intro ν hprob hmean hvar hexpint hexp
  haveI := hprob
  have hint : Integrable id ν := LatticeProb.integrable_id_of_exp_moment ν θ₀ hθ₀ hexpint
  have hpos : Integrable (fun z : ℝ => max z 0) ν :=
    Integrable.mono' hint.abs (measurable_id.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right z 0)]
        exact max_le (le_abs_self z) (abs_nonneg z))
  have hsq : Integrable (fun z : ℝ => z ^ 2) ν :=
    Sandpile.integrable_sq_of_exp_moment ν θ₀ hθ₀ hexpint
  have htailν := htail ν hprob hmean hvar hexpint hexp
  -- the mean lower bound, carried into the mass-field language
  have hmeanlow : ∀ t : ℕ, t₀ ≤ t →
      c₁ * (Real.log t) ^ ((2 : ℝ) / d) ≤
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t := by
    intro t ht
    rw [Sandpile.meanOdometer_eq d ν hd1 t]
    exact hlow ν hprob hint hmean htailν t ht
  have hlognn : ∀ t : ℕ, 1 ≤ t → (0 : ℝ) ≤ (Real.log t) ^ ((2 : ℝ) / d) := by
    intro t ht
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast ht)) _
  have hdiv : Filter.Tendsto
      (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t)
      Filter.atTop Filter.atTop :=
    Sandpile.tendsto_atTop_of_log_lower hc₁ (by positivity) hmeanlow
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have ht₀ : t₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
    refine le_trans ?_ (hmeanlow t ht₀)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hlognn t ht1)
  · intro x t s hs
    refine le_trans (hconc ν hprob hexpint hexp x t s hs) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₂.le
    refine Real.exp_le_exp.mpr ?_
    have hmin : 0 ≤ min (s ^ 2) s := le_min (sq_nonneg s) hs
    have : min c₁ c₂ * min (s ^ 2) s ≤ c₂ * min (s ^ 2) s :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hmin
    linarith
  · intro x
    refine ⟨Sandpile.tendsto_ratio_L2 hGreenHigh hd ν hsq hdiv x, ?_⟩
    exact Sandpile.tendsto_ratio_ae hd1 ν hpos hint hmean hc₂ hC₂ hc₁
      (fun y t s hs => hconc ν hprob hexpint hexp y t s hs) hmeanlow x
