/-
Corollary of Section 3 of sandpile.tex, frozen.  `sandpile.tex:1820-1826`
(label `cor:critical-mean-one`, under the standing hypotheses of Subsection
`ssec:expl-d123` stated at `sandpile.tex:1696-1701`):

  "Throughout this subsection, $d\leq3$, the scenery is i.i.d.,
   $\E\zeta(0)=0$, $0<\Var(\zeta(0))<\infty$, and $\E|\zeta(0)|^3<\infty$.

   For every $\gamma\in[0,(4-d)/4)$ there are $C<\infty$ and $\alpha>0$ such
   that, for all $t\geq2$, $\P\bigl(u_t(0)\leq t^\gamma\bigr)\leq Ct^{-\alpha}$."

The scenery `ζ` is carried by its one-site law `ν`, and the field itself by
`centeredMassLaw d ν`, the law of `σ = 1 + 2dζ`.  The corollary claims no
uniformity in the law, so the law is fixed first, as a standing hypothesis of
the subsection; `γ` comes next, and `C` and `α` are bound after `γ` and before
`t`, as the paper orders them.  The probability is stated on the measure of the
event in `ℝ≥0∞`, against `ENNReal.ofReal` of the paper's right-hand side, so
that no `toReal` junk value can weaken it; `t ≥ 2` is the paper's threshold.
Integrability of `|ζ(0)|³` is the standing hypothesis `E|ζ(0)|³ < ∞`.
-/
import Sandpile.Law
import Sandpile.External.BerryEsseen
import Sandpile.External.VarianceScale
import Sandpile.Frozen.CriticalToppling
import Sandpile.Support.CriticalMean

open MeasureTheory ProbabilityTheory Filter Topology

set_option maxHeartbeats 4000000 in
-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.critical_mean_one
    (hBerryEsseen : Sandpile.External.MultivariateBerryEsseen)
    (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hmean : ∫ z, z ∂ν = 0) (hvar : 0 < evariance id ν) (hvar' : evariance id ν < ⊤)
    (hthird : Integrable (fun z => |z| ^ 3) ν)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ' : γ < (4 - (d : ℝ)) / 4) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ t : ℕ, 2 ≤ t →
      Sandpile.centeredMassLaw d ν {σ | Sandpile.odometer σ t 0 ≤ (t : ℝ) ^ γ} ≤
        ENNReal.ofReal (C * (t : ℝ) ^ (-α))
-- FROZEN-STATEMENT-END
:= by
  classical
  have hVarScale : Sandpile.External.VarianceScale := Sandpile.External.varianceScale
  haveI := hprob
  have hne0 : evariance (id : ℝ → ℝ) ν ≠ 0 := ne_of_gt hvar
  have hnetop : evariance (id : ℝ → ℝ) ν ≠ ⊤ := ne_of_lt hvar'
  have hvarR : 0 < variance (id : ℝ → ℝ) ν := by
    show 0 < (evariance (id : ℝ → ℝ) ν).toReal
    exact ENNReal.toReal_pos hne0 hnetop
  have hν₀ : 0 < Real.sqrt (variance (id : ℝ → ℝ) ν) := Real.sqrt_pos.mpr hvarR
  have hν₀sq : ENNReal.ofReal (Real.sqrt (variance (id : ℝ → ℝ) ν) ^ 2)
      ≤ evariance (id : ℝ → ℝ) ν := by
    rw [Real.sq_sqrt hvarR.le]
    show ENNReal.ofReal ((evariance (id : ℝ → ℝ) ν).toReal) ≤ evariance (id : ℝ → ℝ) ν
    rw [ENNReal.ofReal_toReal hnetop]
  have hvpow : 0 < variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hvarR _
  have hM : ∫ z, |z| ^ 3 ∂ν
      ≤ ((∫ z, |z| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2))
        * variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2) := by
    rw [div_mul_cancel₀ _ (ne_of_gt hvpow)]
  -- the exponents
  have hd3R : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 - (d : ℝ) := by linarith
  set δ : ℝ := ((4 : ℝ) - (d : ℝ)) / 4 - γ with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hbinv : (0 : ℝ) < 4 / (4 - (d : ℝ)) := by positivity
  have hdinv : (0 : ℝ) < 1 / δ := by positivity
  set a : ℝ := (1 / 2) * min (4 / (4 - (d : ℝ))) (1 / δ) with hadef
  have hmin0 : (0 : ℝ) < min (4 / (4 - (d : ℝ))) (1 / δ) := lt_min hbinv hdinv
  have ha : 0 < a := by rw [hadef]; linarith
  have hainv : a < 4 / (4 - (d : ℝ)) := by
    have h1 : min (4 / (4 - (d : ℝ))) (1 / δ) ≤ 4 / (4 - (d : ℝ)) := min_le_left _ _
    rw [hadef]; linarith
  have haδ : a * δ ≤ 1 / 2 := by
    have h1 : min (4 / (4 - (d : ℝ))) (1 / δ) ≤ 1 / δ := min_le_right _ _
    have h2 : min (4 / (4 - (d : ℝ))) (1 / δ) * δ ≤ (1 / δ) * δ :=
      mul_le_mul_of_nonneg_right h1 hδ0.le
    have h3 : (1 / δ) * δ = 1 := by field_simp
    have h4 : min (4 / (4 - (d : ℝ))) (1 / δ) * δ ≤ 1 := by linarith
    rw [hadef]; nlinarith [h4]
  obtain ⟨c, C, hc, hC, hb⟩ :=
    Sandpile.Frozen.critical_toppling hBerryEsseen d hd hd3
      (Real.sqrt (variance (id : ℝ → ℝ) ν))
      ((∫ z, |z| ^ 3 ∂ν) / variance (id : ℝ → ℝ) ν ^ ((3 : ℝ) / 2)) hν₀ a ha hainv
  set t₀ : ℕ := max 4 ⌈(2 : ℝ) ^ (1 / δ)⌉₊ with ht₀def
  set α : ℝ := min (c * δ) (1 / 16) with hαdef
  have hα : 0 < α := by rw [hαdef]; exact lt_min (mul_pos hc hδ0) (by norm_num)
  have hα1 : α ≤ c * δ := by rw [hαdef]; exact min_le_left _ _
  have hα2 : α ≤ 1 / 16 := by rw [hαdef]; exact min_le_right _ _
  set Krate : ℝ := max ((12 : ℝ) ^ ((3 : ℝ) / 4)) ((14 : ℝ) ^ ((7 : ℝ) / 4)) with hKdef
  have hKrate : 0 < Krate := by
    rw [hKdef]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) (le_max_left _ _)
  set Cfin : ℝ := max (C + C * Krate) ((t₀ : ℝ) ^ α) with hCfindef
  have hCfin : 0 < Cfin := by
    rw [hCfindef]
    exact lt_of_lt_of_le (by nlinarith [hC, hKrate]) (le_max_left _ _)
  refine ⟨Cfin, α, hCfin, hα, ?_⟩
  intro t ht2
  have ht1 : 1 ≤ t := by omega
  have ht0R : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have ht1R : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have hαrhs : (0 : ℝ) < (t : ℝ) ^ (-α) := Real.rpow_pos_of_pos ht0R _
  by_cases hbig : t₀ ≤ t
  · have ht4 : (4 : ℕ) ≤ t := le_trans (le_max_left _ _) hbig
    have ht3 : 3 ≤ t := by omega
    have hL2 : (2 : ℝ) ≤ (t : ℝ) ^ δ :=
      Sandpile.two_le_rpow_of_ceil_le hδ0 (le_trans (le_max_right _ _) hbig)
    have h4t : (4 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht4
    have hLa : ((t : ℝ) ^ δ) ^ a ≤ (t : ℝ) / 2 := by
      have he : ((t : ℝ) ^ δ) ^ a = (t : ℝ) ^ (δ * a) := (Real.rpow_mul ht0R.le δ a).symm
      rw [he]
      have hexp : δ * a ≤ 1 / 2 := by nlinarith [haδ]
      have h1 : (t : ℝ) ^ (δ * a) ≤ (t : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le ht1R hexp
      have hsq : (t : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (t : ℝ) := (Real.sqrt_eq_rpow _).symm
      have hs2 : (2 : ℝ) ≤ Real.sqrt (t : ℝ) := by
        have h2 : Real.sqrt 4 ≤ Real.sqrt (t : ℝ) := Real.sqrt_le_sqrt h4t
        have h3 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        linarith [h2, h3]
      have hss : Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ) = (t : ℝ) := Real.mul_self_sqrt ht0R.le
      rw [hsq] at h1
      nlinarith [h1, hs2, hss]
    have hevt : (t : ℝ) ^ ((4 - (d : ℝ)) / 4) / ((t : ℝ) ^ δ) = (t : ℝ) ^ γ := by
      rw [← Real.rpow_sub ht0R]
      congr 1
      rw [hδdef]; ring
    have hmain := hb ν hprob hmean hvar hvar' hthird hν₀sq hM t ((t : ℝ) ^ δ) ht3 hL2 hLa
    rw [hevt] at hmain
    refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ((t : ℝ) ^ δ) ^ (-c) ≤ (t : ℝ) ^ (-α) := by
      have hpow1 : ((t : ℝ) ^ δ) ^ (-c) = (t : ℝ) ^ (-(c * δ)) := by
        rw [← Real.rpow_mul ht0R.le]
        congr 1
        ring
      rw [hpow1]
      exact Sandpile.rpow_neg_mono ht1 hα1
    have h2 : Sandpile.lowerTailRemainder d t ((t : ℝ) ^ δ) a ≤ Krate * (t : ℝ) ^ (-α) := by
      rw [Sandpile.lowerTailRemainder]
      by_cases hd2 : d = 2
      · rw [if_pos hd2]
        refine Sandpile.log_power_rate_le ht1 (ε := (1 : ℝ) / 14) (w := (1 : ℝ) / 4)
          (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
        · have e : (1 : ℝ) / ((1 : ℝ) / 14) = 14 := by norm_num
          rw [e, hKdef]
          exact le_max_right _ _
        · exact Real.rpow_nonneg (Real.rpow_nonneg ht0R.le δ) _
        · have he : ((t : ℝ) ^ δ) ^ (a / 2) = (t : ℝ) ^ (δ * (a / 2)) :=
            (Real.rpow_mul ht0R.le _ _).symm
          rw [he]
          exact Real.rpow_le_rpow_of_exponent_le ht1R (by nlinarith [haδ])
        · have e : (1 : ℝ) / 14 * ((7 : ℝ) / 4) + (-(1 : ℝ) / 2) + (1 : ℝ) / 4
              = -((1 : ℝ) / 8) := by norm_num
          rw [e]
          linarith
      · rw [if_neg hd2]
        refine Sandpile.log_power_rate_le ht1 (ε := (1 : ℝ) / 12) (w := (1 : ℝ) / 8)
          (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
        · have e : (1 : ℝ) / ((1 : ℝ) / 12) = 12 := by norm_num
          rw [e, hKdef]
          exact le_max_left _ _
        · exact Real.rpow_nonneg (Real.rpow_nonneg ht0R.le δ) _
        · have he : ((t : ℝ) ^ δ) ^ (a / 4) = (t : ℝ) ^ (δ * (a / 4)) :=
            (Real.rpow_mul ht0R.le _ _).symm
          rw [he]
          exact Real.rpow_le_rpow_of_exponent_le ht1R (by nlinarith [haδ])
        · have e : (1 : ℝ) / 12 * ((3 : ℝ) / 4) + (-(1 : ℝ) / 4) + (1 : ℝ) / 8
              = -((1 : ℝ) / 16) := by norm_num
          rw [e]
          linarith
    have hCle : C + C * Krate ≤ Cfin := by rw [hCfindef]; exact le_max_left _ _
    calc C * ((t : ℝ) ^ δ) ^ (-c) + C * Sandpile.lowerTailRemainder d t ((t : ℝ) ^ δ) a
        ≤ C * (t : ℝ) ^ (-α) + C * (Krate * (t : ℝ) ^ (-α)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hC.le)
            (mul_le_mul_of_nonneg_left h2 hC.le)
      _ = (C + C * Krate) * (t : ℝ) ^ (-α) := by ring
      _ ≤ Cfin * (t : ℝ) ^ (-α) := mul_le_mul_of_nonneg_right hCle hαrhs.le
  · have hlt : t ≤ t₀ := by omega
    have ht0le : (t : ℝ) ≤ (t₀ : ℝ) := by exact_mod_cast hlt
    have ht04 : (4 : ℕ) ≤ t₀ := le_max_left _ _
    have ht02 : (2 : ℝ) ≤ (t₀ : ℝ) := by exact_mod_cast (by omega : (2 : ℕ) ≤ t₀)
    have ht2R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
    have h1le : (1 : ℝ) ≤ (t₀ : ℝ) ^ α * (t : ℝ) ^ (-α) :=
      Sandpile.le_mul_rpow_of_le hα ht02 ht2R ht0le
    have h2le : (t₀ : ℝ) ^ α ≤ Cfin := by rw [hCfindef]; exact le_max_right _ _
    have h3le : (t₀ : ℝ) ^ α * (t : ℝ) ^ (-α) ≤ Cfin * (t : ℝ) ^ (-α) :=
      mul_le_mul_of_nonneg_right h2le hαrhs.le
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
