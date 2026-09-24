/-
The one-dimensional Gaussian inputs of case (a) of
`prop:dgt4-contact-asymptotics`: "The Mills-ratio tail asymptotics for the
mean-zero Gaussian $V_\infty(0)$ give, as $t\to\infty$,
$\E(-V_\infty(0)-t)_+\sim\frac{\Sigma^2}{t}\P(-V_\infty(0)>t)$ and
$-\frac{d}{dt}\P(-V_\infty(0)>t)\sim\frac{t}{\Sigma^2}\P(-V_\infty(0)>t)$"
(`sandpile.tex:4991-5000`).

`gaussianUpperTail v` is the tail `t \mapsto \P(N(0,v)>t)` and `gaussianIntegratedTail v` the
integrated tail `t \mapsto \E(N(0,v)-t)_+`; in case (a) the field `-V_\infty(0)`
is the mean-zero Gaussian of variance `\Sigma^2`, so these are the two
quantities the display names.

`GaussianMillsBounds v` collects the four non-asymptotic Mills bounds and the two
monotonicity bounds for the increment of the tail; the asymptotics the chain of
`Support/Dgt4TailChain.lean` consumes are squeezed out of them here.  All six
are inequalities between explicit one-dimensional Gaussian quantities.
-/
import Sandpile.Support.Dgt4TailChain
import Sandpile.Support.Dgt4CaseSelect

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

/-- The Gaussian tail `Φ(t) = P(N(0,v) > t)`, the law of `-V_∞(0)` in case (a). -/
noncomputable def gaussianUpperTail (v : ℝ≥0) (t : ℝ) : ℝ := (gaussianReal 0 v (Set.Ioi t)).toReal

/-- The integrated Gaussian tail `I(t) = E(N(0,v) - t)_+`, the denominator of
`eq:dgt4-contact-mean-increment`. -/
noncomputable def gaussianIntegratedTail (v : ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, max 0 (x - t) ∂(gaussianReal 0 v)

/-- The Gaussian tail is positive at every level, because the Gaussian law and
Lebesgue measure are mutually absolutely continuous. -/
theorem gaussianUpperTail_pos (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) : 0 < gaussianUpperTail v t := by
  have hac : (volume : Measure ℝ) ≪ gaussianReal 0 v :=
    gaussianReal_absolutelyContinuous' 0 hv
  have hne : gaussianReal 0 v (Set.Ioi t) ≠ 0 := by
    intro h
    have hvol : (volume : Measure ℝ) (Set.Ioi t) = 0 := hac h
    rw [Real.volume_Ioi] at hvol
    exact ENNReal.top_ne_zero hvol
  have hlt : gaussianReal 0 v (Set.Ioi t) ≠ ⊤ := measure_ne_top _ _
  exact ENNReal.toReal_pos hne hlt

/-- The Mills-ratio inequalities for the mean-zero Gaussian of variance `v`.

The first two are the classical two-sided bound
`(v/t - v^2/t^3)\varphi(t)\leq\Phi(t)\leq (v/t)\varphi(t)`, the next two the
corresponding bound for the integrated tail, and the last two say that the
decrement of the tail over `[s, s+d]` lies between `d\varphi(s+d)` and
`d\varphi(s)`.  Together they give the two asymptotics of
`sandpile.tex:4986-4995` and the first-order expansion of the tail used at
`sandpile.tex:5002-5006`. -/
structure GaussianMillsBounds (v : ℝ≥0) : Prop where
  /-- `Φ(t) ≤ (v/t)φ(t)`. -/
  tail_le : ∀ t : ℝ, 0 < t → gaussianUpperTail v t ≤ (v : ℝ) / t * gaussianPDFReal 0 v t
  /-- `(v/t - v²/t³)φ(t) ≤ Φ(t)`. -/
  le_tail : ∀ t : ℝ, 0 < t →
    ((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3) * gaussianPDFReal 0 v t ≤ gaussianUpperTail v t
  /-- `I(t) ≤ v²φ(t)/t²`. -/
  mean_le : ∀ t : ℝ, 0 < t → gaussianIntegratedTail v t ≤ (v : ℝ) ^ 2 * gaussianPDFReal 0 v t / t ^ 2
  /-- `v²φ(t)/(t²+3v) ≤ I(t)`. -/
  le_mean : ∀ t : ℝ, 0 < t →
    (v : ℝ) ^ 2 * gaussianPDFReal 0 v t / (t ^ 2 + 3 * (v : ℝ)) ≤ gaussianIntegratedTail v t
  /-- `Φ(s) - Φ(s+d) ≤ φ(s)d`. -/
  tail_diff_le : ∀ s d : ℝ, 0 ≤ s → 0 < d →
    gaussianUpperTail v s - gaussianUpperTail v (s + d) ≤ gaussianPDFReal 0 v s * d
  /-- `φ(s+d)d ≤ Φ(s) - Φ(s+d)`. -/
  le_tail_diff : ∀ s d : ℝ, 0 ≤ s → 0 < d →
    gaussianPDFReal 0 v (s + d) * d ≤ gaussianUpperTail v s - gaussianUpperTail v (s + d)

/-- Shifting the argument multiplies the Gaussian density by an explicit
exponential factor. -/
theorem gaussianPDFReal_add (v : ℝ≥0) (s d : ℝ) :
    gaussianPDFReal 0 v (s + d)
      = gaussianPDFReal 0 v s * Real.exp (-(2 * s * d + d ^ 2) / (2 * (v : ℝ))) := by
  have hexp : Real.exp (-(s - 0) ^ 2 / (2 * (v : ℝ))) *
      Real.exp (-(2 * s * d + d ^ 2) / (2 * (v : ℝ)))
      = Real.exp (-(s + d - 0) ^ 2 / (2 * (v : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gaussianPDFReal]
  rw [mul_assoc _ (Real.exp (-(s - 0) ^ 2 / (2 * (v : ℝ)))), hexp]

/-- The Gaussian density is bounded by its value at the mean. -/
theorem gaussianPDFReal_le (v : ℝ≥0) (t : ℝ) :
    gaussianPDFReal 0 v t ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by
  have h1 : -(t - 0) ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
  have h2 : (0 : ℝ) ≤ 2 * (v : ℝ) := by positivity
  have hexp : Real.exp (-(t - 0) ^ 2 / (2 * (v : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_iff.mpr (Or.inr ⟨h1, h2⟩))
  have hc : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
  calc gaussianPDFReal 0 v t
      = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(t - 0) ^ 2 / (2 * (v : ℝ))) := rfl
    _ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hc
    _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := mul_one _

/-- The Gaussian tail vanishes at infinity. -/
theorem tendsto_gaussianUpperTail_zero (v : ℝ≥0) (hv : v ≠ 0) (h : GaussianMillsBounds v) :
    Tendsto (gaussianUpperTail v) atTop (𝓝 0) := by
  set c : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hcdef
  have hid : Tendsto (fun t : ℝ => t) atTop atTop := tendsto_id
  have hlim : Tendsto (fun t : ℝ => (v : ℝ) * c / t) atTop (𝓝 0) := hid.const_div_atTop _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with t using (gaussianUpperTail_pos v hv t).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    refine le_trans (h.tail_le t ht) ?_
    have hpdf : gaussianPDFReal 0 v t ≤ c := gaussianPDFReal_le v t
    have hvt : (0 : ℝ) ≤ (v : ℝ) / t := by positivity
    calc (v : ℝ) / t * gaussianPDFReal 0 v t ≤ (v : ℝ) / t * c :=
          mul_le_mul_of_nonneg_left hpdf hvt
      _ = (v : ℝ) * c / t := by ring

/-- `0 < v` in the reals. -/
theorem coe_pos_of_ne_zero {v : ℝ≥0} (hv : v ≠ 0) : (0 : ℝ) < (v : ℝ) := by
  have : 0 < v := pos_iff_ne_zero.mpr hv
  exact_mod_cast this

/-- The Mills ratio for the Gaussian tail, `sandpile.tex:4993-4995`. -/
theorem tendsto_gaussMills_tail (v : ℝ≥0) (hv : v ≠ 0) (h : GaussianMillsBounds v) :
    Tendsto (fun t : ℝ => (v : ℝ) * gaussianPDFReal 0 v t / (t * gaussianUpperTail v t))
      atTop (𝓝 1) :=
  tendsto_mills_tail (coe_pos_of_ne_zero hv) (fun t => gaussianPDFReal_pos 0 v t hv)
    h.tail_le h.le_tail (tendsto_inv_one_sub_div_sq _)

/-- The Mills ratio for the integrated Gaussian tail, `sandpile.tex:4990-4992`. -/
theorem tendsto_gaussMills_mean (v : ℝ≥0) (hv : v ≠ 0) (h : GaussianMillsBounds v) :
    Tendsto (fun t : ℝ => t * gaussianIntegratedTail v t / ((v : ℝ) * gaussianUpperTail v t)) atTop (𝓝 1) :=
  tendsto_mills_mean (coe_pos_of_ne_zero hv) (fun t => gaussianPDFReal_pos 0 v t hv)
    h.tail_le h.le_tail h.mean_le h.le_mean
    (tendsto_inv_one_add_div_sq (3 * (v : ℝ))) (tendsto_inv_one_sub_div_sq _)

/-- The first-order expansion of the Gaussian tail, `sandpile.tex:5002-5006`. -/
theorem tendsto_gaussianUpperTail_expansion (v : ℝ≥0) (hv : v ≠ 0) (h : GaussianMillsBounds v)
    {t dl : ℕ → ℝ} (htnn : ∀ᶠ n in atTop, 0 ≤ t n) (hdl : ∀ᶠ n in atTop, 0 < dl n)
    (htd : Tendsto (fun n : ℕ => t n * dl n) atTop (𝓝 0))
    (hd0 : Tendsto dl atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (gaussianUpperTail v (t n) - gaussianUpperTail v (t n + dl n)) /
        (gaussianPDFReal 0 v (t n) * dl n)) atTop (𝓝 1) :=
  tendsto_tail_expansion (v := (v : ℝ)) (fun s => gaussianPDFReal_pos 0 v s hv) htnn
    h.le_tail_diff h.tail_diff_le (gaussianPDFReal_add v) hdl htd hd0

/-- The derivative of the Gaussian density: `\varphi'(x)=-(x/v)\varphi(x)`. -/
theorem hasDerivAt_gaussianPDF (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) x := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hbase : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ))) (-(2 * x) / (2 * (v : ℝ))) x :=
    hbase.neg.div_const _
  have h2 : -(2 * x) / (2 * (v : ℝ)) = -(x / (v : ℝ)) := by field_simp
  rw [h2] at h1
  have hq : HasDerivAt (fun y : ℝ => -(y - (0 : ℝ)) ^ 2 / (2 * (v : ℝ)))
      (-(x / (v : ℝ))) x := by simpa using h1
  have he : HasDerivAt (fun y : ℝ => Real.exp (-(y - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))))
      (Real.exp (-(x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))) * -(x / (v : ℝ))) x := hq.exp
  have hc := he.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  have heq : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
      (Real.exp (-(x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))) * -(x / (v : ℝ)))
      = -(x / (v : ℝ)) * gaussianPDFReal 0 v x := by
    show _ = -(x / (v : ℝ)) *
      ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))))
    ring
  rw [heq] at hc
  exact hc

/-- The Gaussian density vanishes at infinity. -/
theorem tendsto_gaussianPDF_zero (v : ℝ≥0) (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal 0 v) atTop (𝓝 0) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have h2 : Tendsto (fun x : ℝ => (x - (0 : ℝ)) ^ 2) atTop atTop := by
    simp only [sub_zero]
    exact tendsto_pow_atTop (by norm_num)
  have h1 : Tendsto (fun x : ℝ => (x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))) atTop atTop :=
    h2.atTop_div_const (by positivity)
  have hsq : Tendsto (fun x : ℝ => -(x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp h1
    simpa [Function.comp_def, neg_div] using h
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(x - (0 : ℝ)) ^ 2 / (2 * (v : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using Real.tendsto_exp_atBot.comp hsq
  have hc := hexp.const_mul (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  rw [mul_zero] at hc
  exact hc

/-- The tail is the integral of the density over the half-line. -/
theorem upperTail_eq_setIntegral (v : ℝ≥0) (hv : v ≠ 0) (t : ℝ) :
    gaussianUpperTail v t = ∫ s in Set.Ioi t, gaussianPDFReal 0 v s := by
  rw [gaussianUpperTail, gaussianReal_apply_eq_integral 0 hv (Set.Ioi t),
    ENNReal.toReal_ofReal (integral_nonneg fun s => gaussianPDFReal_nonneg 0 v s)]

theorem integrable_mul_gaussianPDFReal (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun s : ℝ => s * gaussianPDFReal 0 v s) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hb : (0 : ℝ) < 1 / (2 * (v : ℝ)) := by positivity
  have h := (integrable_mul_exp_neg_mul_sq hb).const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  have hexp : -(1 / (2 * (v : ℝ))) * s ^ 2 = -(s - 0) ^ 2 / (2 * (v : ℝ)) := by
    rw [sub_zero]
    field_simp
  simp only [gaussianPDFReal, hexp]
  ring

theorem integral_Ioi_mul_gaussianPDFReal (v : ℝ≥0) (hv : v ≠ 0) (a : ℝ) :
    ∫ s in Set.Ioi a, s / (v : ℝ) * gaussianPDFReal 0 v s = gaussianPDFReal 0 v a := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hderiv : ∀ x ∈ Set.Ici a, HasDerivAt (fun s : ℝ => -gaussianPDFReal 0 v s)
      (x / (v : ℝ) * gaussianPDFReal 0 v x) x := by
    intro x _
    have h := (hasDerivAt_gaussianPDF v hv x).neg
    have heq : -(-(x / (v : ℝ)) * gaussianPDFReal 0 v x)
        = x / (v : ℝ) * gaussianPDFReal 0 v x := by ring
    rw [heq] at h
    exact h
  have hint : IntegrableOn (fun s : ℝ => s / (v : ℝ) * gaussianPDFReal 0 v s) (Set.Ioi a) := by
    have h := (integrable_mul_gaussianPDFReal v hv).const_mul ((v : ℝ)⁻¹)
    refine (h.congr (Filter.Eventually.of_forall fun s => ?_)).integrableOn
    field_simp
  have hf : Tendsto (fun s : ℝ => -gaussianPDFReal 0 v s) atTop (𝓝 0) := by
    have h := (tendsto_gaussianPDF_zero v hv).neg
    simpa using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hf
  simpa using h

/-- The density divided by a positive power is integrable on a half-line away from
the origin. -/
theorem integrableOn_div_pow_mul_pdf (v : ℝ≥0) {a : ℝ} (ha : 0 < a) (c : ℝ) (k : ℕ) :
    IntegrableOn (fun s : ℝ => c * gaussianPDFReal 0 v s / s ^ k) (Set.Ioi a) := by
  have hint : IntegrableOn (fun s : ℝ => |c| / a ^ k * gaussianPDFReal 0 v s) (Set.Ioi a) :=
    ((integrable_gaussianPDFReal 0 v).const_mul _).integrableOn
  refine Integrable.mono' hint (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hsa : a < s := hs
  have hs0 : (0 : ℝ) < s := lt_trans ha hsa
  have hak : a ^ k ≤ s ^ k := pow_le_pow_left₀ ha.le hsa.le k
  have hpk : (0 : ℝ) < a ^ k := by positivity
  have hsk : (0 : ℝ) < s ^ k := by positivity
  have hphi : (0 : ℝ) ≤ gaussianPDFReal 0 v s := gaussianPDFReal_nonneg 0 v s
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hphi, abs_of_nonneg hsk.le]
  calc |c| * gaussianPDFReal 0 v s / s ^ k
      ≤ |c| * gaussianPDFReal 0 v s / a ^ k :=
        div_le_div_of_nonneg_left (by positivity) hpk hak
    _ = |c| / a ^ k * gaussianPDFReal 0 v s := by ring

theorem hasDerivAt_millsAux (v : ℝ≥0) (hv : v ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun r : ℝ => -((v : ℝ) / r * gaussianPDFReal 0 v r))
      (gaussianPDFReal 0 v s + (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s) s := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hinv : HasDerivAt (fun r : ℝ => r⁻¹) (-(s ^ 2)⁻¹) s := hasDerivAt_inv hs
  have h1 : HasDerivAt (fun r : ℝ => (v : ℝ) * r⁻¹) ((v : ℝ) * -(s ^ 2)⁻¹) s :=
    hinv.const_mul _
  have key := (h1.mul (hasDerivAt_gaussianPDF v hv s)).neg
  have heq : -((v : ℝ) * -(s ^ 2)⁻¹ * gaussianPDFReal 0 v s
      + (v : ℝ) * s⁻¹ * (-(s / (v : ℝ)) * gaussianPDFReal 0 v s))
      = gaussianPDFReal 0 v s + (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s := by
    field_simp
    ring
  rw [heq] at key
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  simp [div_eq_mul_inv]

theorem hasDerivAt_millsAux3 (v : ℝ≥0) (hv : v ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun r : ℝ => -((v : ℝ) / r ^ 3 * gaussianPDFReal 0 v r))
      (gaussianPDFReal 0 v s / s ^ 2 + 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4) s := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hcube : HasDerivAt (fun r : ℝ => r ^ 3) (3 * s ^ 2) s := by
    simpa using hasDerivAt_pow 3 s
  have hne : s ^ 3 ≠ 0 := pow_ne_zero 3 hs
  have hinv : HasDerivAt (fun r : ℝ => (r ^ 3)⁻¹) (-(3 * s ^ 2) / (s ^ 3) ^ 2) s :=
    hcube.inv hne
  have h1 : HasDerivAt (fun r : ℝ => (v : ℝ) * (r ^ 3)⁻¹)
      ((v : ℝ) * (-(3 * s ^ 2) / (s ^ 3) ^ 2)) s := hinv.const_mul _
  have key := (h1.mul (hasDerivAt_gaussianPDF v hv s)).neg
  have heq : -((v : ℝ) * (-(3 * s ^ 2) / (s ^ 3) ^ 2) * gaussianPDFReal 0 v s
      + (v : ℝ) * (s ^ 3)⁻¹ * (-(s / (v : ℝ)) * gaussianPDFReal 0 v s))
      = gaussianPDFReal 0 v s / s ^ 2 + 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4 := by
    field_simp
    ring
  rw [heq] at key
  refine key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)
  simp [div_eq_mul_inv]

/-- The two fundamental-theorem identities behind the Mills bounds: the
antiderivatives are `-(v/s)\varphi(s)` and `-(v/s^3)\varphi(s)`. -/
theorem integral_Ioi_millsAux (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    ∫ s in Set.Ioi a, (gaussianPDFReal 0 v s + (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s)
      = (v : ℝ) / a * gaussianPDFReal 0 v a := by
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun r : ℝ => -((v : ℝ) / r * gaussianPDFReal 0 v r))
        (gaussianPDFReal 0 v x + (v : ℝ) / x ^ 2 * gaussianPDFReal 0 v x) x := by
    intro x hx
    exact hasDerivAt_millsAux v hv (ne_of_gt (lt_of_lt_of_le ha hx))
  have hint : IntegrableOn
      (fun s : ℝ => gaussianPDFReal 0 v s + (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s)
      (Set.Ioi a) := by
    refine ((integrable_gaussianPDFReal 0 v).integrableOn).add ?_
    exact (integrableOn_div_pow_mul_pdf v ha (v : ℝ) 2).congr
      (Filter.Eventually.of_forall fun s => by ring)
  have hdiv : Tendsto (fun r : ℝ => (v : ℝ) / r) atTop (𝓝 0) := tendsto_id.const_div_atTop _
  have hf : Tendsto (fun r : ℝ => -((v : ℝ) / r * gaussianPDFReal 0 v r)) atTop (𝓝 0) := by
    have h := (hdiv.mul (tendsto_gaussianPDF_zero v hv)).neg
    simpa using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hf
  simpa using h

theorem integral_Ioi_millsAux3 (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    ∫ s in Set.Ioi a, (gaussianPDFReal 0 v s / s ^ 2
        + 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4)
      = (v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a := by
  have hderiv : ∀ x ∈ Set.Ici a,
      HasDerivAt (fun r : ℝ => -((v : ℝ) / r ^ 3 * gaussianPDFReal 0 v r))
        (gaussianPDFReal 0 v x / x ^ 2 + 3 * (v : ℝ) * gaussianPDFReal 0 v x / x ^ 4) x := by
    intro x hx
    exact hasDerivAt_millsAux3 v hv (ne_of_gt (lt_of_lt_of_le ha hx))
  have hint : IntegrableOn
      (fun s : ℝ => gaussianPDFReal 0 v s / s ^ 2
        + 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4) (Set.Ioi a) := by
    refine Integrable.add ?_ ?_
    · exact (integrableOn_div_pow_mul_pdf v ha 1 2).congr
        (Filter.Eventually.of_forall fun s => by ring)
    · exact (integrableOn_div_pow_mul_pdf v ha (3 * (v : ℝ)) 4).congr
        (Filter.Eventually.of_forall fun s => by ring)
  have hcube : Tendsto (fun r : ℝ => r ^ 3) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hdiv : Tendsto (fun r : ℝ => (v : ℝ) / r ^ 3) atTop (𝓝 0) := hcube.const_div_atTop _
  have hf : Tendsto (fun r : ℝ => -((v : ℝ) / r ^ 3 * gaussianPDFReal 0 v r)) atTop (𝓝 0) := by
    have h := (hdiv.mul (tendsto_gaussianPDF_zero v hv)).neg
    simpa using h
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hf
  simpa using h

/-- The two-sided Mills bound for the tail, from the first identity. -/
theorem integrableOn_pdf_Ioi (v : ℝ≥0) (a : ℝ) :
    IntegrableOn (gaussianPDFReal 0 v) (Set.Ioi a) :=
  (integrable_gaussianPDFReal 0 v).integrableOn

theorem integrableOn_weight_Ioi (v : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s) (Set.Ioi a) :=
  (integrableOn_div_pow_mul_pdf v ha (v : ℝ) 2).congr
    (Filter.Eventually.of_forall fun s => by ring)

theorem upperTail_add_weight (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    gaussianUpperTail v a + ∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s
      = (v : ℝ) / a * gaussianPDFReal 0 v a := by
  rw [upperTail_eq_setIntegral v hv a,
    ← integral_add (integrableOn_pdf_Ioi v a) (integrableOn_weight_Ioi v ha)]
  exact integral_Ioi_millsAux v hv ha

theorem weight_nonneg (v : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := lt_trans ha hs
  have := gaussianPDFReal_nonneg 0 v s
  positivity

theorem upperTail_le_mills (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    gaussianUpperTail v a ≤ (v : ℝ) / a * gaussianPDFReal 0 v a := by
  have h := upperTail_add_weight v hv ha
  have hnn := weight_nonneg v ha
  linarith

theorem weight_le (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    (∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s)
      ≤ (v : ℝ) / a ^ 2 * gaussianUpperTail v a := by
  have hmono : (∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s)
      ≤ ∫ s in Set.Ioi a, (v : ℝ) / a ^ 2 * gaussianPDFReal 0 v s := by
    refine setIntegral_mono_on (integrableOn_weight_Ioi v ha)
      ((integrableOn_pdf_Ioi v a).const_mul _) measurableSet_Ioi fun s hs => ?_
    have hsa : a < s := hs
    have hs0 : (0 : ℝ) < s := lt_trans ha hsa
    have hphi := gaussianPDFReal_nonneg 0 v s
    have hv2 : (0 : ℝ) ≤ (v : ℝ) := (v : ℝ≥0).coe_nonneg
    have hle : (v : ℝ) / s ^ 2 ≤ (v : ℝ) / a ^ 2 :=
      div_le_div_of_nonneg_left hv2 (by positivity) (by nlinarith)
    exact mul_le_mul_of_nonneg_right hle hphi
  calc (∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s)
      ≤ ∫ s in Set.Ioi a, (v : ℝ) / a ^ 2 * gaussianPDFReal 0 v s := hmono
    _ = (v : ℝ) / a ^ 2 * gaussianUpperTail v a := by
        rw [integral_const_mul, upperTail_eq_setIntegral v hv a]

theorem mills_le_upperTail (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    ((v : ℝ) / a - (v : ℝ) ^ 2 / a ^ 3) * gaussianPDFReal 0 v a ≤ gaussianUpperTail v a := by
  have h := upperTail_add_weight v hv ha
  have hle := weight_le v hv ha
  have hup := upperTail_le_mills v hv ha
  have hv2 : (0 : ℝ) ≤ (v : ℝ) := (v : ℝ≥0).coe_nonneg
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hkey : (v : ℝ) / a ^ 2 * gaussianUpperTail v a
      ≤ (v : ℝ) / a ^ 2 * ((v : ℝ) / a * gaussianPDFReal 0 v a) :=
    mul_le_mul_of_nonneg_left hup (by positivity)
  have hid : (v : ℝ) / a ^ 2 * ((v : ℝ) / a * gaussianPDFReal 0 v a)
      = (v : ℝ) ^ 2 / a ^ 3 * gaussianPDFReal 0 v a := by
    field_simp
  rw [hid] at hkey
  have : (v : ℝ) / a * gaussianPDFReal 0 v a
      = gaussianUpperTail v a + ∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s := h.symm
  nlinarith [hle, hkey]

/-- The integrated tail through the tail: `I(a)=v\varphi(a)-a\Phi(a)`, and hence
`I(a)=a\int_a^\infty v\varphi(s)/s^2\,ds`. -/
theorem integratedTail_eq (v : ℝ≥0) (hv : v ≠ 0) (a : ℝ) :
    gaussianIntegratedTail v a
      = (v : ℝ) * gaussianPDFReal 0 v a - a * gaussianUpperTail v a := by
  have hvne : ((v : ℝ)) ≠ 0 := (coe_pos_of_ne_zero hv).ne'
  have h1 : gaussianIntegratedTail v a = ∫ x, gaussianPDFReal 0 v x * max 0 (x - a) := by
    rw [gaussianIntegratedTail, integral_gaussianReal_eq_integral_smul hv]
    simp [smul_eq_mul]
  have h2 : (fun x : ℝ => gaussianPDFReal 0 v x * max 0 (x - a))
      = Set.indicator (Set.Ioi a) (fun x => gaussianPDFReal 0 v x * (x - a)) := by
    funext x
    by_cases hx : a < x
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hx), max_eq_right (by linarith : (0 : ℝ) ≤ x - a)]
    · rw [Set.indicator_of_notMem (by simpa using not_lt.mp hx), max_eq_left (by linarith [not_lt.mp hx] : x - a ≤ 0),
        mul_zero]
  have hA : IntegrableOn (fun x : ℝ => x * gaussianPDFReal 0 v x) (Set.Ioi a) :=
    (integrable_mul_gaussianPDFReal v hv).integrableOn
  have hB : IntegrableOn (fun x : ℝ => a * gaussianPDFReal 0 v x) (Set.Ioi a) :=
    (integrableOn_pdf_Ioi v a).const_mul _
  have h3 : (∫ x in Set.Ioi a, gaussianPDFReal 0 v x * (x - a))
      = (∫ x in Set.Ioi a, x * gaussianPDFReal 0 v x)
        - ∫ x in Set.Ioi a, a * gaussianPDFReal 0 v x := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have h4 : (∫ x in Set.Ioi a, x * gaussianPDFReal 0 v x) = (v : ℝ) * gaussianPDFReal 0 v a := by
    have hkey := integral_Ioi_mul_gaussianPDFReal v hv a
    calc (∫ x in Set.Ioi a, x * gaussianPDFReal 0 v x)
        = ∫ x in Set.Ioi a, (v : ℝ) * (x / (v : ℝ) * gaussianPDFReal 0 v x) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
          field_simp
      _ = (v : ℝ) * ∫ x in Set.Ioi a, x / (v : ℝ) * gaussianPDFReal 0 v x := integral_const_mul _ _
      _ = (v : ℝ) * gaussianPDFReal 0 v a := by rw [hkey]
  have h5 : (∫ x in Set.Ioi a, a * gaussianPDFReal 0 v x) = a * gaussianUpperTail v a := by
    rw [integral_const_mul, upperTail_eq_setIntegral v hv a]
  rw [h1, h2, integral_indicator measurableSet_Ioi, h3, h4, h5]

theorem integratedTail_eq_mul_weight (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    gaussianIntegratedTail v a
      = a * ∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s := by
  have h1 := integratedTail_eq v hv a
  have h2 := upperTail_add_weight v hv ha
  have hane : a ≠ 0 := ha.ne'
  have h3 : gaussianUpperTail v a = (v : ℝ) / a * gaussianPDFReal 0 v a
      - ∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s := by linarith
  rw [h1, h3]
  field_simp
  ring

/-- The two-sided Mills bound for the integrated tail, from the second identity. -/
theorem integrableOn_pdf_div_sq (v : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => gaussianPDFReal 0 v s / s ^ 2) (Set.Ioi a) :=
  (integrableOn_div_pow_mul_pdf v ha 1 2).congr (Filter.Eventually.of_forall fun s => by ring)

theorem integrableOn_pdf_div_four (v : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4) (Set.Ioi a) :=
  (integrableOn_div_pow_mul_pdf v ha (3 * (v : ℝ)) 4).congr
    (Filter.Eventually.of_forall fun s => by ring)

theorem weight_eq_const_mul (v : ℝ≥0) (a : ℝ) :
    (∫ s in Set.Ioi a, (v : ℝ) / s ^ 2 * gaussianPDFReal 0 v s)
      = (v : ℝ) * ∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2 := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  ring

theorem weight3_identity (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    (∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2)
      + ∫ s in Set.Ioi a, 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4
      = (v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a := by
  rw [← integral_add (integrableOn_pdf_div_sq v ha) (integrableOn_pdf_div_four v ha)]
  exact integral_Ioi_millsAux3 v hv ha

theorem integral_pdf_div_four_nonneg (v : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    0 ≤ ∫ s in Set.Ioi a, 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4 := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := lt_trans ha hs
  have hphi := gaussianPDFReal_nonneg 0 v s
  have hv2 : (0 : ℝ) ≤ (v : ℝ) := (v : ℝ≥0).coe_nonneg
  positivity

theorem integral_pdf_div_four_le (v : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    (∫ s in Set.Ioi a, 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4)
      ≤ 3 * (v : ℝ) / a ^ 2 * ∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2 := by
  have hmono : (∫ s in Set.Ioi a, 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4)
      ≤ ∫ s in Set.Ioi a, 3 * (v : ℝ) / a ^ 2 * (gaussianPDFReal 0 v s / s ^ 2) := by
    refine setIntegral_mono_on (integrableOn_pdf_div_four v ha)
      ((integrableOn_pdf_div_sq v ha).const_mul _) measurableSet_Ioi fun s hs => ?_
    have hsa : a < s := hs
    have hs0 : (0 : ℝ) < s := lt_trans ha hsa
    have hphi := gaussianPDFReal_nonneg 0 v s
    have hv2 : (0 : ℝ) ≤ (v : ℝ) := (v : ℝ≥0).coe_nonneg
    have ha2 : a ^ 2 ≤ s ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < s ^ 4)]
    have hexp : 3 * (v : ℝ) / a ^ 2 * (gaussianPDFReal 0 v s / s ^ 2) * s ^ 4
        = 3 * (v : ℝ) * gaussianPDFReal 0 v s * (s ^ 2 / a ^ 2) := by
      field_simp
    rw [hexp]
    have hratio : (1 : ℝ) ≤ s ^ 2 / a ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hv2) hphi]
  calc (∫ s in Set.Ioi a, 3 * (v : ℝ) * gaussianPDFReal 0 v s / s ^ 4)
      ≤ ∫ s in Set.Ioi a, 3 * (v : ℝ) / a ^ 2 * (gaussianPDFReal 0 v s / s ^ 2) := hmono
    _ = 3 * (v : ℝ) / a ^ 2 * ∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2 :=
        integral_const_mul _ _



theorem integratedTail_le_mills (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    gaussianIntegratedTail v a ≤ (v : ℝ) ^ 2 * gaussianPDFReal 0 v a / a ^ 2 := by
  have hv2 : (0 : ℝ) ≤ (v : ℝ) := (v : ℝ≥0).coe_nonneg
  have hI := integratedTail_eq_mul_weight v hv ha
  have hid := weight3_identity v hv ha
  have hJ4 := integral_pdf_div_four_nonneg v ha
  have hJ2 : (∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2)
      ≤ (v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a := by linarith
  rw [hI, weight_eq_const_mul v a]
  have hstep : a * ((v : ℝ) * (∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2))
      ≤ a * ((v : ℝ) * ((v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a)) := by
    have hav : (0 : ℝ) ≤ a * (v : ℝ) := by positivity
    nlinarith
  have heq : a * ((v : ℝ) * ((v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a))
      = (v : ℝ) ^ 2 * gaussianPDFReal 0 v a / a ^ 2 := by
    field_simp
  rw [heq] at hstep
  exact hstep

theorem mills_le_integratedTail (v : ℝ≥0) (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) :
    (v : ℝ) ^ 2 * gaussianPDFReal 0 v a / (a ^ 2 + 3 * (v : ℝ))
      ≤ gaussianIntegratedTail v a := by
  have hv2 : (0 : ℝ) ≤ (v : ℝ) := (v : ℝ≥0).coe_nonneg
  have hI := integratedTail_eq_mul_weight v hv ha
  have hid := weight3_identity v hv ha
  have hJ4le := integral_pdf_div_four_le v ha
  set J2 := ∫ s in Set.Ioi a, gaussianPDFReal 0 v s / s ^ 2 with hJ2def
  have hRpos : (0 : ℝ) < (a ^ 2 + 3 * (v : ℝ)) / a ^ 2 := by positivity
  have hsum : (v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a ≤ J2 * ((a ^ 2 + 3 * (v : ℝ)) / a ^ 2) := by
    have hexp : J2 * ((a ^ 2 + 3 * (v : ℝ)) / a ^ 2) = J2 + 3 * (v : ℝ) / a ^ 2 * J2 := by
      field_simp
    rw [hexp]
    linarith
  have hJ2ge : ((v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a) / ((a ^ 2 + 3 * (v : ℝ)) / a ^ 2) ≤ J2 :=
    (div_le_iff₀ hRpos).mpr hsum
  rw [hI, weight_eq_const_mul v a, ← hJ2def]
  have hfin : (v : ℝ) ^ 2 * gaussianPDFReal 0 v a / (a ^ 2 + 3 * (v : ℝ))
      = a * ((v : ℝ) * (((v : ℝ) / a ^ 3 * gaussianPDFReal 0 v a)
          / ((a ^ 2 + 3 * (v : ℝ)) / a ^ 2))) := by
    field_simp
  rw [hfin]
  have hav : (0 : ℝ) ≤ a * (v : ℝ) := by positivity
  nlinarith [hJ2ge]

/-- The increment of the tail over `[s,s+d]`, between `d\varphi(s+d)` and
`d\varphi(s)` by monotonicity of the density on the half-line. -/
theorem gaussianPDFReal_antitone (v : ℝ≥0) (hv : v ≠ 0) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gaussianPDFReal 0 v y ≤ gaussianPDFReal 0 v x := by
  have h2v : (0 : ℝ) < 2 * (v : ℝ) := by
    have := coe_pos_of_ne_zero hv
    positivity
  have hc : (0 : ℝ) ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ := by positivity
  have hexp : Real.exp (-(y - 0) ^ 2 / (2 * (v : ℝ)))
      ≤ Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff₀ h2v h2v]
    have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) h2v.le]
  calc gaussianPDFReal 0 v y
      = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * (v : ℝ))) := rfl
    _ ≤ (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (v : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hc
    _ = gaussianPDFReal 0 v x := rfl

theorem upperTail_sub_eq (v : ℝ≥0) (hv : v ≠ 0) (s d : ℝ) (hd : 0 < d) :
    gaussianUpperTail v s - gaussianUpperTail v (s + d)
      = ∫ x in Set.Ioc s (s + d), gaussianPDFReal 0 v x := by
  have hsd : s ≤ s + d := by linarith
  have hdisj : Disjoint (Set.Ioc s (s + d)) (Set.Ioi (s + d)) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx')
  have hsplit : Set.Ioc s (s + d) ∪ Set.Ioi (s + d) = Set.Ioi s :=
    Set.Ioc_union_Ioi_eq_Ioi hsd
  have hI : (∫ x in Set.Ioi s, gaussianPDFReal 0 v x)
      = (∫ x in Set.Ioc s (s + d), gaussianPDFReal 0 v x)
        + ∫ x in Set.Ioi (s + d), gaussianPDFReal 0 v x := by
    rw [← hsplit]
    exact setIntegral_union hdisj measurableSet_Ioi
      ((integrable_gaussianPDFReal 0 v).integrableOn)
      ((integrable_gaussianPDFReal 0 v).integrableOn)
  rw [upperTail_eq_setIntegral v hv s, upperTail_eq_setIntegral v hv (s + d), hI]
  ring

theorem volume_real_Ioc_add (s d : ℝ) (hd : 0 < d) :
    (volume : Measure ℝ).real (Set.Ioc s (s + d)) = d := by
  rw [Real.volume_real_Ioc]
  rw [show s + d - s = d by ring, max_eq_left hd.le]

theorem upperTail_sub_le (v : ℝ≥0) (hv : v ≠ 0) {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    gaussianUpperTail v s - gaussianUpperTail v (s + d) ≤ gaussianPDFReal 0 v s * d := by
  rw [upperTail_sub_eq v hv s d hd]
  have hmono : (∫ x in Set.Ioc s (s + d), gaussianPDFReal 0 v x)
      ≤ ∫ _x in Set.Ioc s (s + d), gaussianPDFReal 0 v s := by
    refine setIntegral_mono_on ((integrable_gaussianPDFReal 0 v).integrableOn)
      (integrableOn_const (by simp)) measurableSet_Ioc fun x hx => ?_
    exact gaussianPDFReal_antitone v hv hs (le_of_lt hx.1)
  calc (∫ x in Set.Ioc s (s + d), gaussianPDFReal 0 v x)
      ≤ ∫ _x in Set.Ioc s (s + d), gaussianPDFReal 0 v s := hmono
    _ = gaussianPDFReal 0 v s * d := by
        rw [setIntegral_const, volume_real_Ioc_add s d hd, smul_eq_mul, mul_comm]

theorem le_upperTail_sub (v : ℝ≥0) (hv : v ≠ 0) {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) :
    gaussianPDFReal 0 v (s + d) * d
      ≤ gaussianUpperTail v s - gaussianUpperTail v (s + d) := by
  rw [upperTail_sub_eq v hv s d hd]
  have hmono : (∫ _x in Set.Ioc s (s + d), gaussianPDFReal 0 v (s + d))
      ≤ ∫ x in Set.Ioc s (s + d), gaussianPDFReal 0 v x := by
    refine setIntegral_mono_on (integrableOn_const (by simp))
      ((integrable_gaussianPDFReal 0 v).integrableOn) measurableSet_Ioc fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := le_trans hs (le_of_lt hx.1)
    exact gaussianPDFReal_antitone v hv hx0 hx.2
  calc gaussianPDFReal 0 v (s + d) * d
      = ∫ _x in Set.Ioc s (s + d), gaussianPDFReal 0 v (s + d) := by
        rw [setIntegral_const, volume_real_Ioc_add s d hd, smul_eq_mul, mul_comm]
    _ ≤ ∫ x in Set.Ioc s (s + d), gaussianPDFReal 0 v x := hmono

/-- Every nondegenerate one-dimensional Gaussian satisfies the six Mills bounds.  This
is what makes the Gaussian case of `prop:dgt4-contact-asymptotics` unconditional in
`sandpile.tex:4986-4995` and `sandpile.tex:5002-5006`. -/
theorem gaussianMillsBounds (v : ℝ≥0) (hv : v ≠ 0) : GaussianMillsBounds v where
  tail_le := fun _ ht => upperTail_le_mills v hv ht
  le_tail := fun _ ht => mills_le_upperTail v hv ht
  mean_le := fun _ ht => integratedTail_le_mills v hv ht
  le_mean := fun _ ht => mills_le_integratedTail v hv ht
  tail_diff_le := fun _ _ hs hd => upperTail_sub_le v hv hs hd
  le_tail_diff := fun _ _ hs hd => le_upperTail_sub v hv hs hd

/-- `eq:dgt4-gaussian-density-ratio` (`sandpile.tex:5265-5271`): the density of
`-V_\infty(0)` in the variable `y`, normalised by the exceedance probability at the
threshold, converges to `e^{-y}`. -/
theorem tendsto_density_ratio (v : ℝ≥0) (hv : v ≠ 0) (y : ℝ) :
    Tendsto (fun t : ℝ => (v : ℝ) / t * gaussianPDFReal 0 v (t + (v : ℝ) * y / t)
        / gaussianUpperTail v t) atTop (𝓝 (Real.exp (-y))) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hmills := tendsto_gaussMills_tail v hv (gaussianMillsBounds v hv)
  have h0 : Tendsto (fun t : ℝ => ((v : ℝ) * y / t) ^ 2) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => (v : ℝ) * y / t) atTop (𝓝 0) := tendsto_id.const_div_atTop _
    simpa using h.pow 2
  have h1 : Tendsto (fun t : ℝ => -y - ((v : ℝ) * y / t) ^ 2 / (2 * (v : ℝ)))
      atTop (𝓝 (-y)) := by
    have h := h0.div_const (2 * (v : ℝ))
    simpa using tendsto_const_nhds.sub h
  have hinner : Tendsto (fun t : ℝ =>
      -(2 * t * ((v : ℝ) * y / t) + ((v : ℝ) * y / t) ^ 2) / (2 * (v : ℝ)))
      atTop (𝓝 (-y)) := by
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have htne : t ≠ 0 := ht.ne'
    field_simp
    ring
  have hexp : Tendsto (fun t : ℝ =>
      Real.exp (-(2 * t * ((v : ℝ) * y / t) + ((v : ℝ) * y / t) ^ 2) / (2 * (v : ℝ))))
      atTop (𝓝 (Real.exp (-y))) := by
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto (-y)).comp hinner
  have hprod := hexp.mul hmills
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have htne : t ≠ 0 := ht.ne'
  rw [gaussianPDFReal_add v t ((v : ℝ) * y / t)]
  have hphi : gaussianPDFReal 0 v t ≠ 0 := (gaussianPDFReal_pos 0 v t hv).ne'
  have hUT : gaussianUpperTail v t ≠ 0 := (gaussianUpperTail_pos v hv t).ne'
  field_simp

/-- The integral that Step 4 of case (a) evaluates at `sandpile.tex:5294-5297`:
`\int_0^\infty y e^{-y}\,dy = 1`, so that the limit of the integral representation is
`1/G(0,0)`. -/
theorem integral_Ioi_id_mul_exp_neg : (∫ y in Set.Ioi (0 : ℝ), y * Real.exp (-y)) = 1 := by
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  rw [Real.Gamma_two] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

/-- **The domination of the density ratio of `eq:dgt4-gaussian-density-ratio`**
(`sandpile.tex:5265-5272`): `\rho_n(y)\leq Ce^{-y}` for every `y`, with the constant
the value of the ratio at `y=0`, which the Mills ratio keeps bounded.  The shift
identity `gaussianPDFReal_add` makes the exponential factor
`e^{-y-vy^2/(2t^2)}\leq e^{-y}` exactly. -/
theorem densityRatio_le (v : ℝ≥0) (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    (v : ℝ) / t * gaussianPDFReal 0 v (t + (v : ℝ) * y / t) / gaussianUpperTail v t
      ≤ (v : ℝ) / t * gaussianPDFReal 0 v t / gaussianUpperTail v t * Real.exp (-y) := by
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  have hUT : 0 < gaussianUpperTail v t := gaussianUpperTail_pos v hv t
  have hphi : 0 < gaussianPDFReal 0 v t := gaussianPDFReal_pos 0 v t hv
  have hc : (0 : ℝ) ≤ (v : ℝ) / t * gaussianPDFReal 0 v t / gaussianUpperTail v t := by positivity
  have hexp : Real.exp (-(2 * t * ((v : ℝ) * y / t) + ((v : ℝ) * y / t) ^ 2) / (2 * (v : ℝ)))
      ≤ Real.exp (-y) := by
    refine Real.exp_le_exp.2 ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (v : ℝ))]
    have h2 : 2 * t * ((v : ℝ) * y / t) = 2 * ((v : ℝ) * y) := by
      field_simp
    nlinarith [sq_nonneg ((v : ℝ) * y / t)]
  calc (v : ℝ) / t * gaussianPDFReal 0 v (t + (v : ℝ) * y / t) / gaussianUpperTail v t
      = (v : ℝ) / t * gaussianPDFReal 0 v t / gaussianUpperTail v t *
        Real.exp (-(2 * t * ((v : ℝ) * y / t) + ((v : ℝ) * y / t) ^ 2) / (2 * (v : ℝ))) := by
        rw [gaussianPDFReal_add v t ((v : ℝ) * y / t)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hc

end Sandpile
