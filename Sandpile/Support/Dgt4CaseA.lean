import Sandpile.Support.Dgt4Mills
import Sandpile.Support.Dgt4MeanDiv

/-!
# Case (a) of the contact-threshold asymptotics: the Gaussian branch

This file proves case (a) of `prop:dgt4-contact-asymptotics`, above its four steps, from the two
estimates `ThresholdRelativeError` and `GaussianMeanIncrement` at `J = -V_∞`. The first estimate
is `ThresholdRelativeError` at `J = -V_∞` character for character, and the second, together with
the Mills-ratio asymptotics of `Support/Dgt4Mills.lean`, gives the threshold asymptotic
`ℙ(-V_∞(0) > 𝔼 u_n(0)) ~ G(0,0)/n` through the chain of `Support/Dgt4TailChain.lean`, with
`κ = 1` in this case. `InfiniteFieldGaussianTail d ν v` records that `-V_∞(0)` is the mean-zero
Gaussian of variance `v`, in the only form the proof uses: the probability of exceeding a level
is the Gaussian tail at that level, which avoids any measurability hypothesis on the field.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- `-V_∞(0)` is the mean-zero Gaussian of variance `v` (`sandpile.tex:4986`),
read at the level of exceedance probabilities. -/
def InfiniteFieldGaussianTail (d : ℕ) (ν : Measure ℝ) (v : ℝ≥0) : Prop :=
  ∀ t : ℝ, ((Sandpile.centeredMassLaw d ν)
      {σ | t < -Sandpile.infiniteGreenField (Sandpile.scenery d σ) 0}).toReal
    = gaussianUpperTail v t

/-- `eq:dgt4-contact-mean-increment` (`sandpile.tex:4976-4979`):
`G(0,0)(\E u_{n+1}(0)-\E u_n(0))/\E(-V_\infty(0)-\E u_n(0))_+\to1`. -/
def GaussianMeanIncrement (d : ℕ) (ν : Measure ℝ) (v : ℝ≥0) : Prop :=
  Tendsto (fun n : ℕ => Sandpile.green d 0 0 *
      (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (n + 1) -
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n) /
      gaussianIntegratedTail v
        (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n)) atTop (𝓝 1)

/-- `eq:dgt4-threshold-probability` (`sandpile.tex:5008-5010`):
`\P(-V_\infty(0)>\E u_n(0))\sim G(0,0)/n`, with `\kappa=1`. -/
theorem thresholdTailAsymptotics_gaussian (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (hatom : ∀ z : ℝ, ν {z} = 0)
    (v : ℝ≥0) (hv : v ≠ 0)
    (hlaw : InfiniteFieldGaussianTail d ν v)
    (hincr : GaussianMeanIncrement d ν v) :
    ThresholdTailAsymptotics d ν
      (fun σ x => -Sandpile.infiniteGreenField (Sandpile.scenery d σ) x) 1 := by
  have hbnd : GaussianMillsBounds v := gaussianMillsBounds v hv
  have hGpos : (0 : ℝ) < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hvpos : (0 : ℝ) < (v : ℝ) := coe_pos_of_ne_zero hv
  set t : ℕ → ℝ := fun n => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n with htdef
  have htinf : Tendsto t atTop atTop :=
    tendsto_meanOdometer_atTop hd ν hint hmean (ne_dirac_of_atomless ν hatom)
  set b : ℕ → ℝ := fun n => gaussianUpperTail v (t n) with hbdef
  set I : ℕ → ℝ := fun n => gaussianIntegratedTail v (t n) with hIdef
  set p : ℕ → ℝ := fun n => gaussianPDFReal 0 v (t n) with hpdef
  set dl : ℕ → ℝ := fun n => t (n + 1) - t n with hdldef
  set D : ℕ → ℝ := fun n => b n - b (n + 1) with hDdef
  have hbpos : ∀ n, 0 < b n := fun n => gaussianUpperTail_pos v hv _
  have htpos : ∀ᶠ n in atTop, 0 < t n := htinf.eventually_gt_atTop 0
  have hIpos : ∀ᶠ n in atTop, 0 < I n := by
    filter_upwards [htpos] with n hn
    refine lt_of_lt_of_le ?_ (hbnd.le_mean _ hn)
    have hpn := gaussianPDFReal_pos 0 v (t n) hv
    positivity
  have hppos : ∀ᶠ n in atTop, 0 < p n :=
    Filter.Eventually.of_forall fun n => gaussianPDFReal_pos 0 v _ hv
  have h1 : Tendsto (fun n : ℕ => Sandpile.green d 0 0 * dl n / I n) atTop (𝓝 1) := hincr
  have hdlpos : ∀ᶠ n in atTop, 0 < dl n := eventually_increment_pos hGpos hIpos h1
  have h2 : Tendsto (fun n : ℕ => t n * I n / ((v : ℝ) * b n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (tendsto_gaussMills_mean v hv hbnd).comp htinf
  have h3 : Tendsto (fun n : ℕ => (v : ℝ) * p n / (t n * b n)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (tendsto_gaussMills_tail v hv hbnd).comp htinf
  have hbz : Tendsto b atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_gaussianUpperTail_zero v hv hbnd).comp htinf
  have htd : Tendsto (fun n : ℕ => t n * dl n) atTop (𝓝 0) :=
    tendsto_level_mul_increment hGpos hvpos hbpos hIpos hbz h1 h2
  have hd0 : Tendsto dl atTop (𝓝 0) := tendsto_increment_zero htinf hdlpos htd
  have h4 : Tendsto (fun n : ℕ => D n / (p n * dl n)) atTop (𝓝 1) := by
    have hexp := tendsto_gaussianUpperTail_expansion v hv hbnd (t := t) (dl := dl)
      (htinf.eventually_ge_atTop 0) hdlpos htd hd0
    refine hexp.congr fun n => ?_
    have hstep : t n + dl n = t (n + 1) := by rw [hdldef]; ring
    rw [hstep]
  have hchain : Tendsto (fun n : ℕ => (b (n + 1))⁻¹ - (b n)⁻¹) atTop
      (𝓝 (Sandpile.green d 0 0)⁻¹) :=
    tendsto_inv_sub_inv_of_factors hGpos hvpos hbpos hIpos hppos htpos hdlpos hbz
      (fun n => by rw [hDdef]; ring) h1 h2 h3 h4
  refine thresholdTailAsymptotics_of_inverse_increment (by simpa using hGpos)
    (fun n => by rw [hlaw (t n)]; exact hbpos n) ?_
  have hone : (Sandpile.green d 0 0 * (1 : ℝ))⁻¹ = (Sandpile.green d 0 0)⁻¹ := by
    rw [mul_one]
  rw [hone]
  refine hchain.congr fun n => ?_
  rw [hlaw (t n), hlaw (t (n + 1))]

/-- Case (a) of `prop:dgt4-contact-asymptotics` above its four steps: the two
estimates `eq:dgt4-contact-threshold-relative-error` and
`eq:dgt4-contact-mean-increment` of `sandpile.tex:4972-4979` give the
contact-threshold field of the Gaussian branch, with `\kappa=1`.  The variance `v`
of the scenery and the variance `w=\Sigma^2=\Var(V_\infty(0))` of the field of
`sandpile.tex:4967` enter separately: the first says which measure `\nu` is, the
second is the parameter of the Mills-ratio asymptotics. -/
theorem caseThresholdField_gaussian (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable id ν) (hmean : ∫ z, z ∂ν = 0) (hatom : ∀ z : ℝ, ν {z} = 0)
    (v : ℝ≥0) (hgauss : ν = gaussianReal 0 v) (w : ℝ≥0) (hw : w ≠ 0)
    (hlaw : InfiniteFieldGaussianTail d ν w)
    (hincr : GaussianMeanIncrement d ν w)
    (hrel : ThresholdRelativeError d ν
      (fun σ x => -Sandpile.infiniteGreenField (Sandpile.scenery d σ) x)) :
    CaseThresholdField d ν 1 :=
  caseThresholdField_of_gaussian (by omega) one_pos ⟨v, hgauss⟩
    (thresholdTailAsymptotics_gaussian hd ν hint hmean hatom w hw hlaw hincr) hrel

/-- In the Gaussian branch of the `hcase` disjunction the variance is nonzero: the
standing hypothesis `0 < evariance id ν` of `thm:dgt4-diffusive-membrane` rules out the
Dirac mass, which is what `gaussianReal 0 0` is. -/
theorem gaussian_var_ne_zero {ν : Measure ℝ}
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) {v : ℝ≥0} (hgauss : ν = gaussianReal 0 v) :
    v ≠ 0 := by
  intro h
  rw [hgauss, h, gaussianReal_zero_var] at hvar
  have hz : evariance (id : ℝ → ℝ) (Measure.dirac (0 : ℝ)) = 0 := by
    simp [evariance]
  rw [hz] at hvar
  exact lt_irrefl 0 hvar

end Sandpile
