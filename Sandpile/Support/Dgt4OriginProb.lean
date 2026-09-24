/-
The convergence in probability of `sandpile.tex:5383`, "By
\eqref{eq:dgt4-origin-fixed-mean} and Markov's inequality, $\E Pw_n(0)\sim\E u_n(0)/G(0,0)$
and $Pw_n(0)/\E Pw_n(0)\to1$ in probability", discharged from the sealed
`lem:dgt4-origin-frozen` at the exponent `p=2`.

Two of the three inputs are clauses of that lemma: the mean ratio
`G(0,0)\E Pw_n(0)/\E u_n(0)\to1` and the uniform second moment of
`Pw_n(0)-\E Pw_n(0)`.  The third is the INTEGRABILITY of that second moment, which the
frozen statement does not carry, its moment clause being a bare inequality between
integrals; it is proved here from the same coordinate-Lipschitz reading of `Pw_n(0)` that
the concentration estimate uses, namely that the neighbour average of the odometer killed
at the origin reads only the box `Q(0,n+1)` and moves by at most `G(0,z)/G(0,0)` when the
scenery at `z` moves by one.
-/
import Sandpile.Support.Dgt4CaseBRelError
import Sandpile.Support.OriginConcentration
import Sandpile.Frozen.DGT4OriginFrozen

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- A law of finite variance is square integrable. -/
theorem integrable_sq_of_evariance (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) : Integrable (fun z : ℝ => z ^ 2) ν := by
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  exact hLp.integrable_sq

/-- `Pw_n(0)` inherits the `p`-th moment of the scenery: it is a coordinate-Lipschitz
function of the finitely many scenery values it reads. -/
theorem integrable_avg_originOdometer_rpow (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 1 ≤ p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) (n : ℕ) :
    Integrable (fun ζ : Sandpile.Site d → ℝ => |Sandpile.avg (Sandpile.originOdometer ζ n) 0| ^ p)
      (LatticeProb.iidLaw d ν) := by
  have hd1 : 1 ≤ d := by omega
  have hpick := LatticeProb.measurePreserving_pick _ ν
    (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)))
    (Sandpile.siteEnum_injective (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)))
  have hFm : Measurable (Sandpile.boxOriginAverage (d := d) n) :=
    Sandpile.measurable_boxOriginAverage hd1 n
  have hFint : Integrable
      (fun ξ : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).card → ℝ =>
        |Sandpile.boxOriginAverage n ξ| ^ p)
      (Measure.pi fun _ : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).card => ν) :=
    LatticeProb.integrable_rpow_of_lip_fam _ hp (fun _ => hmom)
      (Sandpile.boxOriginAverage n) hFm
      (fun i => Sandpile.originInfluence
        (Sandpile.siteEnum (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)) i))
      (fun _ => Sandpile.originInfluence_nonneg _)
      (Sandpile.abs_boxOriginAverage_update_le hd1 n)
  have h := LatticeProb.integrable_comp_mp hpick
    (fun ξ : Fin (Sandpile.boxFinset (0 : Sandpile.Site d) (n + 1)).card → ℝ =>
      |Sandpile.boxOriginAverage n ξ| ^ p)
    (LatticeProb.measurable_abs_rpow hFm p).aestronglyMeasurable hFint
  exact h.congr (Filter.Eventually.of_forall fun ζ => by
    simp only [Sandpile.boxOriginAverage_pick hd1 n])

/-- The centred `p`-th moment of `Pw_n(0)` is integrable, which is what the frozen moment
clause of `lem:dgt4-origin-frozen` does not itself assert. -/
theorem integrable_avg_originOdometer_centred_rpow (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 1 ≤ p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) (n : ℕ) (c : ℝ) :
    Integrable (fun ζ : Sandpile.Site d → ℝ =>
        |Sandpile.avg (Sandpile.originOdometer ζ n) 0 - c| ^ p) (LatticeProb.iidLaw d ν) := by
  have hd1 : 1 ≤ d := by omega
  refine LatticeProb.integrable_rpow_sub _ hp _ (fun _ => c)
    (LatticeProb.measurable_abs_rpow
      ((Sandpile.measurable_avg_originOdometer hd1 n).sub measurable_const) p).aestronglyMeasurable
    (integrable_avg_originOdometer_rpow hd ν hp hmom n) ?_
  exact integrable_const (|c| ^ p)

/-- `eq:dgt4-origin-fixed-mean` in the language of the i.i.d. field:
`G(0,0)\E Pw_n(0)/\E u_n(0)\to1`, i.e. `\E Pw_n(0)\sim\E u_n(0)/G(0,0)`. -/
theorem tendsto_meanAvg_originOdometer_ratio
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) :
    Tendsto (fun n : ℕ =>
        (∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)) /
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0))
      atTop (𝓝 1) := by
  have hd1 : 1 ≤ d := by omega
  have hmom2 : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν :=
    Sandpile.integrable_abs_rpow_two ν (integrable_sq_of_evariance ν hvar')
  obtain ⟨hratio, -⟩ :=
    (Sandpile.Frozen.dgt4_origin_frozen hGreenHigh d hd ν hatom hmean hvar hvar').2.1
      2 le_rfl hmom2
  simp only [Sandpile.killedOdometer_eq_originOdometer] at hratio
  refine hratio.congr fun n => ?_
  rw [Sandpile.integral_scenery d ν hd1
      (F := fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
      (Sandpile.measurable_avg_originOdometer hd1 n).aestronglyMeasurable,
    div_div_eq_mul_div, mul_comm]

/-- `Pw_n(0)/(\E u_n(0)/G(0,0))\to1` in probability, `sandpile.tex:5378-5379`.  The mean
ratio and the uniform second moment are the two clauses of `lem:dgt4-origin-frozen` at the
exponent `p=2`, which the standing finite variance supplies; the integrability that the
frozen moment clause omits is `integrable_avg_originOdometer_centred_rpow`. -/
theorem tendsto_prob_avg_originOdometer_ratio
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | ε < |Sandpile.avg (Sandpile.originOdometer ζ n) 0 /
          (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0) - 1|}).toReal) atTop (𝓝 0) := by
  have hd1 : 1 ≤ d := by omega
  have hG : 0 < Sandpile.green d 0 0 :=
    lt_of_lt_of_le zero_lt_one (Sandpile.one_le_green (by omega))
  have hLp : MemLp (id : ℝ → ℝ) 2 ν :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).mp hvar'
  have hintν : Integrable (id : ℝ → ℝ) ν := hLp.integrable (by norm_num)
  have hmom2 : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν :=
    Sandpile.integrable_abs_rpow_two ν (integrable_sq_of_evariance ν hvar')
  obtain ⟨-, M, hM⟩ :=
    (Sandpile.Frozen.dgt4_origin_frozen hGreenHigh d hd ν hatom hmean hvar hvar').2.1
      2 le_rfl hmom2
  simp only [Sandpile.killedOdometer_eq_originOdometer] at hM
  have hmean_eq : ∀ n : ℕ,
      (∫ σ, Sandpile.avg (Sandpile.originOdometer (Sandpile.scenery d σ) n) 0
        ∂(Sandpile.centeredMassLaw d ν))
        = ∫ ζ, Sandpile.avg (Sandpile.originOdometer ζ n) 0 ∂(LatticeProb.iidLaw d ν) :=
    fun n => Sandpile.integral_scenery d ν hd1
      (F := fun ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
      (Sandpile.measurable_avg_originOdometer hd1 n).aestronglyMeasurable
  have hMi : ∀ n : ℕ,
      (∫ ζ, |Sandpile.avg (Sandpile.originOdometer ζ n) 0 -
          ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)| ^ (2 : ℝ)
        ∂(LatticeProb.iidLaw d ν)) ≤ M := by
    intro n
    have h2 := hM n
    rw [hmean_eq n] at h2
    rwa [Sandpile.integral_scenery d ν hd1
      (F := fun ζ => |Sandpile.avg (Sandpile.originOdometer ζ n) 0 -
        ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν)| ^ (2 : ℝ))
      (LatticeProb.measurable_abs_rpow
        ((Sandpile.measurable_avg_originOdometer hd1 n).sub measurable_const)
        (2 : ℝ)).aestronglyMeasurable] at h2
  have hinf : Tendsto (fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
      atTop atTop :=
    (tendsto_meanOdometer_atTop hd ν hintν hmean
      (ne_dirac_of_atomless ν hatom)).atTop_div_const hG
  have hratio' := tendsto_meanAvg_originOdometer_ratio hGreenHigh d hd ν hatom hmean hvar hvar'
  exact Sandpile.tendsto_prob_ratio_zero_of_moment (p := 2) (M := M)
    (X := fun n ζ => Sandpile.avg (Sandpile.originOdometer ζ n) 0)
    (m := fun n => ∫ η, Sandpile.avg (Sandpile.originOdometer η n) 0 ∂(LatticeProb.iidLaw d ν))
    (a := fun n : ℕ =>
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n / Sandpile.green d 0 0)
    (by norm_num)
    (fun n => integrable_avg_originOdometer_centred_rpow hd ν (by norm_num) hmom2 n _)
    hMi hinf hratio'

/-- Case (b) of `prop:dgt4-contact-asymptotics` from Step 1 and nothing else.  With the
convergence in probability discharged from `lem:dgt4-origin-frozen`, the heavy-tailed
branch of `hcase` rests on the single estimate `eq:dgt4-small-origin-neighbor-average`
(`sandpile.tex:5344-5346`), that `Pw_n(0)` falls below a fixed fraction of its level with
probability `o(\P(-\zeta(0)>\E u_n(0)/G(0,0)))`. -/
theorem caseThresholdField_linear_of_step1_only
    (hGreenHigh : Sandpile.External.GreenBoundsHigh)
    (d : ℕ) (hd : 5 ≤ d) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hatom : ∀ z : ℝ, ν {z} = 0) (hmean : ∫ z, z ∂ν = 0)
    (hvar : 0 < evariance (id : ℝ → ℝ) ν) (hvar' : evariance (id : ℝ → ℝ) ν < ⊤)
    {α : ℝ} (hα : 1 < α)
    (hrv : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun r : ℝ => (ν (Iio (-(lam * r)))).toReal / (ν (Iio (-r))).toReal)
        atTop (𝓝 (lam ^ (-α))))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hstep1 : Tendsto (fun n : ℕ => ((LatticeProb.iidLaw d ν)
        {ζ | Sandpile.avg (Sandpile.originOdometer ζ n) 0 <
          θ * (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
            Sandpile.green d 0 0)}).toReal /
        LatticeProb.lowerTail ν (Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) n /
          Sandpile.green d 0 0)) atTop (𝓝 0)) :
    CaseThresholdField d ν (1 - 1 / α) :=
  caseThresholdField_linear_of_step1 hGreenHigh d hd ν hatom hmean hvar hvar' hα hrv hθ hθ1
    (tendsto_prob_avg_originOdometer_ratio hGreenHigh d hd ν hatom hmean hvar hvar') hstep1

end Sandpile
