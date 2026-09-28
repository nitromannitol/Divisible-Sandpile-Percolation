import Sandpile.Walk
import Sandpile.Law
import Sandpile.Support.Translation

/-!
# Reflection increment identity for the mean odometer

Lemma of sandpile.tex on the growth of the mean odometer, frozen.
`sandpile.tex:899-905` (label `lem:reflection-increment`):

  "Suppose $(\zeta(x))_{x\in\Z^d}$ are i.i.d.\ with mean zero. Then $\E u_t(0)$
   is nondecreasing and concave in $t$, and
   $\E u_{t+1}(0)-\E u_t(0)=\E(-\zeta(0)-Pu_t(0))_+$."

An i.i.d. mean-zero scenery is the mass law `Sandpile.centeredMassLaw d ν`,
which is the law of `σ = 1 + 2dζ` for `ζ` i.i.d. with one-site law `ν`, so that
`Sandpile.scenery d σ 0` is the paper's `ζ(0)` and `∫ z ∂ν = 0` is its mean-zero
hypothesis; `Integrable id ν` is what makes that mean an honest mean and not the
junk value of a divergent integral.  The paper's `E u_t(0)` is
`Sandpile.meanOdometer`, its `P` is `Sandpile.avg`, and `(·)₊` is `max 0 (·)`.
Concavity in the integer variable `t` is transcribed as the statement the
paper's proof establishes and uses, namely that the increments are
nonincreasing.  The two integrability hypotheses are what keeps the increment
identity an identity between integrals rather than between junk zeros; both
follow from the displayed hypotheses, and are assumed here so that no clause is
read vacuously.  The dimension carries `1 ≤ d` because at `d = 0` the scenery
and the averaging operator are junk zeros.
-/

open MeasureTheory ProbabilityTheory Filter Topology

-- FROZEN-STATEMENT-BEGIN
theorem Sandpile.Frozen.reflection_increment
    (d : ℕ) (hd : 1 ≤ d) (ν : Measure ℝ) (hprob : IsProbabilityMeasure ν)
    (hintν : Integrable id ν) (hmean : ∫ z, z ∂ν = 0)
    (hodo : ∀ t : ℕ, Integrable (fun σ => Sandpile.odometer σ t 0)
      (Sandpile.centeredMassLaw d ν))
    (hrefl : ∀ t : ℕ, Integrable
      (fun σ => max 0 (-(Sandpile.scenery d σ 0) - Sandpile.avg (Sandpile.odometer σ t) 0))
      (Sandpile.centeredMassLaw d ν)) :
    Monotone (fun t : ℕ => Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) ∧
      (∀ t : ℕ,
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (t + 2) -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (t + 1) ≤
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (t + 1) -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t) ∧
      (∀ t : ℕ,
        Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (t + 1) -
            Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t =
          ∫ σ, max 0 (-(Sandpile.scenery d σ 0) - Sandpile.avg (Sandpile.odometer σ t) 0)
            ∂(Sandpile.centeredMassLaw d ν))
-- FROZEN-STATEMENT-END
:= by
  haveI := hprob
  haveI : IsProbabilityMeasure (ν.map fun z => 1 + 2 * (d : ℝ) * z) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  set μ : Measure ℝ := ν.map (fun z => 1 + 2 * (d : ℝ) * z) with hμ
  have hPeq : Sandpile.centeredMassLaw d ν = Sandpile.massLaw d μ := rfl
  obtain ⟨hζint, hζmean⟩ := Sandpile.scenery_integrable_and_mean d hd ν hintν hmean
  have hodo' : ∀ t : ℕ, Integrable (fun σ => Sandpile.odometer σ t 0)
      (Sandpile.massLaw d μ) := by rw [← hPeq]; exact hodo
  have havgint : ∀ t : ℕ, Integrable (fun σ => Sandpile.avg (Sandpile.odometer σ t) 0)
      (Sandpile.centeredMassLaw d ν) := by
    intro t; rw [hPeq]; exact Sandpile.integrable_avg_odometer d μ t (hodo' t)
  have havg : ∀ t : ℕ, ∫ σ, Sandpile.avg (Sandpile.odometer σ t) 0
      ∂(Sandpile.centeredMassLaw d ν) = Sandpile.meanOdometer
        (Sandpile.centeredMassLaw d ν) t := by
    intro t
    show _ = ∫ σ, Sandpile.odometer σ t 0 ∂(Sandpile.centeredMassLaw d ν)
    rw [hPeq]; exact Sandpile.integral_avg_odometer d hd μ t (hodo' t)
  have hident : ∀ t : ℕ,
      Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (t + 1) -
          Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) t =
        ∫ σ, max 0 (-(Sandpile.scenery d σ 0) - Sandpile.avg (Sandpile.odometer σ t) 0)
          ∂(Sandpile.centeredMassLaw d ν) := by
    intro t
    have hpt : ∀ σ : Sandpile.Site d → ℝ, Sandpile.odometer σ (t + 1) 0
        = (Sandpile.scenery d σ 0 + Sandpile.avg (Sandpile.odometer σ t) 0)
          + max 0 (-(Sandpile.scenery d σ 0) - Sandpile.avg (Sandpile.odometer σ t) 0) := by
      intro σ
      show Sandpile.relax σ (Sandpile.odometer σ t) 0 = _
      rw [Sandpile.relax_eq_scenery, Sandpile.max_zero_eq]
      congr 2
      ring
    have hsplit : Sandpile.meanOdometer (Sandpile.centeredMassLaw d ν) (t + 1)
        = (∫ σ, (Sandpile.scenery d σ 0 + Sandpile.avg (Sandpile.odometer σ t) 0)
            ∂(Sandpile.centeredMassLaw d ν))
          + ∫ σ, max 0 (-(Sandpile.scenery d σ 0) - Sandpile.avg (Sandpile.odometer σ t) 0)
            ∂(Sandpile.centeredMassLaw d ν) := by
      show ∫ σ, Sandpile.odometer σ (t + 1) 0 ∂(Sandpile.centeredMassLaw d ν) = _
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact integral_add (hζint.add (havgint t)) (hrefl t)
    have hadd : ∫ σ, (Sandpile.scenery d σ 0 + Sandpile.avg (Sandpile.odometer σ t) 0)
        ∂(Sandpile.centeredMassLaw d ν)
        = (∫ σ, Sandpile.scenery d σ 0 ∂(Sandpile.centeredMassLaw d ν))
          + ∫ σ, Sandpile.avg (Sandpile.odometer σ t) 0
            ∂(Sandpile.centeredMassLaw d ν) := integral_add hζint (havgint t)
    rw [hsplit, hadd, hζmean, havg t]
    ring
  refine ⟨?_, ?_, hident⟩
  · refine monotone_nat_of_le_succ fun t => ?_
    show ∫ σ, Sandpile.odometer σ t 0 ∂(Sandpile.centeredMassLaw d ν)
      ≤ ∫ σ, Sandpile.odometer σ (t + 1) 0 ∂(Sandpile.centeredMassLaw d ν)
    exact integral_mono (hodo t) (hodo (t + 1))
      (fun σ => Sandpile.odometer_le_succ σ t 0)
  · intro t
    rw [hident (t + 1), hident t]
    refine integral_mono (hrefl (t + 1)) (hrefl t) fun σ => ?_
    have h := Sandpile.avg_odometer_mono σ t (0 : Sandpile.Site d)
    exact max_le_max le_rfl (by linarith)
