import Sandpile.External.Stopping.IndependentWeakLimits
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Independence under almost sure convergence

Independence passes to almost sure limits of random variables in separable
metric spaces. This allows a positive separation between past and future to
be removed in a path-space stopping argument.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Sandpile.External.Stopping

/-- Almost sure limits of independent random variables remain independent. -/
theorem indepFun_of_ae_tendsto
    {Ω E F : Type*} [MeasurableSpace Ω] [MetricSpace E] [MetricSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → E) (Y : ℕ → Ω → F) (x : Ω → E) (y : Ω → F)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hx : Measurable x) (hy : Measurable y)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => (X n ω, Y n ω)) atTop (𝓝 (x ω, y ω)))
    (hindep : ∀ n, IndepFun (X n) (Y n) P) : IndepFun x y P := by
  let Z : ℕ → Ω → E × F := fun n ω => (X n ω, Y n ω)
  let z : Ω → E × F := fun ω => (x ω, y ω)
  have hZ (n : ℕ) : Measurable (Z n) := (hX n).prodMk (hY n)
  have hz : Measurable z := hx.prodMk hy
  let μ : ℕ → ProbabilityMeasure (E × F) := fun n =>
    ⟨P.map (Z n), (Measure.isProbabilityMeasure_map_iff (hZ n).aemeasurable).2 inferInstance⟩
  let ν : ProbabilityMeasure (E × F) :=
    ⟨P.map z, (Measure.isProbabilityMeasure_map_iff hz.aemeasurable).2 inferInstance⟩
  have hconv : Tendsto μ atTop (𝓝 ν) :=
    (tendstoInDistribution_of_ae_tendsto (fun n => (hZ n).aemeasurable)
      hz.aemeasurable hlim).tendsto
  have hind (n : ℕ) : IndepFun (Prod.fst : E × F → E) Prod.snd (μ n : Measure (E × F)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map
      measurable_fst.aemeasurable measurable_snd.aemeasurable).2
    have hi := (indepFun_iff_map_prod_eq_prod_map_map (hX n).aemeasurable
      (hY n).aemeasurable).1 (hindep n)
    change (P.map (Z n)).map (fun p => (p.1, p.2)) =
      ((P.map (Z n)).map Prod.fst).prod ((P.map (Z n)).map Prod.snd)
    rw [Measure.map_map (measurable_fst.prodMk measurable_snd) (hZ n),
      Measure.map_map measurable_fst (hZ n), Measure.map_map measurable_snd (hZ n)]
    exact hi
  have hν := indepFun_fst_snd_of_weak_limit μ ν hconv hind
  have hν' := (indepFun_iff_map_prod_eq_prod_map_map
    measurable_fst.aemeasurable measurable_snd.aemeasurable).1 hν
  apply (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).2
  change (P.map z).map (fun p => (p.1, p.2)) =
    ((P.map z).map Prod.fst).prod ((P.map z).map Prod.snd) at hν'
  rw [Measure.map_map (measurable_fst.prodMk measurable_snd) hz,
    Measure.map_map measurable_fst hz, Measure.map_map measurable_snd hz] at hν'
  exact hν'

end Sandpile.External.Stopping
